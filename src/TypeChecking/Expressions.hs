module TypeChecking.Expressions
    ( typeCheck, typeCheckCtx
    , inferErrorMsg, notInScope
    , prettyOpen, checkIsType
    , termPos
    ) where

import Control.Monad
import Data.Void
import Data.Bifunctor

import Syntax as S
import Semantics
import Semantics.Value as V
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import Normalization

notInScope :: Show a => Posn -> String -> a -> EMsg f
notInScope pos s a = emsgLC pos ("Not in scope: " ++ (if null s then "" else s ++ " ") ++ show a) enull

inferErrorMsg :: Posn -> String -> EMsg f
inferErrorMsg pos s = emsgLC pos ("Cannot infer type of " ++ s) enull

inferParamsErrorMsg :: Show a => Posn -> a -> EMsg f
inferParamsErrorMsg pos d = emsgLC pos ("Cannot infer parameters of data constructor " ++ show d) enull

argsErrorMsg :: Posn -> String -> EMsg f
argsErrorMsg pos s = emsgLC pos (s ++ " is applied to arguments") enull

expectedArgErrorMsg :: Show a => Posn -> a -> EMsg f
expectedArgErrorMsg lc d = emsgLC lc ("Expected an argument to " ++ show d) enull

type Context = Ctx String (Type Semantics) Void

prettyOpen :: Context a -> Term Semantics a -> EDoc (Term Syntax)
prettyOpen ctx term = epretty $ fmap (pretty . either id absurd) $ close ctx (bimap syntax Right term)

checkIsType :: Monad m => Context a -> Posn -> Term Semantics a -> EDocM m Level
checkIsType _ _ (Apply (Semantics _ (Universe lvl)) _) = return lvl
checkIsType ctx pos t = throwError [emsgLC pos "" $ pretty "Expected type: Type"
                                                 $$ pretty "Actual type:" <+> prettyOpen ctx t]

intType :: Type Semantics a
intType = Type interval NoLevel

interval :: Term Semantics a
interval = capply $ Semantics (Name Prefix $ Ident "I") Interval

pathExp :: Level -> Semantics
pathExp lvl = Semantics (Name Prefix $ Ident "Path") (Path lvl)

pathImp :: Level -> Semantics
pathImp lvl = Semantics PathImp (Path lvl)

termPos :: Term (Posn, s) a -> Posn
termPos (Apply (pos, _) _) = pos
termPos _ = error "termPos"

typeCheck :: Monad m => Term (Posn, Syntax) Void -> Maybe (Type Semantics Void) -> TCM m (Term Semantics Void, Type Semantics Void)
typeCheck = typeCheckCtx Nil

typeCheckCtx :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void
    -> Maybe (Type Semantics a) -> TCM m (Term Semantics a, Type Semantics a)
typeCheckCtx ctx (Apply (pos, Name ft var) ts) mty = typeCheckName ctx pos ft var ts mty
typeCheckCtx ctx (Apply (_, S.Lam []) [te]) mty = typeCheckCtx ctx te mty
typeCheckCtx ctx (Apply (pos, S.Lam (v:vs)) [te]) (Just ty@(Type (Apply p@(Semantics _ (V.Pi lvl1 lvl2)) [a,b]) _)) = do
    (te', _) <- typeCheckCtx (Snoc ctx v $ Type a lvl1) (Apply (pos, S.Lam vs) [te]) $ Just $ Type (nf WHNF $ snd $ dropOnePi p a b) lvl2
    let te'' = case te' of
            Apply (Semantics (S.Lam vs') _) [t] -> Apply (Semantics (S.Lam $ v:vs') V.Lam) [Lambda t]
            _                                   -> Apply (Semantics (S.Lam [v]) V.Lam) [Lambda te']
    return (te'', ty)
typeCheckCtx ctx (Apply (pos, S.Lam{}) [_]) (Just (Type ty _)) =
    throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                             $$ pretty "But lambda expression has pi type"]
typeCheckCtx ctx (Apply (pos, S.Lam{}) _) _ = throwError [inferErrorMsg pos "the argument"]
typeCheckCtx ctx (Apply (pos, S.Pi vs) (a:b:ts)) Nothing = do
    (a', Type ty1 _) <- typeCheckCtx ctx a Nothing
    lvl1 <- checkIsType ctx (termPos a) ty1
    (b', lvl2) <- extend ctx vs (Type a' lvl1)
    unless (null ts) $ warn [argsErrorMsg pos "A type"]
    let lvl = max lvl1 lvl2
    return (Apply (Semantics (S.Pi vs) (V.Pi lvl1 lvl2)) [a', b'], Type (universe lvl) $ succ lvl)
  where
    extend :: (Monad m, Eq a) => Context a -> [String] -> Type Semantics a -> TCM m (Term Semantics a, Level)
    extend ctx [] _ = do
        (te, Type ty _) <- typeCheckCtx ctx b Nothing
        lvl <- checkIsType ctx (termPos b) ty
        return (te, lvl)
    extend ctx (v:vs) a = do
        (te, lvl) <- extend (Snoc ctx v a) vs (fmap Free a)
        return (Lambda te, lvl)
typeCheckCtx ctx (Apply (pos, PathImp) (a1:a2:ts)) Nothing = do
    unless (null ts) $ warn [argsErrorMsg pos "A type"]
    (r1, Type t1 lvl) <- typeCheckCtx ctx a1 Nothing
    (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF t1) lvl
    return (Apply (Semantics PathImp (Path lvl)) [Apply (Semantics (S.Lam ["_"]) V.Lam)
            [Lambda $ fmap Free t1], r1, r2], Type (universe lvl) $ succ lvl)
typeCheckCtx ctx (Apply (pos, S.At) (b:c:ts)) Nothing = do
    (r1, Type t1 lvl) <- typeCheckCtx ctx b Nothing
    (r2, _) <- typeCheckCtx ctx c (Just intType)
    case nf WHNF t1 of
        Apply (Semantics _ Path{}) [a,b',c'] -> do
            (tes, ty) <- typeCheckApps pos ctx ts $ Type (apps a [r2]) lvl
            return (Apply (Semantics S.At V.At) (b':c':r1:r2:tes), ty)
        t1' -> throwError [emsgLC pos "" $ pretty "Expected type: Path"
                                        $$ pretty "Actual type:" <+> prettyOpen ctx t1']
typeCheckCtx ctx te (Just (Type ty _)) = do
    (te', Type ty' lvl') <- typeCheckCtx ctx te Nothing
    actExpType ctx ty' ty (termPos te)
    return (te', Type ty' lvl')
typeCheckCtx _ _ _ = error "typeCheckCtx"

typeCheckName :: (Monad m, Eq a) => Context a -> Posn -> Fixity -> Name -> [Term (Posn, Syntax) Void]
    -> Maybe (Type Semantics a) -> TCM m (Term Semantics a, Type Semantics a)
typeCheckName ctx pos ft var ts mty = do
    when (getStr var == "_") $ throwError [emsgLC pos "Expected an identifier" enull]
    let mdt = case mty of
                Just (Type (Apply (Semantics _ (DataType dti _)) params) _) -> Just (dti,params)
                _ -> Nothing
    mt <- lift $ getEntry var mdt
    eres <- case mt of
        [] -> liftM Right (typeCheckKeyword ctx pos (getStr var) ts mty)
        [(s,ty)] ->
            let s' = case syntax s of
                        Name ft' _ | ft == ft'  -> s
                        _                       -> s { syntax = Name ft var }
            in return $ Left (capply s', ty)
        _ -> throwError [emsgLC pos ("Ambiguous identifier: " ++ show (getStr var)) enull]
    case eres of
        Left (te, ty) -> do
            (tes, Type ty' lvl') <- typeCheckApps pos ctx ts ty
            case (mty, ty') of
                (Nothing, _)            -> return ()
                (Just (Type ety _), _)  -> actExpType ctx ty' ety pos
            return (apps te tes, Type ty' lvl')
        Right res -> return res

typeCheckKeyword :: (Monad m, Eq a) => Context a -> Posn -> String -> [Term (Posn, Syntax) Void]
    -> Maybe (Type Semantics a) -> TCM m (Term Semantics a, Type Semantics a)
typeCheckKeyword ctx pos u as Nothing | (lvl,""):_ <- reads u = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (universe lvl, Type (universe $ succ lvl) $ succ $ succ lvl)
typeCheckKeyword ctx pos "I" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (interval, Type (universe NoLevel) $ Level 1)
typeCheckKeyword ctx pos "left" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "left"]
    return (iCon ILeft, intType)
typeCheckKeyword ctx pos "right" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "right"]
    return (iCon IRight, intType)
typeCheckKeyword ctx pos "Path" [] _ = throwError [expectedArgErrorMsg pos "Path"]
typeCheckKeyword ctx pos "Path" (a:as) Nothing = do
    (r1, _, (v, t1)) <- typeCheckLambda ctx a intType
    lvl <- checkIsType (Snoc ctx v $ error "") (termPos a) t1
    let r1' c = apps r1 [iCon c]
        mkType t = Type t (succ lvl)
    case as of
        [] -> return (Apply (pathExp lvl) [r1], mkType $
            Apply (Semantics (S.Pi []) $ V.Pi lvl $ succ lvl) [r1' ILeft, Apply (Semantics (S.Pi []) $ V.Pi lvl $ succ lvl) [r1' IRight, universe lvl]])
        [a2] -> do
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF $ r1' ILeft) lvl
            return (Apply (pathExp lvl) [r1,r2], mkType $ Apply (Semantics (S.Pi []) $ V.Pi lvl $ succ lvl) [r1' IRight, universe lvl])
        a2:a3:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF $ r1' ILeft) lvl
            (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ r1' IRight) lvl
            return (Apply (pathExp lvl) [r1,r2,r3], mkType $ universe lvl)
typeCheckKeyword ctx pos "path" [] _ = throwError [expectedArgErrorMsg pos "path"]
typeCheckKeyword ctx pos "path" (a:as) mty = do
    unless (null as) $ warn [argsErrorMsg pos "A path"]
    case mty of
        Nothing -> do
            (te, Type ty lvl, _) <- typeCheckLambda ctx a intType
            let te' c = apps te [iCon c]
            return (te, Type (Apply (pathImp lvl) [ty, te' ILeft, te' IRight]) lvl)
        Just (Type ty@(Apply (Semantics _ (Path l1)) [t1,_,_]) lvl) -> do
            (r,t) <- typeCheckCtx ctx a $ Just $
                Type (Apply (Semantics (S.Pi ["i"]) $ V.Pi NoLevel l1) [interval, Lambda $ apps (fmap Free t1) [cvar Bound]]) l1
            actExpType ctx (Apply (pathImp l1) [t1, apps r [iCon ILeft], apps r [iCon IRight]]) ty pos
            return (Apply (Semantics (Name Prefix $ Ident "path") $ Con PCon) [r], Type ty lvl)
        Just (Type ty _) -> throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                                     $$ pretty "Actual type: Path"]
typeCheckKeyword ctx pos "coe" [] _ = throwError [expectedArgErrorMsg pos "coe"]
typeCheckKeyword ctx pos "coe" (a1:as) Nothing = do
    (r1, _, (v, t1)) <- typeCheckLambda ctx a1 intType
    lvl <- checkIsType (Snoc ctx v $ error "") (termPos a1) t1
    let res = Apply (Semantics (S.Pi ["r"]) $ V.Pi NoLevel lvl) [interval, Lambda $ apps (fmap Free r1) [cvar Bound]]
        coe = Semantics (Name Prefix $ Ident "coe") Coe
    case as of
        [] -> return (Apply coe [r1], Type (Apply (Semantics (S.Pi ["l"]) $ V.Pi NoLevel lvl) [interval, Lambda $
            Apply (Semantics (S.Pi []) $ V.Pi lvl lvl) [apps (fmap Free r1) [cvar Bound], fmap Free res]]) lvl)
        a2:as1 -> do
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            case as1 of
                [] -> return (Apply coe [r1,r2], Type (Apply (Semantics (S.Pi []) $ V.Pi lvl lvl) [apps r1 [r2], res]) lvl)
                a3:as2 -> do
                    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ apps r1 [r2]) lvl
                    case as2 of
                        [] -> return (Apply coe [r1,r2,r3], Type res lvl)
                        a4:as3 -> do
                            (r4, _) <- typeCheckCtx ctx a4 (Just intType)
                            (tes, ty) <- typeCheckApps pos ctx as3 $ Type (apps r1 [r4]) lvl
                            return (Apply coe $ [r1,r2,r3,r4] ++ tes, ty)
typeCheckKeyword ctx pos "iso" (a1:a2:a3:a4:a5:a6:as) Nothing = do
    (r1, Type t1 _) <- typeCheckCtx ctx a1 Nothing
    (r2, Type t2 _) <- typeCheckCtx ctx a2 Nothing
    let t1' = nf WHNF t1
        t2' = nf WHNF t2
    lvl1 <- checkIsType ctx (termPos a1) t1'
    lvl2 <- checkIsType ctx (termPos a2) t2'
    let lvl = max lvl1 lvl2
    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (Apply (Semantics (S.Pi []) $ V.Pi lvl1 lvl2) [r1,r2]) lvl
    (r4, _) <- typeCheckCtx ctx a4 $ Just $ Type (Apply (Semantics (S.Pi []) $ V.Pi lvl2 lvl1) [r2,r1]) lvl
    let h e s1 s3 s4 tlvl = typeCheckCtx ctx e $ Just $ Type (Apply (Semantics (S.Pi ["x"]) $ V.Pi tlvl tlvl) [s1, Lambda $
            Apply (pathImp tlvl) [Apply (Semantics (S.Lam ["_"]) V.Lam) [Lambda $ fmap (Free . Free) s1],
                apps (fmap Free s4) [apps (fmap Free s3) [cvar Bound]], cvar Bound]]) tlvl
        iso = Semantics (Name Prefix $ Ident "iso") Iso
    (r5, _) <- h a5 r1 r3 r4 lvl1
    (r6, _) <- h a6 r2 r4 r3 lvl2
    case as of
        [] -> return (Apply iso [r1,r2,r3,r4,r5,r6],
            Type (Apply (Semantics (S.Pi []) $ V.Pi NoLevel $ succ lvl) [interval, universe lvl]) $ succ lvl)
        a7:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r7, _) <- typeCheckCtx ctx a7 (Just intType)
            return (Apply iso [r1,r2,r3,r4,r5,r6,r7], Type (universe lvl) $ succ lvl)
typeCheckKeyword ctx pos "iso" _ Nothing = throwError [emsgLC pos "Expected at least 6 arguments to \"iso\"" enull]
typeCheckKeyword ctx pos "squeeze" as Nothing =
    let mkType t = Apply (Semantics (S.Pi []) $ V.Pi NoLevel NoLevel) [interval, t]
        squeeze = Semantics (Name Prefix $ Ident "squeeze") Squeeze
    in case as of
        [] -> return (capply squeeze, Type (mkType $ mkType interval) NoLevel)
        [a1] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            return (Apply squeeze [r1], Type (mkType interval) NoLevel)
        [a1,a2] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            return (Apply squeeze [r1,r2], intType)
        _ -> throwError [argsErrorMsg pos "squeeze _ _"]
typeCheckKeyword ctx pos var ts (Just (Type ty _)) = do
    (te', Type ty' lvl') <- typeCheckKeyword ctx pos var ts Nothing
    actExpType ctx ty' ty pos
    return (te', Type ty' lvl')
typeCheckKeyword ctx pos var ts mty = case lookupCtx var ctx of
    Just (te, ty)  -> do
        (tes, Type ty' lvl') <- typeCheckApps pos ctx ts ty
        case (mty, ty') of
            (Nothing, _)            -> return ()
            (Just (Type ety _), _)  -> actExpType ctx ty' ety pos
        return (apps te tes, Type ty' lvl')
    Nothing -> throwError [notInScope pos "" var]

actExpType :: (Monad m, Eq a) => Context a -> Term Semantics a -> Term Semantics a -> Posn -> EDocM m ()
actExpType ctx act exp pos =
    let act' = nf NF act
        exp' = nf NF exp
    in unless (act' `lessOrEqual` exp') $
        throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx exp'
                                 $$ pretty "Actual type:"   <+> prettyOpen ctx act']

typeCheckApps :: (Monad m, Eq a) => Posn -> Context a -> [Term (Posn, Syntax) Void] -> Type Semantics a -> TCM m ([Term Semantics a], Type Semantics a)
typeCheckApps pos ctx terms ty = go terms (nfType WHNF ty)
  where
    go [] ty = return ([], ty)
    go (term:terms) (Type (Apply p@(Semantics _ (V.Pi lvl1 lvl2)) [a,b]) _) = do
        (term, _)   <- typeCheckCtx ctx term $ Just (Type (nf WHNF a) lvl1)
        (terms, ty) <- go terms $ Type (nf WHNF $ case b of
            Lambda{} -> instantiate1 term $ snd (dropOnePi p a b)
            _        -> b) lvl2
        return (term:terms, ty)
    go _ (Type ty _) = throwError [emsgLC pos "" $ pretty "Expected pi type"
                                                $$ pretty "Actual type:" <+> prettyOpen ctx ty]

typeCheckLambda :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void -> Type Semantics a
    -> TCM m (Term Semantics a, Type Semantics a, (String, Term Semantics (Scoped a)))
typeCheckLambda ctx (Apply (pos, S.Lam (v:vs)) [te]) (Type ty lvl) = do
    (te', Type ty' lvl') <- typeCheckCtx (Snoc ctx v $ Type ty lvl) (if null vs then te else Apply (pos, S.Lam vs) [te]) Nothing
    let te'' = case te' of
                Apply (Semantics (S.Lam vs') _) [te''] -> Apply (Semantics (S.Lam $ v:vs') V.Lam) [Lambda te'']
                _ -> Apply (Semantics (S.Lam [v]) V.Lam) [Lambda te']
    return (te'', Type (Apply (Semantics (S.Pi [v]) (V.Pi lvl lvl')) [ty, Lambda ty']) $ max lvl lvl', (v, ty'))
typeCheckLambda ctx te ty = do
    (te', Type ty' lvl') <- typeCheckCtx ctx te Nothing
    case nf WHNF ty' of
        ty''@(Apply p@(Semantics sp (V.Pi lvla lvlb)) [a,b]) ->
            let na = nf NF a
                Type nty lvlty = nfType NF ty
            in if (nty `lessOrEqual` na)
                then return (te', Type ty'' lvl', dropOnePi p a b)
                else throwError [emsgLC (termPos te) "" $
                        pretty "Expected type:" <+> prettyOpen ctx (Apply (Semantics sp $ V.Pi lvlty lvlb) [nty,b]) $$
                        pretty "Actual type:"   <+> prettyOpen ctx (Apply p [na,b])]
        _ -> throwError [emsgLC (termPos te) "" $ pretty "Expected pi type"
                                               $$ pretty "Actual type:" <+> prettyOpen ctx ty']
