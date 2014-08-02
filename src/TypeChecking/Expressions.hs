module TypeChecking.Expressions
    ( typeCheck, typeCheckCtx
    , inferErrorMsg, notInScope
    , prettyOpen, checkIsType
    , termPos
    ) where

import Control.Monad
import Data.List
import Data.Maybe
import Data.Void

import Syntax
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

type Context = Ctx String (Type Syntax) Void

prettyOpen :: Context a -> Term p a -> EDoc (Term p)
prettyOpen ctx term = epretty $ fmap (pretty . either id absurd) $ close ctx (fmap Right term)

checkIsType :: Monad m => Context a -> Posn -> Term Syntax a -> EDocM m Level
checkIsType _ _ (Apply (Universe lvl) _) = return lvl
checkIsType ctx pos t = throwError [emsgLC pos "" $ pretty "Expected type: Type"
                                                 $$ pretty "Actual type:" <+> prettyOpen ctx t]

intType :: Type Syntax a
intType = Type (cterm Interval) NoLevel

termPos :: Term (Posn, s) a -> Posn
termPos (Apply (pos, _) _) = pos
termPos _ = error "termPos"

typeCheck :: Monad m => Term (Posn, Syntax) Void -> Maybe (Type Syntax Void) -> TCM m (Term Syntax Void, Type Syntax Void)
typeCheck = typeCheckCtx Nil

typeCheckCtx :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void -> Maybe (Type Syntax a) -> TCM m (Term Syntax a, Type Syntax a)
typeCheckCtx ctx term mty = go ctx term [] $ fmap (nfType WHNF) mty
  where
    go :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void -> [Term (Posn, Syntax) Void] -> Maybe (Type Syntax a) -> TCM m (Term Syntax a, Type Syntax a)
    go ctx (Apply (pos, Ident var) _) ts mty = do
        when (var == "_") $ throwError [emsgLC pos "Expected an identifier" enull]
        let mdt = case mty >>= fst . collect . getType of
                    Just (DataType dt _) -> Just dt
                    _                    -> Nothing
        mt <- lift (getEntry var mdt)
        eres <- case mt of
            [FunctionE (Apply (FunCall name clauses) _) ty] -> return $ Left (cterm $ FunCall  name clauses, fmap (liftBase ctx) ty)
            [FunctionE (Apply (FunSyn name expr) _) ty]     -> return $ Left (cterm $ FunSyn   name expr   , fmap (liftBase ctx) ty)
            DataTypeE ty e : _                              -> return $ Left (cterm $ DataType var e       , fmap (liftBase ctx) ty)
            [ConstructorE _ (ScopeTerm con) (ScopeTerm ty, lvl)] ->
                return $ Left (fmap (liftBase ctx) con, Type (fmap (liftBase ctx) ty) lvl)
            [ConstructorE _ con (ty, lvl)] -> case (fmap (collect . getType) mty, mty) of
                (Just (Just DataType{}, params), _) ->
                    let liftTerm = instantiate params . fmap (liftBase ctx)
                    in  return $ Left (liftTerm con, Type (liftTerm ty) lvl)
                (_, Just (Type ty' _)) -> throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty'
                                                                   $$ pretty ("But given data constructor " ++ show var)]
                _ -> throwError [inferParamsErrorMsg pos var]
            [] -> do
                cons <- lift (getConstructorDataTypes var)
                case cons of
                    []    -> liftM Right (typeCheckKeyword ctx pos var ts mty)
                    [act] -> throwError [emsgLC pos "" $
                        pretty ("Expected data type: " ++ fromJust mdt) $$
                        pretty ("Actual data type: " ++ act)]
                    acts -> throwError [emsgLC pos "" $
                        pretty ("Expected data type: " ++ fromJust mdt) $$
                        pretty ("Posible data types: " ++ intercalate ", " acts)]
            _  -> throwError [inferErrorMsg pos $ show var]
        case eres of
            Left (te, ty) -> do
                (tes, Type ty' lvl') <- typeCheckApps pos ctx ts ty
                case (mty, ty') of
                    (Nothing, _)            -> return ()
                    (Just (Type ety _), _)  -> actExpType ctx ty' ety pos
                return (apps te tes, Type ty' lvl')
            Right res -> return res
    go ctx (Apply (_, App) [t1,t2]) ts mty = go ctx t1 (t2:ts) mty
    go ctx (Apply (_, Lam []) [te]) [] mty = go ctx te [] mty
    go ctx (Apply (pos, Lam (v:vs)) te) [] (Just ty@(Type (Apply p@(Pi _ lvl1 lvl2) [a,b]) _)) = do
        (te', _) <- go (Snoc ctx v $ Type a lvl1) (Apply (pos, Lam vs) te) [] $ Just $ Type (nf WHNF $ snd $ dropOnePi p a b) lvl2
        let te'' = case te' of
                Apply (Lam vs') [t] -> Apply (Lam $ v:vs') [Lambda $ Scope1 t]
                _                   -> Apply (Lam [v]) [Lambda $ Scope1 te']
        return (te'', ty)
    go ctx (Apply (pos, Lam{}) _) [] (Just (Type ty _)) =
        throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                 $$ pretty "But lambda expression has pi type"]
    go ctx (Apply (pos, Lam{}) _) _ _ = throwError [inferErrorMsg pos "the argument"]
    go ctx (Apply (pos, Pi vs _ _) [a,b]) ts Nothing = do
        (a', Type ty1 _) <- go ctx a [] Nothing
        lvl1 <- checkIsType ctx (termPos a) ty1
        (b', lvl2) <- extend ctx vs (Type a' lvl1)
        unless (null ts) $ warn [argsErrorMsg pos "A type"]
        let lvl = max lvl1 lvl2
        return (Apply (Pi vs lvl1 lvl2) [a', b'], Type (cterm $ Universe lvl) $ succ lvl)
      where
        extend :: (Monad m, Eq a) => Context a -> [String] -> Type Syntax a -> TCM m (Term Syntax a, Level)
        extend ctx [] _ = do
            (te, Type ty _) <- go ctx b [] Nothing
            lvl <- checkIsType ctx (termPos b) ty
            return (te, lvl)
        extend ctx (v:vs) a = do
            (te, lvl) <- extend (Snoc ctx v a) vs (fmap Free a)
            return (Lambda $ Scope1 te, lvl)
    go ctx (Apply (pos, Path{}) [a1,a2]) ts Nothing = do
        unless (null ts) $ warn [argsErrorMsg pos "A type"]
        (r1, Type t1 lvl) <- go ctx a1 [] Nothing
        (r2, _) <- go ctx a2 [] $ Just $ Type (nf WHNF t1) lvl
        return (Apply (Path Implicit lvl) [Apply (Lam ["_"]) [Lambda $ Scope1 $ fmap Free t1], r1, r2],
                Type (cterm $ Universe lvl) $ succ lvl)
    go ctx (Apply (pos, At) [b,c]) ts Nothing = do
        (r1, Type t1 lvl) <- go ctx b [] Nothing
        (r2, _) <- go ctx c [] (Just intType)
        case nf WHNF t1 of
            Apply Path{} [a,b',c'] -> do
                (tes, ty) <- typeCheckApps pos ctx ts $ Type (Apply App [a,r2]) lvl
                return (apps (Apply At [b',c',r1,r2]) tes, ty)
            t1' -> throwError [emsgLC pos "" $ pretty "Expected type: Path"
                                            $$ pretty "Actual type:" <+> prettyOpen ctx t1']
    go ctx te ts (Just (Type ty _)) = do
        (te', Type ty' lvl') <- go ctx te ts Nothing
        actExpType ctx ty' ty (termPos te)
        return (te', Type ty' lvl')
    go _ _ _ _ = error "typeCheckCtx"

typeCheckKeyword :: (Monad m, Eq a) => Context a -> Posn -> String -> [Term (Posn, Syntax) Void]
    -> Maybe (Type Syntax a) -> TCM m (Term Syntax a, Type Syntax a)
typeCheckKeyword ctx pos u as Nothing | (lvl,""):_ <- reads u = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (cterm $ Universe lvl, Type (cterm $ Universe $ succ lvl) $ succ $ succ lvl)
typeCheckKeyword ctx pos "I" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (cterm Interval, Type (cterm $ Universe NoLevel) $ Level 1)
typeCheckKeyword ctx pos "left" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "left"]
    return (cterm $ ICon ILeft, intType)
typeCheckKeyword ctx pos "right" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "right"]
    return (cterm $ ICon IRight, intType)
typeCheckKeyword ctx pos "Path" [] _ = throwError [expectedArgErrorMsg pos "Path"]
typeCheckKeyword ctx pos "Path" (a:as) Nothing = do
    (r1, _, (v, t1)) <- typeCheckLambda ctx a intType
    lvl <- checkIsType (Snoc ctx v $ error "") (termPos a) t1
    let r1' c = Apply App [r1, cterm (ICon c)]
        mkType t = Type t (succ lvl)
    case as of
        [] -> return (Apply (Path Explicit lvl) [r1], mkType $
            Apply (Pi [] lvl $ succ lvl) [r1' ILeft, Apply (Pi [] lvl $ succ lvl) [r1' IRight, cterm $ Universe lvl]])
        [a2] -> do
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF $ r1' ILeft) lvl
            return (Apply (Path Explicit lvl) [r1,r2], mkType $ Apply (Pi [] lvl $ succ lvl) [r1' IRight, cterm $ Universe lvl])
        a2:a3:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF $ r1' ILeft) lvl
            (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ r1' IRight) lvl
            return (Apply (Path Explicit lvl) [r1,r2,r3], mkType $ cterm $ Universe lvl)
typeCheckKeyword ctx pos "path" [] _ = throwError [expectedArgErrorMsg pos "path"]
typeCheckKeyword ctx pos "path" (a:as) mty = do
    unless (null as) $ warn [argsErrorMsg pos "A path"]
    case mty of
        Nothing -> do
            (te, Type ty lvl, _) <- typeCheckLambda ctx a intType
            let te' c = Apply App [te, cterm $ ICon c]
            return (te, Type (Apply (Path Implicit lvl) [ty, te' ILeft, te' IRight]) lvl)
        Just (Type ty@(Apply (Path _ l1) [t1,_,_]) lvl) -> do
            (r,t) <- typeCheckCtx ctx a $ Just $
                Type (Apply (Pi ["i"] NoLevel l1) [cterm Interval, Lambda $ Scope1 $ Apply App [fmap Free t1, Var Bound]]) l1
            actExpType ctx (Apply (Path Implicit l1)
                [t1, Apply App [r, cterm $ ICon ILeft], Apply App [r, cterm $ ICon IRight]]) ty pos
            return (Apply PCon [r], Type ty lvl)
        Just (Type ty _) -> throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                                     $$ pretty "Actual type: Path"]
typeCheckKeyword ctx pos "coe" [] _ = throwError [expectedArgErrorMsg pos "coe"]
typeCheckKeyword ctx pos "coe" (a1:as) Nothing = do
    (r1, _, (v, t1)) <- typeCheckLambda ctx a1 intType
    lvl <- checkIsType (Snoc ctx v $ error "") (termPos a1) t1
    let res = Apply (Pi ["r"] NoLevel lvl) [cterm Interval, Lambda $ Scope1 $ Apply App [fmap Free r1, Var Bound]]
    case as of
        [] -> return (capps Coe [r1], Type (Apply (Pi ["l"] NoLevel lvl) [cterm Interval, Lambda $ Scope1 $
            Apply (Pi [] lvl lvl) [Apply App [fmap Free r1, Var Bound], fmap Free res]]) lvl)
        a2:as1 -> do
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            case as1 of
                [] -> return (capps Coe [r1,r2], Type (Apply (Pi [] lvl lvl) [Apply App [r1,r2], res]) lvl)
                a3:as2 -> do
                    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ Apply App [r1,r2]) lvl
                    case as2 of
                        [] -> return (capps Coe [r1,r2,r3], Type res lvl)
                        a4:as3 -> do
                            (r4, _) <- typeCheckCtx ctx a4 (Just intType)
                            (tes, ty) <- typeCheckApps pos ctx as3 $ Type (Apply App [r1,r4]) lvl
                            return (capps Coe $ [r1,r2,r3,r4] ++ tes, ty)
typeCheckKeyword ctx pos "iso" (a1:a2:a3:a4:a5:a6:as) Nothing = do
    (r1, Type t1 _) <- typeCheckCtx ctx a1 Nothing
    (r2, Type t2 _) <- typeCheckCtx ctx a2 Nothing
    let t1' = nf WHNF t1
        t2' = nf WHNF t2
    lvl1 <- checkIsType ctx (termPos a1) t1'
    lvl2 <- checkIsType ctx (termPos a2) t2'
    let lvl = max lvl1 lvl2
    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (Apply (Pi [] lvl1 lvl2) [r1,r2]) lvl
    (r4, _) <- typeCheckCtx ctx a4 $ Just $ Type (Apply (Pi [] lvl2 lvl1) [r2,r1]) lvl
    let h e s1 s3 s4 tlvl = typeCheckCtx ctx e $ Just $ Type (Apply (Pi ["x"] tlvl tlvl) [s1, Lambda $ Scope1 $
            Apply (Path Implicit tlvl) [Apply (Lam ["_"]) [Lambda $ Scope1 $ fmap (Free . Free) s1],
                Apply App [fmap Free s4, Apply App [fmap Free s3, Var Bound]], Var Bound]]) tlvl
    (r5, _) <- h a5 r1 r3 r4 lvl1
    (r6, _) <- h a6 r2 r4 r3 lvl2
    case as of
        [] -> return (capps Iso [r1,r2,r3,r4,r5,r6],
            Type (Apply (Pi [] NoLevel $ succ lvl) [cterm Interval, cterm $ Universe lvl]) $ succ lvl)
        a7:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r7, _) <- typeCheckCtx ctx a7 (Just intType)
            return (capps Iso [r1,r2,r3,r4,r5,r6,r7], Type (cterm $ Universe lvl) $ succ lvl)
typeCheckKeyword ctx pos "iso" _ Nothing = throwError [emsgLC pos "Expected at least 6 arguments to \"iso\"" enull]
typeCheckKeyword ctx pos "squeeze" as Nothing =
    let mkType t = Apply (Pi [] NoLevel NoLevel) [cterm Interval, t] in
    case as of
        [] -> return (cterm Squeeze, Type (mkType $ mkType $ cterm Interval) NoLevel)
        [a1] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            return (capps Squeeze [r1], Type (mkType $ cterm Interval) NoLevel)
        [a1,a2] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            return (capps Squeeze [r1,r2], intType)
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

actExpType :: (Monad m, Eq a) => Context a -> Term Syntax a -> Term Syntax a -> Posn -> EDocM m ()
actExpType ctx act exp pos =
    let act' = nf NF act
        exp' = nf NF exp
    in unless (act' `lessOrEqual` exp') $
        throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx exp'
                                 $$ pretty "Actual type:"   <+> prettyOpen ctx act']

typeCheckApps :: (Monad m, Eq a) => Posn -> Context a -> [Term (Posn, Syntax) Void] -> Type Syntax a -> TCM m ([Term Syntax a], Type Syntax a)
typeCheckApps pos ctx terms ty = go terms (nfType WHNF ty)
  where
    go [] ty = return ([], ty)
    go (term:terms) (Type (Apply p@(Pi _ lvl1 lvl2) [a,b]) _) = do
        (term, _)   <- typeCheckCtx ctx term $ Just (Type a lvl1)
        (terms, ty) <- go terms $ Type (nf WHNF $ case b of
            Lambda{} -> instantiate1 term $ snd (dropOnePi p a b)
            _        -> b) lvl2
        return (term:terms, ty)
    go _ (Type ty _) = throwError [emsgLC pos "" $ pretty "Expected pi type"
                                                $$ pretty "Actual type:" <+> prettyOpen ctx ty]

typeCheckLambda :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void -> Type Syntax a
    -> TCM m (Term Syntax a, Type Syntax a, (String, Term Syntax (Scoped a)))
typeCheckLambda ctx (Apply (pos, Lam (v:vs)) [te]) (Type ty lvl) = do
    (te', Type ty' lvl') <- typeCheckCtx (Snoc ctx v $ Type ty lvl) (if null vs then te else Apply (pos, Lam vs) [te]) Nothing
    let te'' = case te' of
                Apply (Lam vs') [te''] -> Apply (Lam $ v:vs') [Lambda $ Scope1 te'']
                _ -> Apply (Lam [v]) [Lambda $ Scope1 te']
    return (te'', Type (Apply (Pi [v] lvl lvl') [ty, Lambda $ Scope1 ty']) $ max lvl lvl', (v, ty'))
typeCheckLambda ctx te ty = do
    (te', Type ty' lvl') <- typeCheckCtx ctx te Nothing
    case nf WHNF ty' of
        ty''@(Apply p@(Pi vs lvla lvlb) [a,b]) ->
            let na = nf NF a
                Type nty lvlty = nfType NF ty
            in if (nty `lessOrEqual` na)
                then return (te', Type ty'' lvl', dropOnePi p a b)
                else throwError [emsgLC (termPos te) "" $
                        pretty "Expected type:" <+> prettyOpen ctx (Apply (Pi vs lvlty lvlb) [nty,b]) $$
                        pretty "Actual type:"   <+> prettyOpen ctx (Apply p [na,b])]
        _ -> throwError [emsgLC (termPos te) "" $ pretty "Expected pi type"
                                               $$ pretty "Actual type:" <+> prettyOpen ctx ty']
