module TypeChecking.Expressions
    ( typeCheck, typeCheckCtx
    , inferErrorMsg, notInScope
    , prettyOpen, checkIsType
    , termPos
    ) where

import Control.Monad
import Data.List
import Data.Maybe

import Syntax.Term
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

type Context = Ctx String (Type ()) PIdent

prettyOpen :: Context a -> Term p a -> EDoc (Term p)
prettyOpen ctx term = epretty $ fmap (pretty . either id getName) $ close ctx (fmap Right term)

checkIsType :: Monad m => Context a -> Posn -> Term () a -> EDocM m Level
checkIsType _ _ (Universe _ lvl) = return lvl
checkIsType ctx pos t = throwError [emsgLC pos "" $ pretty "Expected type: Type" $$
                                                    pretty "Actual type:" <+> prettyOpen ctx t]

intType :: Type () a
intType = Type (Interval ()) NoLevel

termPos :: Context a -> Term Posn a -> Posn
termPos ctx = getAttr $ maybe (0,0) getPos . toBase ctx

typeCheck :: Monad m => Term Posn PIdent -> Maybe (Type () PIdent) -> TCM m (Term () PIdent, Type () PIdent)
typeCheck = typeCheckCtx Nil

typeCheckCtx :: (Monad m, Eq a) => Context a -> Term Posn a -> Maybe (Type () a) -> TCM m (Term () a, Type () a)
typeCheckCtx ctx term mty = go ctx term [] $ fmap (nfType WHNF) mty
  where
    go :: (Monad m, Eq a) => Context a -> Term Posn a -> [Term Posn a] -> Maybe (Type () a) -> TCM m (Term () a, Type () a)
    go ctx (Var v) ts mty = do
        let v'@(PIdent pos var) = fromJust (toBase ctx v)
        when (var == "_") $ throwError [emsgLC pos "Expected an identifier" enull]
        eres <- case lookupCtx (\s p -> s == getName p) v' ctx of
            Just r -> return (Left r)
            Nothing -> do
                mt <- lift $ getEntry var $ case mty of
                    Just (Type (DataType _ dt _ _) _) -> Just dt
                    _                                 -> Nothing
                case mt of
                    [FunctionE (FunCall _ name clauses) ty] -> return $ Left (FunCall  () name clauses, fmap (liftBase ctx) $ mapType (const ()) ty)
                    [FunctionE (FunSyn _ name expr) ty]     -> return $ Left (FunSyn   () name expr   , fmap (liftBase ctx) $ mapType (const ()) ty)
                    DataTypeE ty e : _                      -> return $ Left (DataType () var e []    , fmap (liftBase ctx) $ mapType (const ()) ty)
                    [ConstructorE _ (ScopeTerm con) (ScopeTerm ty, lvl)] ->
                        return $ Left (fmap (liftBase ctx) $ mapTerm (const ()) con, Type (fmap (liftBase ctx) $ mapTerm (const ()) ty) lvl)
                    [ConstructorE _ con (ty, lvl)] -> case mty of
                        Just (Type (DataType _ _ _ params) _) ->
                            let liftTerm = instantiate params . fmap (liftBase ctx) . mapScope' (const ())
                            in  return $ Left (liftTerm con, Type (liftTerm ty) lvl)
                        Just (Type ty _) -> throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                                                     $$ pretty ("But given data constructor " ++ show var)]
                        Nothing -> throwError [inferParamsErrorMsg pos var]
                    [] -> do
                        cons <- lift (getConstructorDataTypes var)
                        let Type (DataType _ dataType _ _) _ = fromJust mty
                        case cons of
                            []    -> liftM Right (typeCheckKeyword ctx pos var ts mty)
                            [act] -> throwError [emsgLC pos "" $
                                pretty ("Expected data type: " ++ dataType) $$
                                pretty ("Actual data type: " ++ act)]
                            acts -> throwError [emsgLC pos "" $
                                pretty ("Expected data type: " ++ dataType) $$
                                pretty ("Posible data types: " ++ intercalate ", " acts)]
                    _  -> throwError [inferErrorMsg pos $ show var]
        case eres of
            Left (te, Type ty lvl) -> do
                (tes, Type ty' lvl') <- typeCheckApps pos ctx ts (Type ty lvl)
                case (mty, ty') of
                    (Nothing, _)  -> return ()
                    (Just (Type (DataType _ edt _ _) _), DataType _ adt _ []) -> unless (edt == adt) $
                        throwError [emsgLC pos "" $ pretty ("Expected data type: " ++ edt)
                                                 $$ pretty ("Actual data type: " ++ adt)]
                    (Just (Type ety _), _) -> actExpType ctx ty' ety pos
                return (apps te tes, Type ty' lvl')
            Right res -> return res
    go ctx (App t1 t2) ts ty = go ctx t1 (t2:ts) ty
    go ctx (Lam p (Scope1 v t)) [] (Just ty@(Type (Pi p' a b lvl2) _)) = do
        (te, _) <- go (Snoc ctx v a) t [] $ Just $ Type (nf WHNF $ unScope1 $ dropOnePi p' a b lvl2) lvl2
        return (Lam () $ Scope1 v te, ty)
    go ctx (Lam p _) [] (Just (Type ty _)) = throwError [emsgLC p "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                                                    $$ pretty "But lambda expression has pi type"]
    go ctx (Lam p _) [] Nothing = throwError [inferErrorMsg p "the argument"]
    go ctx (Lam p (Scope1 v t1)) (t2:ts) mty = do
        (te2, ty2@(Type _ lvl2)) <- go ctx t2 [] Nothing
        (te1, Type ty1 lvl1) <- go (Snoc ctx v ty2) t1 (map (fmap Free) ts) $ fmap (fmap Free) mty
        return (Lam () (Scope1 v te1), Type (Pi () ty2 (Scope v $ ScopeTerm ty1) lvl1) $ max lvl1 lvl2)
    go ctx (Pi pos (Type a _) b _) ts Nothing = do
        (a', Type ty1 _) <- go ctx a [] Nothing
        lvl1 <- checkIsType ctx (termPos ctx a) ty1
        (b', lvl2) <- typeCheckScope ctx (Type a' lvl1) b
        unless (null ts) $ warn [argsErrorMsg pos "A type"]
        let lvl = max lvl1 lvl2
        return (Pi () (Type a' lvl1) b' lvl2, Type (Universe () lvl) $ succ lvl)
    go ctx (Path pos Implicit _ [a1,a2]) ts Nothing = do
        unless (null ts) $ warn [argsErrorMsg pos "A type"]
        (r1, Type t1 lvl) <- go ctx a1 [] Nothing
        (r2, _) <- go ctx a2 [] $ Just $ Type (nf WHNF t1) lvl
        return (Path () Implicit (Just (Lam () $ Scope1 "_" $ fmap Free t1, lvl)) [r1,r2], Type (Universe () lvl) $ succ lvl)
    go ctx (At _ b c) ts Nothing = do
        let pos = termPos ctx b
        (r1, Type t1 lvl) <- go ctx b [] Nothing
        (r2, _) <- go ctx c [] (Just intType)
        case nf WHNF t1 of
            Path _ _ (Just (a,_)) [b',c'] -> do
                (tes, ty) <- typeCheckApps pos ctx ts $ Type (App a r2) lvl
                return (apps (At (Just (b', c')) r1 r2) tes, ty)
            Path _ _ Nothing _ -> throwError [emsgLC pos "Cannot infer type" enull]
            t1' -> throwError [emsgLC pos "" $ pretty "Expected type: Path"
                                            $$ pretty "Actual type:" <+> prettyOpen ctx t1']
    go ctx te ts (Just (Type ty _)) = do
        (te', Type ty' lvl') <- go ctx te ts Nothing
        actExpType ctx ty' ty (termPos ctx te)
        return (te', Type ty' lvl')
    go _ Con{} _ _ = error "typeCheck: Con"
    go _ FunCall{} _ _ = error "typeCheck: FunCall"
    go _ FunSyn{} _ _ = error "typeCheck: FunSyn"
    go _ DataType{} _ _ = error "typeCheck: DataType"
    go _ Squeeze{} _ _ = error "typeCheck: Squeeze"
    go _ Iso{} _ _ = error "typeCheck: Iso"
    go _ Coe{} _ _ = error "typeCheck: Coe"
    go _ PCon{} _ _ = error "typeCheck: PCon"
    go _ Path{} _ _ = error "typeCheck: Path"
    go _ ICon{} _ _ = error "typeCheck: ICon"
    go _ Interval{} _ _ = error "typeCheck: Interval"
    go _ Universe{} _ _ = error "typeCheck: Universe"

typeCheckKeyword :: (Monad m, Eq a) => Context a -> Posn -> String -> [Term Posn a]
    -> Maybe (Type () a) -> TCM m (Term () a, Type () a)
typeCheckKeyword ctx pos u as Nothing | (lvl,""):_ <- reads u = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (Universe () lvl, Type (Universe () $ succ lvl) $ succ $ succ lvl)
typeCheckKeyword ctx pos "I" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (Interval (), Type (Universe () NoLevel) $ Level 1)
typeCheckKeyword ctx pos "left" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "left"]
    return (ICon () ILeft, intType)
typeCheckKeyword ctx pos "right" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "right"]
    return (ICon () IRight, intType)
typeCheckKeyword ctx pos "Path" [] _ = throwError [expectedArgErrorMsg pos "Path"]
typeCheckKeyword ctx pos "Path" (a:as) Nothing = do
    (r1, _, Scope1 v t1) <- typeCheckLambda ctx a intType
    lvl <- checkIsType (Snoc ctx v $ error "") (termPos ctx a) t1
    let r1' c = Type (App r1 $ ICon () c) lvl
        mkType t = Type t (succ lvl)
    case as of
        [] -> return (Path () Explicit (Just (r1,lvl)) [], mkType $
            Pi () (r1' ILeft) (ScopeTerm $ Pi () (r1' IRight) (ScopeTerm $ Universe () lvl) $ succ lvl) $ succ lvl)
        [a2] -> do
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ nfType WHNF (r1' ILeft)
            return (Path () Explicit (Just (r1,lvl)) [r2], mkType $
                Pi () (r1' IRight) (ScopeTerm $ Universe () lvl) $ succ lvl)
        a2:a3:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ nfType WHNF (r1' ILeft)
            (r3, _) <- typeCheckCtx ctx a3 $ Just $ nfType WHNF (r1' IRight)
            return (Path () Explicit (Just (r1,lvl)) [r2,r3], mkType $ Universe () lvl)
typeCheckKeyword ctx pos "path" [] _ = throwError [expectedArgErrorMsg pos "path"]
typeCheckKeyword ctx pos "path" (a:as) mty = do
    unless (null as) $ warn [argsErrorMsg pos "A path"]
    case mty of
        Nothing -> do
            (te, ty, _) <- typeCheckLambda ctx a intType
            return (te, ty)
        Just (Type ty@(Path _ h mt1 _) lvl) -> do
            (r,t) <- typeCheckCtx ctx a $ fmap (\(t1,l1) -> Type
                (Pi () intType (Scope "i" $ ScopeTerm $ App (fmap Free t1) $ Var Bound) l1) l1) mt1
            actExpType ctx (Path () Implicit Nothing [App r (ICon () ILeft), App r (ICon () IRight)]) ty pos
            return (PCon () (Just r), Type ty lvl)
        Just (Type ty _) -> throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                                     $$ pretty "Actual type: Path"]
typeCheckKeyword ctx pos "coe" [] _ = throwError [expectedArgErrorMsg pos "coe"]
typeCheckKeyword ctx pos "coe" (a1:as) Nothing = do
    (r1, _, Scope1 v t1) <- typeCheckLambda ctx a1 intType
    lvl <- checkIsType (Snoc ctx v $ error "") (termPos ctx a1) t1
    let res = Pi () intType (Scope "r" $ ScopeTerm $ App (fmap Free r1) $ Var Bound) lvl
    case as of
        [] -> return (Coe () [r1], Type (Pi () intType (Scope "l" $ ScopeTerm $
            Pi () (Type (App (fmap Free r1) $ Var Bound) lvl) (ScopeTerm $ fmap Free res) lvl) lvl) lvl)
        a2:as1 -> do
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            case as1 of
                [] -> return (Coe () [r1,r2], Type (Pi () (Type (App r1 r2) lvl) (ScopeTerm res) lvl) lvl)
                a3:as2 -> do
                    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ App r1 r2) lvl
                    case as2 of
                        [] -> return (Coe () [r1,r2,r3], Type res lvl)
                        a4:as3 -> do
                            (r4, _) <- typeCheckCtx ctx a4 (Just intType)
                            (tes, ty) <- typeCheckApps pos ctx as3 $ Type (App r1 r4) lvl
                            return (Coe () $ [r1,r2,r3,r4] ++ tes, ty)
typeCheckKeyword ctx pos "iso" (a1:a2:a3:a4:a5:a6:as) Nothing = do
    (r1, Type t1 _) <- typeCheckCtx ctx a1 Nothing
    (r2, Type t2 _) <- typeCheckCtx ctx a2 Nothing
    let t1' = nf WHNF t1
        t2' = nf WHNF t2
    lvl1 <- checkIsType ctx (termPos ctx a1) t1'
    lvl2 <- checkIsType ctx (termPos ctx a2) t2'
    let lvl = max lvl1 lvl2
    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (Pi () (Type r1 lvl1) (ScopeTerm r2) lvl2) lvl
    (r4, _) <- typeCheckCtx ctx a4 $ Just $ Type (Pi () (Type r2 lvl2) (ScopeTerm r1) lvl1) lvl
    let h e s1 s3 s4 tlvl = typeCheckCtx ctx e $ Just $ Type (Pi () (Type s1 tlvl) (Scope "x" $
            ScopeTerm $ Path () Implicit (Just (Lam () $ Scope1 "_" $ fmap (Free . Free) s1, tlvl))
            [App (fmap Free s4) $ App (fmap Free s3) $ Var Bound, Var Bound]) tlvl) tlvl
    (r5, _) <- h a5 r1 r3 r4 lvl1
    (r6, _) <- h a6 r2 r4 r3 lvl2
    case as of
        [] -> return (Iso () [r1,r2,r3,r4,r5,r6],
            Type (Pi () intType (ScopeTerm $ Universe () lvl) $ succ lvl) $ succ lvl)
        a7:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r7, _) <- typeCheckCtx ctx a7 (Just intType)
            return (Iso () [r1,r2,r3,r4,r5,r6,r7], Type (Universe () lvl) $ succ lvl)
typeCheckKeyword ctx pos "iso" _ Nothing = throwError [emsgLC pos "Expected at least 6 arguments to \"iso\"" enull]
typeCheckKeyword ctx pos "squeeze" as Nothing =
    let ty = Pi () intType (ScopeTerm $ Interval ()) NoLevel in
    case as of
        [] -> return (Squeeze () [], Type (Pi () intType (ScopeTerm ty) NoLevel) NoLevel)
        [a1] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            return (Squeeze () [r1], Type ty NoLevel)
        [a1,a2] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            return (Squeeze () [r1,r2], intType)
        _ -> throwError [argsErrorMsg pos "squeeze _ _"]
typeCheckKeyword ctx pos var ts (Just (Type ty _)) = do
    (te', Type ty' lvl') <- typeCheckKeyword ctx pos var ts Nothing
    actExpType ctx ty' ty pos
    return (te', Type ty' lvl')
typeCheckKeyword _ pos var _ _ = throwError [notInScope pos "" var]

actExpType :: (Monad m, Eq a) => Context a -> Term () a -> Term () a -> Posn -> EDocM m ()
actExpType ctx act exp pos =
    let act' = nf NF act
        exp' = nf NF exp
    in unless (act' `lessOrEqual` exp') $
        throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx exp'
                                 $$ pretty "Actual type:"   <+> prettyOpen ctx act']

typeCheckScope :: (Monad m, Eq a) => Context a -> Type () a
    -> Scope String (Term Posn) a -> TCM m (Scope String (Term ()) a, Level)
typeCheckScope ctx _ (ScopeTerm b) = do
    (te, Type ty _) <- typeCheckCtx ctx b Nothing
    lvl <- checkIsType ctx (termPos ctx b) ty
    return (ScopeTerm te, lvl)
typeCheckScope ctx a (Scope v b) = do
    (te, ty) <- typeCheckScope (Snoc ctx v a) (fmap Free a) b
    return (Scope v te, ty)

typeCheckApps :: (Monad m, Eq a) => Posn -> Context a -> [Term Posn a] -> Type () a -> TCM m ([Term () a], Type () a)
typeCheckApps pos ctx terms ty = go terms (nfType WHNF ty)
  where
    go [] ty = return ([], ty)
    go (term:terms) (Type (Pi p a b lvl') _) = do
        (term, _)   <- typeCheckCtx ctx term (Just a)
        (terms, ty) <- go terms $ Type (nf WHNF $ instantiate1 term $ unScope1 $ dropOnePi p a b lvl') lvl'
        return (term:terms, ty)
    go _ (Type ty _) = throwError [emsgLC pos "" $ pretty "Expected pi type"
                                                $$ pretty "Actual type:" <+> prettyOpen ctx ty]

typeCheckLambda :: (Monad m, Eq a) => Context a -> Term Posn a -> Type () a
    -> TCM m (Term () a, Type () a, Scope1 String (Term ()) a)
typeCheckLambda ctx (Lam _ (Scope1 v te)) ty@(Type _ lvl) = do
    (te', Type ty' lvl') <- typeCheckCtx (Snoc ctx v ty) te Nothing
    return (Lam () $ Scope1 v te', Type (Pi () ty (Scope v $ ScopeTerm ty') lvl') $ max lvl lvl', Scope1 v ty')
typeCheckLambda ctx te ty = do
    (te', Type ty' lvl') <- typeCheckCtx ctx te Nothing
    case nf WHNF ty' of
        ty'@(Pi p a b lvlb) ->
            let Type na lvla = nfType NF a
                Type nty lvlty = nfType NF ty
            in if (nty `lessOrEqual` na)
                then return (te', Type ty' lvl', dropOnePi p a b lvlb)
                else throwError [emsgLC (termPos ctx te) "" $
                        pretty "Expected type:" <+> prettyOpen ctx (Pi p (Type nty lvlty) b lvlb) $$
                        pretty "Actual type:"   <+> prettyOpen ctx (Pi p (Type na  lvla)  b lvlb)]
        _ -> throwError [emsgLC (termPos ctx te) "" $ pretty "Expected pi type"
                                                   $$ pretty "Actual type:" <+> prettyOpen ctx ty']
