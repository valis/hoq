module TypeChecking.Expressions
    ( typeCheck, typeCheckCtx
    , inferErrorMsg, notInScope
    , prettyOpen, checkIsType
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

type Context = Ctx String Posn (Type Posn) PIdent

prettyOpen :: Context a -> Term p a -> EDoc (Term p)
prettyOpen ctx term = epretty $ fmap (pretty . either id getName) $ close ctx (fmap Right term)

checkIsType :: Monad m => Context a -> Posn -> Term Posn a -> EDocM m Level
checkIsType _ _ (Universe _ lvl) = return lvl
checkIsType ctx pos t = throwError [emsgLC pos "" $ pretty "Expected type: Type" $$
                                                    pretty "Actual type:" <+> prettyOpen ctx t]

intType :: p -> Type p a
intType p = Type (Interval p) NoLevel

typeCheck :: Monad m => Term Posn PIdent -> Maybe (Type Posn PIdent) -> TCM m (Term Posn PIdent, Type Posn PIdent)
typeCheck = typeCheckCtx Nil

typeCheckCtx :: (Monad m, Eq a) => Context a -> Term Posn a -> Maybe (Type Posn a) -> TCM m (Term Posn a, Type Posn a)
typeCheckCtx ctx term mty = go ctx term [] $ fmap (nfType WHNF) mty
  where
    go :: (Monad m, Eq a) => Context a -> Term Posn a -> [Term Posn a] -> Maybe (Type Posn a) -> TCM m (Term Posn a, Type Posn a)
    go ctx (Var v) ts mty = do
        eres <- case lookupCtx (\s p -> s == getName p) getPos v ctx of
            Right (pos, ty) -> return $ Left (pos, Var v, ty)
            Left (PIdent pos _, Just (te, ty)) -> return $ Left (pos, te, ty)
            Left (PIdent pos "_", Nothing) -> throwError [emsgLC pos "Expected an identifier" enull]
            Left (PIdent pos var, Nothing) -> do
                mt <- lift $ getEntry var $ case mty of
                    Just (Type (DataType _ dt _ _) _) -> Just dt
                    _                                 -> Nothing
                let replaceConPos (Con _ i name conds args) = Con pos i name conds args
                    replaceConPos t = t
                case mt of
                    [FunctionE (FunCall _ name clauses) ty] -> return $ Left (pos, FunCall pos name clauses, fmap (liftBase ctx) ty)
                    [FunctionE (FunSyn _ name expr) ty]     -> return $ Left (pos, FunSyn  pos name expr   , fmap (liftBase ctx) ty)
                    [FunctionE te ty]                       -> return $ Left (pos, fmap (liftBase ctx) te  , fmap (liftBase ctx) ty)
                    DataTypeE ty e : _                      -> return $ Left (pos, DataType pos var e []   , fmap (liftBase ctx) ty)
                    [ConstructorE _ (ScopeTerm con) (ScopeTerm ty, lvl)] ->
                        return $ Left (pos, fmap (liftBase ctx) (replaceConPos con), Type (fmap (liftBase ctx) ty) lvl)
                    [ConstructorE _ con (ty, lvl)] -> case mty of
                        Just (Type (DataType _ _ _ params) _) ->
                            let liftTerm = instantiate params . fmap (liftBase ctx)
                            in  return $ Left (pos, replaceConPos (liftTerm con), Type (liftTerm ty) lvl)
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
            Left (pos, te, Type ty lvl) -> do
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
        return (Lam p (Scope1 v te), ty)
    go ctx (Lam p _) [] (Just (Type ty _)) = throwError [emsgLC p "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                                                    $$ pretty "But lambda expression has pi type"]
    go ctx (Lam p _) [] Nothing = throwError [inferErrorMsg p "the argument"]
    go ctx (Lam p (Scope1 v t1)) (t2:ts) mty = do
        (te2, ty2@(Type _ lvl2)) <- go ctx t2 [] Nothing
        (te1, Type ty1 lvl1) <- go (Snoc ctx v ty2) t1 (map (fmap Free) ts) $ fmap (fmap Free) mty
        return (Lam p (Scope1 v te1), Type (Pi p ty2 (Scope v $ ScopeTerm ty1) lvl1) $ max lvl1 lvl2)
    go ctx (Pi pos (Type a _) b _) ts Nothing = do
        (a', Type ty1 _) <- go ctx a [] Nothing
        lvl1 <- checkIsType ctx (getAttr (toBase ctx getPos) a) ty1
        (b', lvl2) <- typeCheckScope ctx (Type a' lvl1) b
        unless (null ts) $ warn [argsErrorMsg pos "A type"]
        let lvl = max lvl1 lvl2
        return (Pi pos (Type a' lvl1) b' lvl2, Type (Universe pos lvl) $ succ lvl)
    go ctx (Path pos Implicit _ [a1,a2]) ts Nothing = do
        unless (null ts) $ warn [argsErrorMsg pos "A type"]
        (r1, Type t1 lvl) <- go ctx a1 [] Nothing
        (r2, _) <- go ctx a2 [] $ Just $ Type (nf WHNF t1) lvl
        return (Path pos Implicit (Just (Lam pos $ Scope1 "_" $ fmap Free t1, lvl)) [r1,r2], Type (Universe pos lvl) $ succ lvl)
    go ctx (At _ b c) ts Nothing = do
        let pos = getAttr (toBase ctx getPos) b
        (r1, Type t1 lvl) <- go ctx b [] Nothing
        (r2, _) <- go ctx c [] $ Just (intType pos)
        case nf WHNF t1 of
            Path _ _ (Just (a,_)) [b',c'] -> do
                (tes, ty) <- typeCheckApps pos ctx ts $ Type (App a r2) lvl
                return (apps (At (Just (b', c')) r1 r2) tes, ty)
            Path _ _ Nothing _ -> throwError [emsgLC pos "Cannot infer type" enull]
            t1' -> throwError [emsgLC pos "" $ pretty "Expected type: Path"
                                            $$ pretty "Actual type:" <+> prettyOpen ctx t1']
    go ctx te ts (Just (Type ty _)) = do
        (te', Type ty' lvl') <- go ctx te ts Nothing
        actExpType ctx ty' ty $ getAttr (toBase ctx getPos) te
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
    -> Maybe (Type Posn a) -> TCM m (Term Posn a, Type Posn a)
typeCheckKeyword ctx pos u as Nothing | (lvl,""):_ <- reads u = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (Universe pos lvl, Type (Universe pos $ succ lvl) $ succ $ succ lvl)
typeCheckKeyword ctx pos "I" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (Interval pos, Type (Universe pos NoLevel) $ Level 1)
typeCheckKeyword ctx pos "left" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "left"]
    return (ICon pos ILeft, Type (Interval pos) NoLevel)
typeCheckKeyword ctx pos "right" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "right"]
    return (ICon pos IRight, Type (Interval pos) NoLevel)
typeCheckKeyword ctx pos "Path" [] _ = throwError [expectedArgErrorMsg pos "Path"]
typeCheckKeyword ctx pos "Path" (a:as) Nothing = do
    (r1, _, Scope1 v t1) <- typeCheckLambda ctx a (intType pos)
    lvl <- checkIsType (Snoc ctx v $ error "") (getAttr (toBase ctx getPos) a) t1
    let r1' c = Type (App r1 $ ICon pos c) lvl
        mkType t = Type t (succ lvl)
    case as of
        [] -> return (Path pos Explicit (Just (r1,lvl)) [], mkType $
            Pi pos (r1' ILeft) (ScopeTerm $ Pi pos (r1' IRight) (ScopeTerm $ Universe pos lvl) $ succ lvl) $ succ lvl)
        [a2] -> do
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ nfType WHNF (r1' ILeft)
            return (Path pos Explicit (Just (r1,lvl)) [r2], mkType $
                Pi pos (r1' IRight) (ScopeTerm $ Universe pos lvl) $ succ lvl)
        a2:a3:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ nfType WHNF (r1' ILeft)
            (r3, _) <- typeCheckCtx ctx a3 $ Just $ nfType WHNF (r1' IRight)
            return (Path pos Explicit (Just (r1,lvl)) [r2,r3], mkType $ Universe pos lvl)
typeCheckKeyword ctx pos "path" [] _ = throwError [expectedArgErrorMsg pos "path"]
typeCheckKeyword ctx pos "path" (a:as) mty = do
    unless (null as) $ warn [argsErrorMsg pos "A path"]
    case mty of
        Nothing -> do
            (te, ty, _) <- typeCheckLambda ctx a (intType pos)
            return (te, ty)
        Just (Type ty@(Path p h mt1 _) lvl) -> do
            (r,t) <- typeCheckCtx ctx a $ fmap (\(t1,l1) -> Type
                (Pi pos (intType pos) (Scope "i" $ ScopeTerm $ App (fmap Free t1) $ Var $ Bound pos) l1) l1) mt1
            actExpType ctx (Path p Implicit Nothing [App r (ICon p ILeft), App r (ICon p IRight)]) ty pos
            return (PCon pos (Just r), Type ty lvl)
        Just (Type ty _) -> throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx ty
                                                     $$ pretty "Actual type: Path"]
typeCheckKeyword ctx pos "coe" [] _ = throwError [expectedArgErrorMsg pos "coe"]
typeCheckKeyword ctx pos "coe" (a1:as) Nothing = do
    (r1, _, Scope1 v t1) <- typeCheckLambda ctx a1 (intType pos)
    lvl <- checkIsType (Snoc ctx v $ error "") (getAttr (toBase ctx getPos) a1) t1
    let res = Pi pos (intType pos) (Scope "r" $ ScopeTerm $ App (fmap Free r1) $ Var $ Bound pos) lvl
    case as of
        [] -> return (Coe pos [r1], Type (Pi pos (intType pos) (Scope "l" $ ScopeTerm $
            Pi pos (Type (App (fmap Free r1) $ Var $ Bound pos) lvl) (ScopeTerm $ fmap Free res) lvl) lvl) lvl)
        a2:as1 -> do
            (r2, _) <- typeCheckCtx ctx a2 $ Just (intType pos)
            case as1 of
                [] -> return (Coe pos [r1,r2], Type (Pi pos (Type (App r1 r2) lvl) (ScopeTerm res) lvl) lvl)
                a3:as2 -> do
                    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ App r1 r2) lvl
                    case as2 of
                        [] -> return (Coe pos [r1,r2,r3], Type res lvl)
                        a4:as3 -> do
                            (r4, _) <- typeCheckCtx ctx a4 $ Just (intType pos)
                            (tes, ty) <- typeCheckApps pos ctx as3 $ Type (App r1 r4) lvl
                            return (Coe pos $ [r1,r2,r3,r4] ++ tes, ty)
typeCheckKeyword ctx pos "iso" (a1:a2:a3:a4:a5:a6:as) Nothing = do
    (r1, Type t1 _) <- typeCheckCtx ctx a1 Nothing
    (r2, Type t2 _) <- typeCheckCtx ctx a2 Nothing
    let t1' = nf WHNF t1
        t2' = nf WHNF t2
    lvl1 <- checkIsType ctx (getAttr (toBase ctx getPos) a1) t1'
    lvl2 <- checkIsType ctx (getAttr (toBase ctx getPos) a2) t2'
    let lvl = max lvl1 lvl2
    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (Pi pos (Type r1 lvl1) (ScopeTerm r2) lvl2) lvl
    (r4, _) <- typeCheckCtx ctx a4 $ Just $ Type (Pi pos (Type r2 lvl2) (ScopeTerm r1) lvl1) lvl
    let h e s1 s3 s4 tlvl = typeCheckCtx ctx e $ Just $ Type (Pi pos (Type s1 tlvl) (Scope "x" $
            ScopeTerm $ Path pos Implicit (Just (Lam pos $ Scope1 "_" $ fmap (Free . Free) s1, tlvl))
            [App (fmap Free s4) $ App (fmap Free s3) $ Var $ Bound pos, Var $ Bound pos]) tlvl) tlvl
    (r5, _) <- h a5 r1 r3 r4 lvl1
    (r6, _) <- h a6 r2 r4 r3 lvl2
    case as of
        [] -> return (Iso pos [r1,r2,r3,r4,r5,r6],
            Type (Pi pos (intType pos) (ScopeTerm $ Universe pos lvl) $ succ lvl) $ succ lvl)
        a7:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r7, _) <- typeCheckCtx ctx a7 $ Just (intType pos)
            return (Iso pos [r1,r2,r3,r4,r5,r6,r7], Type (Universe pos lvl) $ succ lvl)
typeCheckKeyword ctx pos "iso" _ Nothing = throwError [emsgLC pos "Expected at least 6 arguments to \"iso\"" enull]
typeCheckKeyword ctx pos "squeeze" as Nothing =
    let ty = Pi pos (intType pos) (ScopeTerm $ Interval pos) NoLevel in
    case as of
        [] -> return (Squeeze pos [], Type (Pi pos (intType pos) (ScopeTerm ty) NoLevel) NoLevel)
        [a1] -> do
            (r1, _) <- typeCheckCtx ctx a1 $ Just (intType pos)
            return (Squeeze pos [r1], Type ty NoLevel)
        [a1,a2] -> do
            (r1, _) <- typeCheckCtx ctx a1 $ Just (intType pos)
            (r2, _) <- typeCheckCtx ctx a2 $ Just (intType pos)
            return (Squeeze pos [r1,r2], intType pos)
        _ -> throwError [argsErrorMsg pos "squeeze _ _"]
typeCheckKeyword ctx pos var ts (Just (Type ty _)) = do
    (te', Type ty' lvl') <- typeCheckKeyword ctx pos var ts Nothing
    actExpType ctx ty' ty pos
    return (te', Type ty' lvl')
typeCheckKeyword _ pos var _ _ = throwError [notInScope pos "" var]

actExpType :: (Monad m, Eq a) => Context a -> Term Posn a -> Term Posn a -> Posn -> EDocM m ()
actExpType ctx act exp pos =
    let act' = nf NF act
        exp' = nf NF exp
    in unless (act' `lessOrEqual` exp') $
        throwError [emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen ctx exp'
                                 $$ pretty "Actual type:"   <+> prettyOpen ctx act']

typeCheckScope :: (Monad m, Eq a) => Context a -> Type Posn a
    -> Scope String Posn (Term Posn) a -> TCM m (Scope String Posn (Term Posn) a, Level)
typeCheckScope ctx _ (ScopeTerm b) = do
    (te, Type ty _) <- typeCheckCtx ctx b Nothing
    lvl <- checkIsType ctx (getAttr (toBase ctx getPos) b) ty
    return (ScopeTerm te, lvl)
typeCheckScope ctx a (Scope v b) = do
    (te, ty) <- typeCheckScope (Snoc ctx v a) (fmap Free a) b
    return (Scope v te, ty)

typeCheckApps :: (Monad m, Eq a) => Posn -> Context a -> [Term Posn a] -> Type Posn a -> TCM m ([Term Posn a], Type Posn a)
typeCheckApps pos ctx terms ty = go terms (nfType WHNF ty)
  where
    go [] ty = return ([], ty)
    go (term:terms) (Type (Pi p a b lvl') _) = do
        (term, _)   <- typeCheckCtx ctx term (Just a)
        (terms, ty) <- go terms $ Type (nf WHNF $ instantiate1 term $ unScope1 $ dropOnePi p a b lvl') lvl'
        return (term:terms, ty)
    go _ (Type ty _) = throwError [emsgLC pos "" $ pretty "Expected pi type"
                                                $$ pretty "Actual type:" <+> prettyOpen ctx ty]

typeCheckLambda :: (Monad m, Eq a) => Context a -> Term Posn a -> Type Posn a
    -> TCM m (Term Posn a, Type Posn a, Scope1 String Posn (Term Posn) a)
typeCheckLambda ctx (Lam pos (Scope1 v te)) ty@(Type _ lvl) = do
    (te', Type ty' lvl') <- typeCheckCtx (Snoc ctx v ty) te Nothing
    return (Lam pos (Scope1 v te'), Type (Pi pos ty (Scope v $ ScopeTerm ty') lvl') $ max lvl lvl', Scope1 v ty')
typeCheckLambda ctx te ty = do
    (te, Type ty' lvl') <- typeCheckCtx ctx te Nothing
    case nf WHNF ty' of
        ty'@(Pi p a b lvlb) ->
            let Type na lvla = nfType NF a
                Type nty lvlty = nfType NF ty
            in if (nty `lessOrEqual` na)
                then return (te, Type ty' lvl', dropOnePi p a b lvlb)
                else throwError [emsgLC (getAttr (toBase ctx getPos) te) "" $
                        pretty "Expected type:" <+> prettyOpen ctx (Pi p (Type nty lvlty) b lvlb) $$
                        pretty "Actual type:"   <+> prettyOpen ctx (Pi p (Type na  lvla)  b lvlb)]
        _ -> throwError [emsgLC (getAttr (toBase ctx getPos) te) "" $ pretty "Expected pi type"
                                                                   $$ pretty "Actual type:" <+> prettyOpen ctx ty']
