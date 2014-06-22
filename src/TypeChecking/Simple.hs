{-# LANGUAGE GADTs #-}

module TypeChecking.Simple
    ( typeCheck
    , typeCheckDefs
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import Syntax.Context
import TypeChecking.Definitions
import TypeChecking.Expressions
import TypeChecking.Monad
import Normalization

data TermsInCtx a where
    TermsInCtx :: Eq b => Ctx Int [String] Term a b -> [Term b] -> Term b -> TermsInCtx a

typeCheckPattern :: (Monad m, Eq a) => Ctx Int [String] Term String a
    -> Term a -> ParPat -> TCM m (TermInCtx Int [String] Term a)
typeCheckPattern ctx ty (ParVar arg) = return $ TermInCtx (Snoc Nil [unArg arg] ty) $ T.Var (B 0)
typeCheckPattern ctx (DataType dt params) (ParPat _ (E.Pattern (PIdent (lc,conName)) pats)) = do
    cons <- lift $ getConstructor conName (Just dt)
    (i, conType) <- case cons of
        []                     -> throwError [notInScope lc "data constructor" conName]
        (i, Left  conType) : _ -> return (i, fmap (liftBase ctx) conType)
        (i, Right conType) : _ -> return (i, conType >>= \v -> case v of
                                                                B i -> reverse params !! i
                                                                F a -> T.Var $ liftBase ctx a)
    TermsInCtx ctx' terms _ <- typeCheckPatterns ctx conType pats
    return $ TermInCtx ctx' (T.Con i conName terms)
typeCheckPattern ctx ty (ParPat (PPar (lc,_)) _) =
    throwError [emsgLC lc "" $ pretty "Unexpected pattern" $$
                               pretty "Expected type:" <+> prettyOpen ctx ty]

typeCheckPatterns :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Term a -> [ParPat] -> TCM m (TermsInCtx a)
typeCheckPatterns _ ty [] = return $ TermsInCtx Nil [] ty
typeCheckPatterns ctx (T.Arr a b) (pat:pats) = do
    TermInCtx ctx' te <- typeCheckPattern ctx a pat
    TermsInCtx ctx'' tes ty <- typeCheckPatterns (ctx +++ ctx') (nf WHNF $ fmap (liftBase ctx') b) pats
    return $ TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty
typeCheckPatterns ctx (T.Pi fl a b) (pat:pats) = do
    TermInCtx ctx' te <- typeCheckPattern ctx a pat
    let b' = either (T.Pi fl $ fmap (liftBase ctx') a) id $ instantiateNames1 te $ fmap (liftBase ctx') b
    TermsInCtx ctx'' tes ty <- typeCheckPatterns (ctx +++ ctx') (nf WHNF b') pats
    return $ TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty
typeCheckPatterns _ _ (pat:_) = throwError [emsgLC (parPatGetPos pat) "Too many arguments" enull]

typeCheckDefs :: MonadFix m => [Def] -> TCM m ()
typeCheckDefs defs = splitDefs defs >>= mapM_ (\t -> typeCheckPDef t `catchError` warn)

typeCheckPDef :: MonadFix m => PDef -> TCM m ()
typeCheckPDef (PDefSyn arg expr) = do
    (term, ty) <- typeCheck expr Nothing
    addFunctionCheck arg (FunSyn (unArg arg) term) ty
typeCheckPDef (PDefCases arg ety cases) = do
    (ty, u) <- typeCheck ety Nothing
    case u of
        T.Universe _ -> return ()
        _            -> throwError [emsgLC (getPos ety) "" $ pretty "Expected a type" $$
                                                             pretty "Actual type:" <+> prettyOpen Nil ty]
    mfix $ \te -> do
        addFunctionCheck arg te ty
        names <- forM cases $ \(pats,expr) -> do
            TermsInCtx ctx terms ty' <- typeCheckPatterns Nil (nf WHNF ty) pats
            (term, _) <- typeCheckCtx ctx expr $ Just (nf WHNF ty')
            pats' <- mapM parPatToPattern pats
            return $ Name pats' $ toScope (abstractTermInCtx ctx term)
        return $ FunCall (unArg arg) names
    return ()
typeCheckPDef (PDefData arg params cons) =
    if null params 
    then do
        addDataTypeCheck arg (T.Universe NoLevel)
        lvls <- forM (zip cons [0..]) $ \((con,tele),i) -> do
            (_, conType, conLevel) <- checkTele Nil tele (T.Universe NoLevel)
            checkPositivity (nf WHNF conType)
            addConstructorCheck con name i (Left conType)
            return conLevel
        lift $ deleteDataType name
        lift $ addDataType name $ T.Universe (maximum lvls)
    else do
        (CtxFrom ctx, dataType, _) <- checkTele Nil params (T.Universe NoLevel)
        addDataTypeCheck arg dataType
        lvls <- forM (zip cons [0..]) $ \((con,tele),i) -> do
            (_, conType, conLevel) <- checkTele ctx tele $ fmap (liftBase ctx) dataType
            checkPositivity (nf WHNF conType)
            addConstructorCheck con name i $ Right (abstractTermInCtx ctx conType)
            return conLevel
        lift $ deleteDataType name
        lift $ addDataType name $ replaceLevel dataType (maximum lvls)
  where
    name = unArg arg
    
    checkTele :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Tele -> Term a ->
        TCM m (CtxFrom Int [String] Term String, Term a, Level)
    checkTele ctx [] term = return (CtxFrom ctx, term, NoLevel)
    checkTele ctx (([],expr):tele) term = do
        (r1,t1) <- typeCheckCtx ctx expr Nothing
        (rctx,r2,t2) <- checkTele ctx tele term
        T.Universe t <- checkUniverses ctx ctx expr expr t1 (T.Universe t2)
        return (rctx, T.Arr r1 r2, t)
    checkTele ctx ((args,expr):tele) term = do
        (r1,t1) <- typeCheckCtx ctx expr Nothing
        let vars = map unArg args
            ctx' = Snoc ctx (reverse vars) r1
        (rctx,r2,t2) <- checkTele ctx' tele (fmap F term)
        T.Universe t <- checkUniverses ctx ctx' expr expr t1 (T.Universe t2)
        return (rctx, T.Pi (null tele) r1 $ Name vars $ toScope r2, t)
    
    replaceLevel :: Term a -> Level -> Term a
    replaceLevel (T.Pi fl r1 (Name vars (Scope r2))) lvl = T.Pi fl r1 $ Name vars $ Scope (replaceLevel r2 lvl)
    replaceLevel _ lvl = T.Universe lvl
    
    checkPositivity :: Monad m => Term a -> EDocM m ()
    checkPositivity (T.Arr a b)                   = checkNoNegative (nf WHNF a) >> checkPositivity (nf WHNF b)
    checkPositivity (T.Pi _ a (Name _ (Scope b))) = checkNoNegative (nf WHNF a) >> checkPositivity (nf WHNF b)
    checkPositivity _                             = return ()
    
    checkNoNegative :: Monad m => Term a -> EDocM m ()
    checkNoNegative (T.Arr a b)                   = checkNoDataType a >> checkNoNegative (nf WHNF b)
    checkNoNegative (T.Pi _ a (Name _ (Scope b))) = checkNoDataType a >> checkNoNegative (nf WHNF b)
    checkNoNegative _                             = return ()
    
    checkNoDataType :: Monad m => Term a -> EDocM m ()
    checkNoDataType t = when (name `elem` collectDataTypes t) $ throwError
        [emsgLC (argGetPos arg) "Data type is not strictly positive" enull]

typeCheck :: Monad m => Expr -> Maybe (Term String) -> TCM m (Term String, Term String)
typeCheck expr ty = typeCheckCtx Nil expr $ fmap (nf WHNF) ty

typeCheckCtx :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Expr -> Maybe (Term a) -> TCM m (Term a, Term a)
typeCheckCtx ctx expr ty = go ctx expr [] ty
  where
    go :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Expr -> [Expr] -> Maybe (Term a) -> TCM m (Term a, Term a)
    go ctx (Paren _ e) exprs ty = go ctx e exprs ty
    go ctx (E.Lam _ args e) [] (Just ty) = case instantiateType Nil (map unArg args) ty of
        Left i -> let msg = emsgLC (argGetPos $ args !! i) "" $
                            pretty "Expected type:" <+> prettyOpen ctx ty $$
                            pretty "But lambda expression has pi type"
                  in throwError [msg]
        Right (TermInCtx ctx' ty') -> do
            (te, _) <- go (ctx +++ ctx') e [] (Just ty')
            return (T.Lam $ Name (map unArg args) $ toScope $ abstractTermInCtx ctx' te, ty)
    go _ e@E.Lam{} _ _ = throwError [inferErrorMsg (getPos e) "the argument"]
    go ctx (E.App e1 e2) exprs ty = go ctx e1 (e2:exprs) ty
    go ctx (E.Var x) exprs mty = do
        let var = unArg x
            lc = argGetPos x
        (te,ty) <- case lookupIndex (var `elemIndex`) ctx of
            Just r  -> return r
            Nothing -> do
                mt <- lift $ getEntry var $ case mty of
                    Just (DataType d _) -> Just d
                    _                   -> Nothing
                case mt of
                    [FunctionE te ty]           -> return (fmap (liftBase ctx) te, fmap (liftBase ctx) ty)
                    [DataTypeE ty]              -> return (DataType var []       , fmap (liftBase ctx) ty)
                    [ConstructorE i (Left ty)]  -> return (T.Con i  var []       , fmap (liftBase ctx) ty)
                    [ConstructorE i (Right ty)] -> case mty of
                        Just (DataType _ params) -> return (T.Con i var [], ty >>= \v -> case v of
                            B i -> reverse params !! i
                            F a -> return $ liftBase ctx a)
                        _ -> throwError [emsgLC lc ("Cannot infer parameters of data constructor " ++ show var) enull]
                    [] -> throwError [notInScope lc "" var]
                    _  -> throwError [inferErrorMsg lc $ show var]
        (tes,ty') <- typeCheckApps exprs [] ty
        case mty of
            Just ety -> actExpType ctx ty' ety lc
            Nothing  -> return ()
        return (apps te tes, ty')
      where
        typeCheckApps [] [] ty = return ([],ty)
        typeCheckApps es is (T.Pi _ _ (Name [] b)) = typeCheckApps es [] $ instantiate (reverse is !!) b
        typeCheckApps [] is (T.Pi fl a (Name ns (Scope b))) =
            return ([], T.Pi fl a $ Name ns $ Scope $ b >>= \v -> return $ case v of
                B i | i >= length ns -> F $ reverse is !! (i - length ns)
                _ -> v)
        typeCheckApps (e:es) is (T.Pi fl a (Name (_:ns) b)) = do
            (r , _) <- go ctx e [] $ Just (nf WHNF a)
            (rs, t) <- typeCheckApps es (r:is) $ T.Pi fl a (Name ns b)
            return (r:rs, t)
        typeCheckApps (e:es) [] (T.Arr a b) = do
            (r , _) <- go ctx e [] $ Just (nf WHNF a)
            (rs, t) <- typeCheckApps es [] b
            return (r:rs, t)
        typeCheckApps _ _ ty = throwError
            [emsgLC (argGetPos x) "" $ pretty "Expected pi type" $$
                                       pretty "Actual type:" <+> prettyOpen ctx ty]
    go ctx (E.Pi [] e) [] Nothing = go ctx e [] Nothing
    go ctx expr@(E.Pi (PiTele _ e1 e2 : tvs) e) [] Nothing = do
        args <- exprToVars e1
        (r1, t1) <- go ctx e2 [] Nothing
        let vars = map unArg args
            ctx' = Snoc ctx (reverse vars) r1
        (r2, t2) <- go ctx' (E.Pi tvs e) [] Nothing
        t <- checkUniverses ctx ctx' e2 (E.Pi tvs e) t1 t2
        return (T.Pi (null tvs) r1 $ Name vars $ toScope r2, t)
    go ctx (E.Arr e1 e2) [] Nothing = do
        (r1,t1) <- go ctx e1 [] Nothing
        (r2,t2) <- go ctx e2 [] Nothing
        t <- checkUniverses ctx ctx e1 e2 t1 t2
        return (T.Arr r1 r2, t)
    go _ (E.Universe (U (_,u))) [] Nothing =
        let l = parseLevel u
        in return $ (T.Universe l, T.Universe $ Level $ level l + 1)
    go ctx e [] (Just ty) = do
        (r, t) <- go ctx e [] Nothing
        actExpType ctx t ty (getPos e)
        return (r, t)
    go _ e _ _ = throwError [emsgLC (getPos e) "A type is applied to arguments" enull]
    
    actExpType :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Term a -> Term a -> (Int,Int) -> EDocM m ()
    actExpType ctx act exp lc = unless (nf NF act `lessOrEqual` nf NF exp) $
        throwError [emsgLC lc "" $ pretty "Expected type:" <+> prettyOpen ctx exp $$
                                   pretty "Actual type:"   <+> prettyOpen ctx act]
