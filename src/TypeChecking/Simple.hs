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

typeCheckDefs :: MonadFix m => [Def] -> TCM m ()
typeCheckDefs defs = splitDefs defs >>= mapM_ (\t -> typeCheckPDef t `catchError` warn)

typeCheckPDef :: MonadFix m => PDef -> TCM m ()
typeCheckPDef (PDefSyn arg expr) = do
    (term, ty) <- typeCheck expr Nothing
    addFunctionCheck arg (FunSyn (unArg arg) term) ty
typeCheckPDef (PDefCases arg ty cases) = do
    (ty, _) <- typeCheck ty Nothing
    mfix $ \te -> do
        addFunctionCheck arg te ty
        names <- mapM (uncurry $ funsToTerm ty) cases
        return $ FunCall (unArg arg) names
    return ()
  where
    funsToTerm :: Monad m => Term String -> [ParPat] -> Expr -> TCM m (Names RTPattern Term String)
    funsToTerm ty pats expr = do
        pats' <- mapM parPatToPattern pats
        let list = toListPat (RTPattern 0 pats') (E.Pattern (error "typeCheckPDef") pats)
        (term, _) <- typeCheck expr $ Just (nf WHNF ty)
        return $ Name pats' $ abstract (`elemIndex` list) term
typeCheckPDef (PDefData arg params cons) = do
    let name = unArg arg
    (CtxFrom ctx, dataType, _) <- checkTele Nil params (T.Universe NoLevel)
    addDataTypeCheck arg dataType
    lvls <- forM (zip cons [0..]) $ \((con,tele),i) -> do
        (_, conType, conLevel) <- checkTele ctx tele $ fmap (liftBase ctx) dataType
        addConstructorCheck con name i (abstractTermInCtx ctx conType)
        return conLevel
    lift $ deleteDataType name
    lift $ addDataType name $ replaceLevel dataType (maximum lvls)
  where
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

typeCheck :: Monad m => Expr -> Maybe (Term String) -> TCM m (Term String, Term String)
typeCheck expr ty = typeCheckCtx Nil expr $ fmap (nf WHNF) ty

typeCheckCtx :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Expr -> Maybe (Term a) -> TCM m (Term a, Term a)
typeCheckCtx ctx (Paren _ e) ty = typeCheckCtx ctx e ty
typeCheckCtx ctx (E.Lam _ args e) (Just ty) = case instantiateType Nil (map unArg args) ty of
    Left i -> let msg = emsgLC (argGetPos $ args !! i) "" $
                        pretty "Expected type:" <+> prettyOpen ctx ty $$
                        pretty "But lambda expression has pi type"
              in throwError [msg]
    Right (TermInCtx ctx' ty') -> do
        (te, _) <- typeCheckCtx (ctx +++ ctx') e (Just ty')
        return (T.Lam $ Name (map unArg args) $ toScope $ abstractTermInCtx ctx' te, ty)
typeCheckCtx ctx e (Just ty) = do
    (r, t) <- typeCheckCtx ctx e Nothing
    let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen ctx ty $$
                                     pretty "Actual type:"   <+> prettyOpen ctx t
    if nf NF t `lessOrEqual` nf NF ty
        then return (r, t)
        else throwError [msg]
typeCheckCtx ctx (E.Pi [] e) Nothing = typeCheckCtx ctx e Nothing
typeCheckCtx ctx expr@(E.Pi (PiTele _ e1 e2 : tvs) e) Nothing = do
    args <- exprToVars e1
    (r1, t1) <- typeCheckCtx ctx e2 Nothing
    let vars = map unArg args
        ctx' = Snoc ctx (reverse vars) r1
    (r2, t2) <- typeCheckCtx ctx' (E.Pi tvs e) Nothing
    t <- checkUniverses ctx ctx' e2 (E.Pi tvs e) t1 t2
    return (T.Pi (null tvs) r1 $ Name vars $ toScope r2, t)
typeCheckCtx ctx (E.App e1 e2) Nothing = do
    (r1, t1) <- typeCheckCtx ctx e1 Nothing
    case t1 of
        T.Pi fl a b -> do
            (r2, _) <- typeCheckCtx ctx e2 $ Just (nf WHNF a)
            return (T.App r1 r2, either (T.Pi fl a) id $ instantiateNames1 r2 b)
        T.Arr a b -> do
            (r2, _) <- typeCheckCtx ctx e2 $ Just (nf WHNF a)
            return (T.App r1 r2, b)
        _ -> let msg = emsgLC (getPos e1) "" $ pretty "Expected pi type" $$
                                               pretty "Actual type:" <+> prettyOpen ctx t1
             in throwError [msg]
typeCheckCtx _ e@E.Lam{} Nothing = throwError [inferErrorMsg (getPos e) "the argument"]
typeCheckCtx ctx (E.Arr e1 e2) Nothing = do
    (r1,t1) <- typeCheckCtx ctx e1 Nothing
    (r2,t2) <- typeCheckCtx ctx e2 Nothing
    t <- checkUniverses ctx ctx e1 e2 t1 t2
    return (T.Arr r1 r2, t)
typeCheckCtx ctx (E.Var x) Nothing =
    let v = unArg x in
    case lookupIndex (v `elemIndex`) ctx of
        Just r  -> return r
        Nothing -> do
            mt <- lift (getEntry v Nothing)
            case mt of
                Nothing    -> throwError [notInScope (argGetPos x) "" v]
                Just entry ->
                    let (te,ty) = entryToTerm v entry
                    in  return (fmap (liftBase ctx) te, fmap (liftBase ctx) ty)
typeCheckCtx _ (E.Universe (U (_,u))) Nothing = let l = parseLevel u
                                    in return $ (T.Universe l, T.Universe $ Level $ level l + 1)

entryToTerm :: String -> Entry Term -> (Term String, Term String)
entryToTerm _    (FunctionE te ty)   = (te, ty)
entryToTerm name (DataTypeE ty)      = (DataType name, ty)
entryToTerm name (ConstructorE i ty) = (T.Con i name [], error "TODO")
