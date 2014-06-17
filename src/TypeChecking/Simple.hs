module TypeChecking.Simple
    ( typeCheck
    , typeCheckDefs
    ) where

import Control.Monad
import Data.List

import Syntax.Expr
import qualified Syntax.Term as T
import Syntax.ErrorDoc
import Syntax.Context
import TypeChecking.Definitions
import TypeChecking.Expressions
import TypeChecking.Monad
import Normalization

typeCheckDefs :: Monad m => [Def] -> TCM m ()
typeCheckDefs defs = splitDefs defs >>= mapM_ (\t -> typeCheckPDef t `catchError` warn)

typeCheckPDef :: Monad m => PDef -> TCM m ()
typeCheckPDef (PDefSyn name expr) = do
    (term, ty) <- typeCheck expr Nothing
    lift $ addDef name (T.FunSyn name term) ty
typeCheckPDef (PDefCases name ty cases) = do
    (ty, _) <- typeCheck ty Nothing
    names <- mapM (uncurry $ funsToTerm ty) cases
    lift $ addDefRec name (T.FunCall name names) ty
  where
    funsToTerm :: Monad m => T.Term String -> [ParPat] -> Expr -> TCM m (T.Names T.RTPattern T.Term String)
    funsToTerm ty pats expr = do
        pats' <- mapM parPatToPattern pats
        let list = toListPat (T.RTPattern 0 pats') (Pattern (error "typeCheckPDef") pats)
        (term, _) <- typeCheck expr $ Just (nf WHNF ty)
        return $ T.Name pats' $ T.abstract (`elemIndex` list) term
typeCheckPDef (PDefData name params cons) = lift $ do
    addDef name (T.DataType name) (T.Universe T.NoLevel)
    forM_ (zip cons [0..]) $ \((con,teles),i) -> do
        addDef con (T.Con i con []) (T.Universe T.NoLevel) -- TODO

typeCheck :: Monad m => Expr -> Maybe (T.Term String) -> TCM m (T.Term String, T.Term String)
typeCheck expr ty = typeCheckCtx Nil expr $ fmap (nf WHNF) ty

typeCheckCtx :: (Monad m, Eq a) => Ctx Int [String] T.Term String a -> Expr -> Maybe (T.Term a) -> TCM m (T.Term a, T.Term a)
typeCheckCtx ctx (Paren _ e) ty = typeCheckCtx ctx e ty
typeCheckCtx ctx (Lam _ args e) (Just ty) = case instantiateType Nil (map unArg args) ty of
    Left i -> let msg = emsgLC (argGetPos $ args !! i) "" $
                        pretty "Expected type:" <+> prettyOpen ctx ty $$
                        pretty "But lambda expression has pi type"
              in throwError [msg]
    Right (TermInCtx ctx' ty') -> do
        (te, _) <- typeCheckCtx (ctx +++ ctx') e (Just ty')
        return (T.Lam $ T.Name (map unArg args) $ T.toScope $ abstractTermInCtx (TermInCtx ctx' te), ty)
typeCheckCtx ctx e (Just ty) = do
    (r, t) <- typeCheckCtx ctx e Nothing
    let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen ctx ty $$
                                     pretty "Actual type:"   <+> prettyOpen ctx t
    if nf NF t `T.lessOrEqual` nf NF ty
        then return (r, t)
        else throwError [msg]
typeCheckCtx ctx (Pi [] e) Nothing = typeCheckCtx ctx e Nothing
typeCheckCtx ctx expr@(Pi (PiTele _ e1 e2 : tvs) e) Nothing = do
    args <- exprToVars e1
    (r1, t1) <- typeCheckCtx ctx e2 Nothing
    let vars = map unArg args
        ctx' = Snoc ctx (reverse vars) r1
    (r2, t2) <- typeCheckCtx ctx' (Pi tvs e) Nothing
    t <- checkUniverses ctx ctx' e2 (Pi tvs e) t1 t2
    return (T.Pi (null tvs) r1 $ T.Name vars $ T.toScope r2, t)
typeCheckCtx ctx (App e1 e2) Nothing = do
    (r1, t1) <- typeCheckCtx ctx e1 Nothing
    case t1 of
        T.Pi fl a b -> do
            (r2, _) <- typeCheckCtx ctx e2 $ Just (nf WHNF a)
            return (T.App r1 r2, either (T.Pi fl a) id $ T.instantiateNames1 r2 b)
        T.Arr a b -> do
            (r2, _) <- typeCheckCtx ctx e2 $ Just (nf WHNF a)
            return (T.App r1 r2, b)
        _ -> let msg = emsgLC (getPos e1) "" $ pretty "Expected pi type" $$
                                               pretty "Actual type:" <+> prettyOpen ctx t1
             in throwError [msg]
typeCheckCtx _ e@Lam{} Nothing = throwError [inferErrorMsg (getPos e)]
typeCheckCtx ctx (Arr e1 e2) Nothing = do
    (r1,t1) <- typeCheckCtx ctx e1 Nothing
    (r2,t2) <- typeCheckCtx ctx e2 Nothing
    t <- checkUniverses ctx ctx e1 e2 t1 t2
    return (T.Arr r1 r2, t)
typeCheckCtx ctx (Var x) Nothing =
    let v = unArg x in
    case lookupIndex (v `elemIndex`) ctx of
        Just r  -> return r
        Nothing -> do
            mt <- lift (getEntry v)
            case mt of
                Just (te,ty) -> return (T.Var $ liftBase ctx v, fmap (liftBase ctx) ty)
                Nothing      -> throwError [notInScope (argGetPos x) "" v]
typeCheckCtx _ (Universe (U (_,u))) Nothing = let l = parseLevel u
                                    in return $ (T.Universe l, T.Universe $ T.Level $ T.level l + 1)
