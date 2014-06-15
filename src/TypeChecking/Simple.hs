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
        (term, _) <- typeCheck expr (Just ty)
        return $ T.Name pats' $ T.abstract (`elemIndex` list) term
typeCheckPDef (PDefData name params cons) = lift $ do
    addDef name (T.DataType name) (T.Universe T.NoLevel)
    forM_ (zip cons [0..]) $ \(Con (PIdent (_,con)) teles, i) -> addDef con (T.Con i con []) (T.Universe T.NoLevel) -- TODO

typeCheck :: Monad m => Expr -> Maybe (T.Term String) -> TCM m (T.Term String, T.Term String)
typeCheck expr ty = go Nil expr $ fmap (nf WHNF) ty
  where
    go :: (Monad m, Eq a) => Ctx Int [String] T.Term String a -> Expr -> Maybe (T.Term a) -> TCM m (T.Term a, T.Term a)
    go ctx (Paren _ e) ty = go ctx e ty
    go ctx (Lam _ [arg] e) (Just ty@(T.Pi _ a (T.Name [_] b))) = do
        (te, _) <- go (Snoc ctx [unArg arg] a) e $ Just $ nf WHNF (T.fromScope b)
        return (T.Lam $ T.Name [unArg arg] $ T.toScope te, ty)
    go ctx (Lam _ [arg] e) (Just ty@(T.Pi fl a (T.Name ns (T.Scope b)))) = do
        (te, _) <- go (Snoc ctx [unArg arg] a) e $ Just $
            T.Pi fl (fmap T.F a) $ T.Name (tail ns) $ T.Scope $ b >>= \v -> case v of
                T.B i | i == length ns - 1 -> T.Var $ T.F $ T.Var (T.B 0)
                      | otherwise          -> T.Var (T.B i)
                T.F t -> fmap (T.F . T.Var . T.F) t
        return (T.Lam $ T.Name [unArg arg] $ T.toScope te, ty)
    go ctx (Lam _ [arg] e) (Just ty@(T.Arr a b)) = do
        (te, _) <- go (Snoc ctx [unArg arg] a) e $ Just $ nf WHNF (fmap T.F b)
        return (T.Lam $ T.Name [unArg arg] $ T.toScope te, ty)
    go ctx (Lam _ [arg] _) (Just ty) =
        let msg = emsgLC (argGetPos arg) "" $
                pretty "Expected type:" <+> prettyOpen ctx ty $$
                pretty "But lambda expression has pi type"
        in throwError [msg]
    go ctx (Lam _ [] e) (Just ty) = go ctx e (Just ty)
    go ctx (Lam p (arg:args) e) (Just ty) = go ctx (Lam p [arg] $ Lam p args e) (Just ty)
    go ctx e (Just ty) = do
        (r, t) <- go ctx e Nothing
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen ctx ty $$
                                         pretty "Actual type:"   <+> prettyOpen ctx t
        if t `T.lessOrEqual` ty
            then return (r, t)
            else throwError [msg]
    go ctx (Pi [] e) Nothing = go ctx e Nothing
    go ctx expr@(Pi (PiTele _ e1 e2 : tvs) e) Nothing = case exprToVars e1 of
        Left lc    -> throwError [emsgLC lc "Expected a list of identifiers" enull]
        Right args -> do
            (r1, t1) <- go ctx e2 Nothing
            let vars = map unArg args
                ctx' = Snoc ctx (reverse vars) r1
            (r2, t2) <- go ctx' (Pi tvs e) Nothing
            t <- checkUniverses ctx ctx' e2 (Pi tvs e) t1 t2
            return (T.Pi (null tvs) r1 $ T.Name vars $ T.toScope r2, t)
    go ctx (App e1 e2) Nothing = do
        (r1, t1) <- go ctx e1 Nothing
        case t1 of
            T.Pi fl a b -> do
                (r2, _) <- go ctx e2 $ Just (nf WHNF a)
                return (T.App r1 r2, either (T.Pi fl a) id $ T.instantiateNames1 r2 b)
            T.Arr a b -> do
                (r2, _) <- go ctx e2 $ Just (nf WHNF a)
                return (T.App r1 r2, b)
            _ -> let msg = emsgLC (getPos e1) "" $ pretty "Expected pi type" $$
                                                   pretty "Actual type:" <+> prettyOpen ctx t1
                 in throwError [msg]
    go _ e@Lam{} Nothing = throwError [inferErrorMsg (getPos e)]
    go ctx (Arr e1 e2) Nothing = do
        (r1,t1) <- go ctx e1 Nothing
        (r2,t2) <- go ctx e2 Nothing
        t <- checkUniverses ctx ctx e1 e2 t1 t2
        return (T.Arr r1 r2, t)
    go ctx (Var x) Nothing =
        let v = unArg x in
        case lookupIndex (v `elemIndex`) ctx of
            Just r  -> return r
            Nothing -> do
                mt <- lift (getEntry v)
                case mt of
                    Just (te,ty) -> return (T.Var $ liftBase ctx v, fmap (liftBase ctx) ty)
                    Nothing      -> throwError [notInScope (argGetPos x) "" v]
    go _ (Universe (U (_,u))) Nothing = let l = parseLevel u
                                        in return $ (T.Universe l, T.Universe $ T.Level $ T.level l + 1)
