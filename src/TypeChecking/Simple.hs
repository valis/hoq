module TypeChecking.Simple
    ( typeCheck
    , typeCheckDefs
    ) where

import Control.Monad
import Control.Monad
import Data.List

import Syntax.Expr
import qualified Syntax.Term as T
import Syntax.ErrorDoc
import TypeChecking.Definitions
import TypeChecking.Expressions
import TypeChecking.Monad

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
typeCheck expr ty = liftM (\(te,ty) -> (fmap fromVar te, fmap fromVar ty)) $ go [] expr $ fmap (fmap T.F) ty
  where
    go :: Monad m => [(String, T.Term (T.Var Int String))] -> Expr -> Maybe (T.Term (T.Var Int String))
        -> TCM m (T.Term (T.Var Int String), T.Term (T.Var Int String))
    go ctx (Paren _ e) ty = go ctx e ty
    go ctx (Lam _ args e) (Just ty@(T.Pi fl a b)) = do
        let vars = map unArg args
        (r, t) <- go (reverse (map (\v -> (v, a)) vars) ++ ctx) e $ Just (T.instantiateVars b)
        return (T.Lam $ T.abstractVars vars r, ty)
    go ctx e@Lam{} (Just ty) =
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen (fmap fst ctx) ty $$
                                         pretty "But lambda expression has pi type"
        in throwError [msg]
    go ctx e (Just ty) = do
        (r, t) <- go ctx e Nothing
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen (fmap fst ctx) ty $$
                                         pretty "Actual type:"   <+> prettyOpen (fmap fst ctx) t
        if t `T.lessOrEqual` ty
            then return (r, t)
            else throwError [msg]
    go ctx (Pi [] e) Nothing = go ctx e Nothing
    go ctx expr@(Pi (PiTele _ e1 e2 : tvs) e) Nothing = case exprToVars e1 of
        Left lc    -> throwError [emsgLC lc "Expected a list of identifiers" enull]
        Right args -> do
            let vars = map unArg args
            (r1, t1) <- go ctx e2 Nothing
            (r2, t2) <- go (map (\v -> (v, r1)) vars ++ ctx) (Pi tvs e) Nothing
            case checkUniverses (fmap fst ctx) e2 (Pi tvs e) t1 t2 of
                Right t   -> return (T.Pi (null tvs) r1 (T.abstractVars vars r2), t)
                Left errs -> throwError errs
    go ctx (App e1 e2) Nothing = do
        (r1, t1) <- go ctx e1 Nothing
        case t1 of
            T.Pi fl a b -> do
                (r2, _) <- go ctx e2 (Just a)
                return (T.App r1 r2, either (T.Pi fl a) id $ T.instantiateNames1 r2 b)
            _ -> let msg = emsgLC (getPos e1) "" $ pretty "Expected pi type" $$
                                                   pretty "Actual type:" <+> prettyOpen (fmap fst ctx) t1
                 in throwError [msg]
    go _ e@Lam{} Nothing = throwError [inferErrorMsg (getPos e)]
    go ctx (Arr e1 e2) Nothing = do
        (r1,t1) <- go ctx e1 Nothing
        (r2,t2) <- go ctx e2 Nothing
        case checkUniverses (fmap fst ctx) e1 e2 t1 t2 of
            Right t   -> return (T.Arr r1 r2, t)
            Left errs -> throwError errs
    go ctx (Var x) Nothing =
        let v = unArg x in
        case lookupIndex v ctx of
            Just (i,t) -> return (T.Var (T.B i), t) -- TODO
            Nothing    -> do
                mt <- lift (getEntry v)
                case mt of
                    Just (te,ty) -> return (fmap T.F (T.Var v), fmap T.F ty)
                    Nothing      -> throwError [notInScope (argGetPos x) "" v]
    go _ (Universe (U (_,u))) Nothing = let l = parseLevel u
                                        in return $ (T.Universe l, T.Universe $ T.Level $ T.level l + 1)
