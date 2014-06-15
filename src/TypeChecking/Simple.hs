module TypeChecking.Simple
    ( typeCheck
    , typeCheckDefs
    ) where

import Control.Monad
import Data.List

import Syntax.Expr
import qualified Syntax.Term as T
import Syntax.ErrorDoc
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
typeCheck expr ty = liftM (\(te,ty) -> (fmap fromVar te, fmap fromVar ty)) $ go [] expr $ fmap (nf WHNF . fmap T.F) ty
  where
    go :: Monad m => [([String], T.Term (T.Var Int String))] -> Expr -> Maybe (T.Term (T.Var Int String))
        -> TCM m (T.Term (T.Var Int String), T.Term (T.Var Int String))
    go ctx (Paren _ e) ty = go ctx e ty
    go ctx (Lam _ args e) (Just ty) = do
        (ctx',ty') <- collectCtx args ctx ty
        (te, _) <- go ctx' e $ Just (nf WHNF ty')
        return (T.Lam $ T.abstractVars (map unArg args) te, ty)
    go ctx e (Just ty) = do
        (r, t) <- go ctx e Nothing
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen (concat $ map fst ctx) ty $$
                                         pretty "Actual type:"   <+> prettyOpen (concat $ map fst ctx) t
        if t `T.lessOrEqual` ty
            then return (r, t)
            else throwError [msg]
    go ctx (Pi [] e) Nothing = go ctx e Nothing
    go ctx expr@(Pi (PiTele _ e1 e2 : tvs) e) Nothing = case exprToVars e1 of
        Left lc    -> throwError [emsgLC lc "Expected a list of identifiers" enull]
        Right args -> do
            let vars = map unArg args
            (r1, t1) <- go ctx e2 Nothing
            (r2, t2) <- go ((reverse vars, r1) : ctx) (Pi tvs e) Nothing
            t <- checkUniverses (concat $ map fst ctx) e2 (Pi tvs e) t1 t2
            return (T.Pi (null tvs) r1 (T.abstractVars vars r2), t)
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
                                                   pretty "Actual type:" <+> prettyOpen (concat $ map fst ctx) t1
                 in throwError [msg]
    go _ e@Lam{} Nothing = throwError [inferErrorMsg (getPos e)]
    go ctx (Arr e1 e2) Nothing = do
        (r1,t1) <- go ctx e1 Nothing
        (r2,t2) <- go ctx e2 Nothing
        t <- checkUniverses (concat $ map fst ctx) e1 e2 t1 t2
        return (T.Arr r1 r2, t)
    go ctx (Var x) Nothing =
        let v = unArg x in
        case lookupIndex v ctx of
            Just (i,t) -> return (T.Var (T.B i), t)
            Nothing    -> do
                mt <- lift (getEntry v)
                case mt of
                    Just (te,ty) -> return (fmap T.F (T.Var v), fmap T.F ty)
                    Nothing      -> throwError [notInScope (argGetPos x) "" v]
    go _ (Universe (U (_,u))) Nothing = let l = parseLevel u
                                        in return $ (T.Universe l, T.Universe $ T.Level $ T.level l + 1)

-- Calculations with De Bruijn indices
-- There is a more type safe way to do this, but it involves GADTs and looks too complicated
lookupIndex :: Eq a => a -> [([a], T.Term (T.Var Int b))] -> Maybe (Int, T.Term (T.Var Int b))
lookupIndex _ [] = Nothing
lookupIndex a ((a',b):r) = case a `elemIndex` a' of
    Just i  -> Just (i, fmap (varPlus $ l - i) b)
    Nothing -> fmap (\(i, b') -> (i + l, fmap (varPlus l) b')) (lookupIndex a r)
  where
    l = length a'
    varPlus m (T.B i) = T.B (i + m)
    varPlus _ (T.F a) = T.F a

type Ctx = [([String], T.Term (T.Var Int String))]

collectCtx :: Monad m => [Arg] -> Ctx -> T.Term (T.Var Int String) -> EDocM m (Ctx, T.Term (T.Var Int String))
collectCtx args ctx (T.Pi fl a b@(T.Name ns _)) = case splitLists args ns of
    Less _ _        -> return ((reverse $ map unArg args, a) : ctx, T.Pi fl a $ T.instantiateSomeVars (length args) b)
    Equal           -> return ((reverse $ map unArg args, a) : ctx, T.instantiateVars b)
    Greater as1 as2 -> collectCtx as2 ((reverse $ map unArg as1, a) : ctx) $ nf WHNF (T.instantiateVars b)
collectCtx args ctx (T.Arr a b) = case args of
    []        -> error "collectCtx"
    [arg]     -> return (([unArg arg], a) : ctx, b)
    arg:args' -> collectCtx args' (([unArg arg], a) : ctx) (nf WHNF b)
collectCtx args ctx ty = 
    let msg = emsgLC (argGetPos $ head args) "" $
            pretty "Expected type:" <+> prettyOpen (concat $ fmap fst ctx) ty $$
            pretty "But lambda expression has pi type"
    in throwError [msg]

data Cmp a b = Less [b] [b] | Equal | Greater [a] [a]

splitLists :: [a] -> [b] -> Cmp a b
splitLists [] []         = Equal
splitLists [] bs         = Less [] bs
splitLists as []         = Greater [] as
splitLists (a:as) (b:bs) = case splitLists as bs of
    Less bs1 bs2    -> Less (b:bs1) bs2
    Equal           -> Equal
    Greater as1 as2 -> Greater (a:as1) as2
