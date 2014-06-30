{-# LANGUAGE FlexibleContexts #-}

module TypeChecking.Expressions
    ( typeCheck, typeCheckCtx
    , notInScope, inferErrorMsg, inferParamsErrorMsg
    , prettyOpen, exprToVars
    , checkUniverses, reverseTerm
    ) where

import Control.Monad
import Data.List
import Data.Maybe

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import Syntax.Context
import TypeChecking.Monad
import Normalization

notInScope :: Show a => (Int,Int) -> String -> a -> EMsg f
notInScope lc s a = emsgLC lc ("Not in scope: " ++ (if null s then "" else s ++ " ") ++ show a) enull

inferErrorMsg :: (Int,Int) -> String -> EMsg f
inferErrorMsg lc s = emsgLC lc ("Cannot infer type of " ++ s) enull

inferParamsErrorMsg :: Show a => (Int,Int) -> a -> EMsg f
inferParamsErrorMsg lc d = emsgLC lc ("Cannot infer parameters of data constructor " ++ show d) enull

prettyOpen :: (Pretty b f, Monad f) => Ctx Int [b] f b a -> f a -> EDoc f
prettyOpen ctx term = epretty $ liftM pretty $ close (!!) ctx term

exprToVars :: Monad m => Expr -> EDocM m [Arg]
exprToVars = liftM reverse . go
  where
    go (E.Var a) = return [a]
    go (E.App as (E.Var a)) = liftM (a:) (go as)
    go e = throwError [emsgLC (getPos e) "Expected a list of identifiers" enull]

checkUniverses :: (Pretty b Term, Monad m) => Ctx Int [b] Term b a1 -> Ctx Int [b] Term b a2
    -> Expr -> Expr -> Term a1 -> Term a2 -> EDocM m (Term a3)
checkUniverses _ _ _ _ (T.Universe u1) (T.Universe u2) = return $ T.Universe (max u1 u2)
checkUniverses ctx1 ctx2 e1 e2 t1 t2 = throwError $ checkIsType ctx1 e1 t1 ++ checkIsType ctx2 e2 t2

checkIsType :: Pretty b Term => Ctx Int [b] Term b a -> Expr -> Term a -> [EMsg Term]
checkIsType _ _ (T.Universe _) = []
checkIsType ctx e t = [emsgLC (getPos e) "" $ pretty "Expected type: Type" $$
                                              pretty "Actual type:" <+> prettyOpen ctx t]

reverseTerm :: Int -> Term (Var Int a) -> Term (Var Int a)
reverseTerm l = fmap $ \v -> case v of
    B i -> B (l - 1 - i)
    F a -> F a

typeCheck :: Monad m => Expr -> Maybe (Term String) -> TCM m (Term String, Term String)
typeCheck expr ty = typeCheckCtx Nil expr $ fmap (nf WHNF) ty

typeCheckCtx :: (Monad m, Eq a, Show a) => Ctx Int [String] Term String a -> Expr -> Maybe (Term a) -> TCM m (Term a, Term a)
typeCheckCtx ctx expr ty = go ctx expr [] ty
  where
    go :: (Monad m, Eq a, Show a) => Ctx Int [String] Term String a -> Expr -> [Expr] -> Maybe (Term a) -> TCM m (Term a, Term a)
    go ctx (Paren _ e) exprs ty = go ctx e exprs ty
    go ctx (E.Lam _ args e) [] (Just ty) = case instantiateType Nil (map unArg args) ty of
        Left i -> let msg = emsgLC (argGetPos $ args !! i) "" $
                            pretty "Expected type:" <+> prettyOpen ctx ty $$
                            pretty "But lambda expression has pi type"
                  in throwError [msg]
        Right (TermInCtx ctx' ty') -> do
            (te, _) <- go (ctx +++ ctx') e [] $ Just (nf WHNF ty')
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
                    [FunctionE te ty]                -> return (fmap (liftBase ctx) te , fmap (liftBase ctx) ty)
                    [DataTypeE ty]                   -> return (DataType var []        , fmap (liftBase ctx) ty)
                    [ConstructorE (Left  (con, ty))] -> return (fmap (liftBase ctx) con, fmap (liftBase ctx) ty)
                    [ConstructorE (Right (con, ty))] -> case mty of
                        Just (DataType _ params) ->
                            let liftTerm te = te >>= \v -> case v of
                                    B i -> reverse params !! i
                                    F a -> return (liftBase ctx a)
                            in return (liftTerm con, liftTerm ty)
                        Just ty -> throwError [emsgLC lc "" $ pretty "Expected type:" <+> prettyOpen ctx ty $$
                                                              pretty ("But given data constructor " ++ show var)]
                        Nothing -> throwError [inferParamsErrorMsg lc var]
                    [] -> do
                        cons <- lift (getConstructorDataTypes var)
                        let DataType dataType _ = fromJust mty
                        case cons of
                            []    -> throwError [notInScope lc "" var]
                            [act] -> throwError [emsgLC lc "" $
                                pretty ("Expected data type: " ++ dataType) $$
                                pretty ("Actual data type: " ++ act)]
                            acts -> throwError [emsgLC lc "" $
                                pretty ("Expected data type: " ++ dataType) $$
                                pretty ("Posible data types: " ++ intercalate ", " acts)]
                    _  -> throwError [inferErrorMsg lc $ show var]
        (tes,ty') <- typeCheckApps (argGetPos x) ctx exprs (nf WHNF ty)
        case (mty, ty') of
            (Nothing, _)  -> return ()
            (Just (DataType edt _), DataType adt []) -> unless (edt == adt) $
                throwError [emsgLC lc "" $ pretty ("Expected data type: " ++ edt) $$
                                           pretty ("Actual data type: " ++ adt)]
            (Just ety, _) -> actExpType ctx ty' ety lc
        return (apps te tes, ty')
    go _ (ELeft _)  [] Nothing = return (ICon ILeft, T.Interval)
    go _ e@ELeft{}  _  Nothing = throwError [emsgLC (getPos e) "\"left\" is applied to arguments" enull]
    go _ (ERight _) [] Nothing = return (ICon IRight, T.Interval)
    go _ e@ERight{} _  Nothing = throwError [emsgLC (getPos e) "\"right\" is applied to arguments" enull]
    go ctx e@PathCon{} es _ | length es > 1 = throwError [emsgLC (getPos e) "A path is applied to arguments" enull]
    go ctx e@PathCon{} [] Nothing = throwError [inferErrorMsg (getPos e) "path"]
    go ctx PathCon{} [e] Nothing = throwError [emsgLC (getPos e) "Not implemented yet" enull] -- TODO
{-
        (r,t) <- go ctx e [] Nothing
        case t of
            T.Arr T.Interval t'  -> ...
            T.Pi _ T.Interval t' -> ...
            _                    -> ...
-}
    go ctx e@PathCon{} [] (Just ty) = throwError [emsgLC (getPos e) "Not implemented yet" enull] -- TODO
    go ctx e'@PathCon{} [e] (Just ty) = do
        (mt1,t2,t3) <- case ty of
            T.Path [t1,t2,t3]   -> return (Just t1, t2, t3)
            T.PathImp mt1 t2 t3 -> return (mt1, t2, t3)
            _                   -> throwError [emsgLC (getPos e') "" $ pretty "Expected type:" <+> prettyOpen ctx ty $$
                                                                       pretty "Actual type: Path"]
        (r,t) <- go ctx e [] $ fmap (T.Arr T.Interval) mt1
        let left  = T.App r (ICon ILeft)
            right = T.App r (ICon IRight)
        actExpType ctx (T.PathImp Nothing left right) ty (getPos e')
        return (PCon (Just r), ty)
    go ctx (E.At e1 e2) es Nothing = do
        (r1, t1) <- go ctx e1 [] Nothing
        (r2, _)  <- go ctx e2 [] (Just T.Interval)
        let tcApps a b c = do
                (tes, ty) <- typeCheckApps (getPos e1) ctx es (nf WHNF a)
                return (apps (T.At b c r1 r2) tes, ty)
        case nf WHNF t1 of
            T.Path [a,b,c]         -> tcApps a b c
            T.PathImp (Just a) b c -> tcApps a b c
            T.PathImp Nothing  _ _ -> throwError [emsgLC (getPos e1) "Cannot infer type" enull]
            t1'                    -> throwError [emsgLC (getPos e1) "" $ pretty "Expected type: Path" $$
                                                                          pretty "Actual type:" <+> prettyOpen ctx t1']
    go ctx e@E.Coe{} es Nothing | length es < 4 = throwError [emsgLC (getPos e) "Not implemented yet" enull] -- TODO
    go ctx E.Coe{} (e1:e2:e3:e4:es) Nothing = do
        (r1, _) <- go ctx e1 [] $ Just $ T.Arr T.Interval (T.Universe NoLevel) -- TODO
        (r2, _) <- go ctx e2 [] $ Just T.Interval
        (r3, _) <- go ctx e3 [] $ Just $ nf WHNF (T.App r1 r2)
        (r4, _) <- go ctx e4 [] $ Just T.Interval
        return (T.Coe [r1,r2,r3,r4], T.App r1 r4)
    go ctx e@E.Iso{} es Nothing | length es < 7 = throwError [emsgLC (getPos e) "Not implemented yet" enull] -- TODO
    go ctx E.Iso{} [e1,e2,e3,e4,e5,e6,e7] Nothing = do
        (r1, t1) <- go ctx e1 [] Nothing
        (r2, t2) <- go ctx e2 [] Nothing
        tm <- checkUniverses ctx ctx e1 e2 (nf WHNF t1) (nf WHNF t2)
        (r3, _)  <- go ctx e3 [] $ Just (T.Arr r1 r2)
        (r4, _)  <- go ctx e4 [] $ Just (T.Arr r2 r1)
        (r5, _)  <- go ctx e5 [] $ Just $ T.Pi True r1 $ Name ["x"] $ Scope $
            T.PathImp (Just $ T.Var $ F r1) (T.App (T.Var (F r4)) $ T.App (T.Var (F r3)) $ T.Var $ B 0) (T.Var $ B 0)
        (r6, _)  <- go ctx e6 [] $ Just $ T.Pi True r2 $ Name ["x"] $ Scope $
            T.PathImp (Just $ T.Var $ F r2) (T.App (T.Var (F r3)) $ T.App (T.Var (F r4)) $ T.Var $ B 0) (T.Var $ B 0)
        (r7, _)  <- go ctx e7 [] $ Just T.Interval
        return (T.Iso [r1,r2,r3,r4,r5,r6,r7], tm)
    go ctx e@E.Squeeze{} es Nothing | length es < 2 = throwError [emsgLC (getPos e) "Not implemented yet" enull] -- TODO
    go ctx E.Squeeze{} [e1,e2] Nothing = do
        (r1, _) <- go ctx e1 [] (Just T.Interval)
        (r2, _) <- go ctx e2 [] (Just T.Interval)
        return (T.Squeeze [r1,r2], T.Interval)
    go ctx (E.Pi [] e) [] Nothing = go ctx e [] Nothing
    go ctx expr@(E.Pi (PiTele _ e1 e2 : tvs) e) [] Nothing = do
        args <- exprToVars e1
        (r1, t1) <- go ctx e2 [] Nothing
        let vars = map unArg args
            ctx' = Snoc ctx (reverse vars) r1
        (r2, t2) <- go ctx' (E.Pi tvs e) [] Nothing
        t <- checkUniverses ctx ctx' e2 (E.Pi tvs e) (nf WHNF t1) (nf WHNF t2)
        return (T.Pi (null tvs) r1 $ Name vars $ toScope r2, t)
    go ctx (E.Arr e1 e2) [] Nothing = do
        (r1,t1) <- go ctx e1 [] Nothing
        (r2,t2) <- go ctx e2 [] Nothing
        t <- checkUniverses ctx ctx e1 e2 (nf WHNF t1) (nf WHNF t2)
        return (T.Arr r1 r2, t)
    go _ (E.Universe (U (_,u))) [] Nothing =
        let l = parseLevel u
        in return (T.Universe l, T.Universe $ Level $ level l + 1)
      where
        parseLevel :: String -> Level
        parseLevel "Type" = NoLevel
        parseLevel ('T':'y':'p':'e':s) = Level (read s)
        parseLevel s = error $ "parseLevel: " ++ s
    go _ E.Interval{} [] Nothing = return (T.Interval, T.Universe NoLevel)
    go ctx e@E.Path{} [] Nothing = throwError [inferErrorMsg (getPos e) "Path"]
    go ctx e@E.Path{} [] (Just ty) = throwError [emsgLC (getPos e) "Not implemented yet" enull] -- TODO
    go ctx E.Path{} (e1:es) Nothing | length es < 3 = do
        (r1,t1) <- go ctx e1 [] Nothing
        let r1' = nf WHNF r1
        case (checkIsType ctx e1 t1, es) of
            ([], [])      -> return (T.Path [r1], T.Arr r1 $ T.Arr r1 t1)
            ([], [e2])    -> do
                (r2,_) <- go ctx e2 [] (Just r1')
                return (T.Path [r1,r2], T.Arr r1 t1)
            ([], [e2,e3]) -> do
                (r2,_) <- go ctx e2 [] (Just r1')
                (r3,_) <- go ctx e3 [] (Just r1')
                return (T.Path [r1,r2,r3], t1)
            (errs, _)     -> throwError errs
    go ctx (E.PathImp e1 e2) [] Nothing = do
        (r1,t1) <- go ctx e1 [] Nothing
        (r2,_)  <- go ctx e2 [] $ Just (nf WHNF t1)
        return (T.PathImp (Just t1) r1 r2, T.Universe NoLevel) -- TODO
    go _ e _ Nothing = throwError [emsgLC (getPos e) "A type is applied to arguments" enull]
    go ctx e es (Just ty) = do
        (r, t) <- go ctx e es Nothing
        actExpType ctx t ty (getPos e)
        return (r, ty)
    
    actExpType :: (Monad m, Eq a, Show a) => Ctx Int [String] Term String a -> Term a -> Term a -> (Int,Int) -> EDocM m ()
    actExpType ctx act exp lc =
        let act' = nf NF act
            exp' = nf NF exp
        in unless (act' `lessOrEqual` exp') $
            throwError [emsgLC lc "" $ pretty "Expected type:" <+> prettyOpen ctx exp' $$
                                       pretty "Actual type:"   <+> prettyOpen ctx act']

typeCheckApps :: (Monad m, Eq a, Show a) => (Int,Int) -> Ctx Int [String] Term String a -> [Expr] -> Term a
    -> TCM m ([Term a], Term a)
typeCheckApps lc ctx exprs = go exprs []
  where
    go [] [] ty = return ([],ty)
    go es is (T.Pi _ _ (Name [] b)) = go es [] $ nf WHNF $ instantiate (is !!) b
    go [] is (T.Pi fl a (Name ns (Scope b))) =
        return ([], T.Pi fl a $ Name ns $ Scope $ b >>= \v -> return $ case v of
            B i | i >= length ns -> F $ reverse is !! (i - length ns)
            _ -> v)
    go (e:es) is (T.Pi fl a (Name (_:ns) b)) = do
        (r , _) <- typeCheckCtx ctx e $ Just (nf WHNF a)
        (rs, t) <- go es (r:is) $ T.Pi fl a (Name ns b)
        return (r:rs, t)
    go (e:es) [] (T.Arr a b) = do
        (r , _) <- typeCheckCtx ctx e $ Just (nf WHNF a)
        (rs, t) <- go es [] (nf WHNF b)
        return (r:rs, t)
    go _ _ ty = throwError [emsgLC lc "" $ pretty "Expected pi type" $$
                                           pretty "Actual type:" <+> prettyOpen ctx ty]

instantiateType :: (Eq a, Show a) => Ctx Int [String] Term b a -> [String] -> Term a -> Either Int (TermInCtx Int [String] Term b)
instantiateType ctx [] ty = Right (TermInCtx ctx ty)
instantiateType ctx (v:vs) (T.Arr a b) =
    either (Left . succ) Right $ instantiateType (Snoc ctx [v] a) vs $ nf WHNF (fmap F b)
instantiateType ctx vs (T.Pi fl a (Name ns b)) = case splitLists vs ns of
    Less _ ns'  -> Right $ TermInCtx (Snoc ctx (reverse vs) a) $ T.Pi fl (fmap F a) $
        Name ns' $ Scope $ unscope b >>= \v -> case v of
            B i -> let l = length ns'
                   in if i < l then return (B i)
                               else return $ F $ T.Var $ B (i - l)
            F t -> fmap (F . T.Var . F) t
    Equal       -> Right $ TermInCtx (Snoc ctx (reverse vs) a) (fromScope b)
    Greater vs1 vs2 -> either (Left . (+ length vs1)) Right $
        instantiateType (Snoc ctx (reverse vs1) a) vs2 $ nf WHNF (fromScope b)
instantiateType _ _ _ = Left 0

data Cmp a b = Less [b] [b] | Equal | Greater [a] [a]

splitLists :: [a] -> [b] -> Cmp a b
splitLists [] []         = Equal
splitLists [] bs         = Less [] bs
splitLists as []         = Greater [] as
splitLists (a:as) (b:bs) = case splitLists as bs of
    Less bs1 bs2    -> Less (b:bs1) bs2
    Equal           -> Equal
    Greater as1 as2 -> Greater (a:as1) as2
