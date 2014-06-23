{-# LANGUAGE FlexibleContexts #-}

module TypeChecking.Expressions
    ( typeCheck, typeCheckCtx
    , notInScope, inferErrorMsg
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
checkUniverses ctx1 ctx2 e1 e2 t1 t2 = throwError $ msg ctx1 e1 t1 ++ msg ctx2 e2 t2
  where
    msg _ _ (T.Universe _) = []
    msg ctx e t = [emsgLC (getPos e) "" $ pretty "Expected type: Type" $$
                                            pretty "Actual type:" <+> prettyOpen ctx t]

reverseTerm :: Int -> Term (Var Int a) -> Term (Var Int a)
reverseTerm l = fmap $ \v -> case v of
    B i -> B (l - 1 - i)
    F a -> F a

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
        (tes,ty') <- typeCheckApps exprs [] ty
        case (mty, ty') of
            (Nothing, _)  -> return ()
            (Just (DataType edt _), DataType adt []) -> unless (edt == adt) $
                throwError [emsgLC lc "" $ pretty ("Expected data type: " ++ edt) $$
                                           pretty ("Actual data type: " ++ adt)]
            (Just ety, _) -> actExpType ctx ty' ety lc
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
      where
        parseLevel :: String -> Level
        parseLevel "Type" = NoLevel
        parseLevel ('T':'y':'p':'e':s) = Level (read s)
        parseLevel s = error $ "parseLevel: " ++ s
    go ctx e [] (Just ty) = do
        (r, t) <- go ctx e [] Nothing
        actExpType ctx t ty (getPos e)
        return (r, t)
    go _ e _ _ = throwError [emsgLC (getPos e) "A type is applied to arguments" enull]
    
    actExpType :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Term a -> Term a -> (Int,Int) -> EDocM m ()
    actExpType ctx act exp lc = unless (nf NF act `lessOrEqual` nf NF exp) $
        throwError [emsgLC lc "" $ pretty "Expected type:" <+> prettyOpen ctx exp $$
                                   pretty "Actual type:"   <+> prettyOpen ctx act]

instantiateType :: Eq a => Ctx Int [String] Term b a -> [String] -> Term a -> Either Int (TermInCtx Int [String] Term b)
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
