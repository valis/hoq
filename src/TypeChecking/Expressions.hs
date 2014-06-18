{-# LANGUAGE FlexibleContexts #-}

module TypeChecking.Expressions
    ( notInScope, inferErrorMsg
    , prettyOpen, parseLevel
    , fixTerm
    , exprToVars, checkUniverses
    , instantiateType, typeCheckPat
    ) where

import Control.Monad
import Data.List

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

fixTerm :: (Monad f, Eq a) => a -> f a -> f a
fixTerm a t = t >>= \a' -> if a == a' then fixTerm a t else return a'

prettyOpen :: (Pretty b f, Monad f) => Ctx Int [b] f b a -> f a -> EDoc f
prettyOpen ctx term = epretty $ liftM pretty $ close (!!) ctx term

parseLevel :: String -> Level
parseLevel "Type" = NoLevel
parseLevel ('T':'y':'p':'e':s) = Level (read s)
parseLevel s = error $ "parseLevel: " ++ s

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

instantiateType :: Eq a => Ctx Int [String] Term b a -> [String] -> Term a -> Either Int (TermInCtx Int [String] Term b)
instantiateType ctx [] ty = Right (TermInCtx ctx ty)
instantiateType ctx (v:vs) (T.Arr a b) = either (Left . succ) Right $ instantiateType (Snoc ctx [v] a) vs $ nf WHNF (fmap F b)
instantiateType ctx vs (T.Pi fl a (Name ns b)) = case splitLists vs ns of
    Less _ ns'  -> Right $ TermInCtx (Snoc ctx vs a) $ T.Pi fl (fmap F a) $ Name ns' $ Scope $ unscope b >>= \v -> case v of
        B i -> let l = length ns'
               in if i < l then return (B i)
                           else return $ F $ T.Var $ B (i - l)
        F t -> fmap (F . T.Var . F) t
    Equal       -> Right $ TermInCtx (Snoc ctx vs a) (fromScope b)
    Greater vs1 vs2 -> either (Left . (+ length vs1)) Right $ instantiateType (Snoc ctx vs1 a) vs2 $ nf WHNF (fromScope b)
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

typeCheckPat :: (Monad m, Eq a) => Ctx Int [String] Term b a -> ParPat -> Term a -> TCM m (TermInCtx Int [String] Term b)
typeCheckPat = undefined
