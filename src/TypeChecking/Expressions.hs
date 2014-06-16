{-# LANGUAGE FlexibleContexts #-}

module TypeChecking.Expressions
    ( notInScope, inferErrorMsg
    , prettyOpen, parseLevel
    , exprToVars, checkUniverses
    , instantiateType
    ) where

import Data.List

import qualified Syntax.Expr as E
import Syntax.Term
import Syntax.ErrorDoc
import Syntax.Context
import TypeChecking.Monad

notInScope :: Show a => (Int,Int) -> String -> a -> EMsg f
notInScope lc s a = emsgLC lc ("Not in scope: " ++ (if null s then "" else s ++ " ") ++ show a) enull

inferErrorMsg :: (Int,Int) -> EMsg Term
inferErrorMsg lc = emsgLC  lc "Cannot infer type of the argument" enull

prettyOpen :: Pretty b Term => Ctx Int [b] Term b a -> Term a -> EDoc Term
prettyOpen ctx term = epretty $ fmap pretty $ close (!!) ctx term

parseLevel :: String -> Level
parseLevel "Type" = NoLevel
parseLevel ('T':'y':'p':'e':s) = Level (read s)
parseLevel s = error $ "parseLevel: " ++ s

exprToVars :: E.Expr -> Either (Int,Int) [E.Arg]
exprToVars = fmap reverse . go
  where
    go (E.Var a) = Right [a]
    go (E.App as (E.Var a)) = fmap (a:) (go as)
    go e = Left (E.getPos e)

checkUniverses :: (Pretty b Term, Monad m) => Ctx Int [b] Term b a1 -> Ctx Int [b] Term b a2
    -> E.Expr -> E.Expr -> Term a1 -> Term a2 -> EDocM m (Term a3)
checkUniverses _ _ _ _ (Universe u1) (Universe u2) = return $ Universe (max u1 u2)
checkUniverses ctx1 ctx2 e1 e2 t1 t2 = throwError $ msg ctx1 e1 t1 ++ msg ctx2 e2 t2
  where
    msg _ _ (Universe _) = []
    msg ctx e t = [emsgLC (E.getPos e) "" $ pretty "Expected type: Type" $$
                                            pretty "Actual type:" <+> prettyOpen ctx t]

instantiateType :: Ctx Int [String] Term b a -> [String] -> Term a -> Either Int (TermInCtx Int [String] Term b)
instantiateType ctx [] ty = Right (TermInCtx ctx ty)
instantiateType ctx (v:vs) (Arr a b) = either (Left . succ) Right $ instantiateType (Snoc ctx [v] a) vs (fmap F b)
instantiateType ctx vs (Pi fl a (Name ns b)) = case splitLists vs ns of
    Less _ ns'  -> Right $ TermInCtx (Snoc ctx vs a) $ Pi fl (fmap F a) $ Name ns' $ Scope $ unscope b >>= \v -> case v of
        B i -> let l = length ns'
               in if i < l then return (B i)
                           else return $ F $ Var $ B (i - l)
        F t -> fmap (F . Var . F) t
    Equal       -> Right $ TermInCtx (Snoc ctx vs a) (fromScope b)
    Greater vs1 vs2 -> either (Left . (+ length vs1)) Right $ instantiateType (Snoc ctx vs1 a) vs2 (fromScope b)
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
