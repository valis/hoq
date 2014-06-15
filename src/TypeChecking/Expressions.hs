{-# LANGUAGE FlexibleContexts #-}

module TypeChecking.Expressions where

import Data.List

import qualified Syntax.Expr as E
import Syntax.Term
import Syntax.ErrorDoc
import TypeChecking.Monad

notInScope :: Show a => (Int,Int) -> String -> a -> EMsg f
notInScope lc s a = emsgLC lc ("Not in scope: " ++ (if null s then "" else s ++ " ") ++ show a) enull

inferErrorMsg :: (Int,Int) -> EMsg Term
inferErrorMsg lc = emsgLC  lc "Cannot infer type of the argument" enull

prettyOpen :: Pretty a Term => [String] -> Term (Var Int a) -> EDoc Term
prettyOpen vars term = epretty $ fmap pretty $ term >>= \v -> return $ case v of
    B i -> Left (vars !! i)
    F a -> Right a

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

checkUniverses :: (Pretty a Term, Monad m) => [String] -> E.Expr -> E.Expr
    -> Term (Var Int a) -> Term (Var Int a) -> EDocM m (Term b)
checkUniverses _ _ _ (Universe u1) (Universe u2) = return $ Universe (max u1 u2)
checkUniverses ctx e1 e2 t1 t2 = throwError $ msg e1 t1 ++ msg e2 t2
  where
    msg _ (Universe _) = []
    msg e t = [emsgLC (E.getPos e) "" $ pretty "Expected type: Type" $$
                                        pretty "Actual type:" <+> prettyOpen ctx t]

fromVar :: Var a b -> b
fromVar (B _) = error "fromVar"
fromVar (F b) = b
