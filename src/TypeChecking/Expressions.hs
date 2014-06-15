{-# LANGUAGE FlexibleContexts #-}

module TypeChecking.Expressions where

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
