module Syntax.ExprToTerm where

import Data.Maybe
import Data.List

import Syntax.Term
import qualified Syntax.Expr as E

bindEitherMaybe :: Either a b -> (b -> Maybe c) -> Maybe c
bindEitherMaybe Left{} _ = Nothing
bindEitherMaybe (Right b) k = k b

exprToTerm :: E.Expr -> Term (Either String String)
exprToTerm (E.Lam _ args e) =
    let vars = map E.unArg args
    in Lam $ Name vars $ abstract (\x -> x `bindEitherMaybe` \v -> v `elemIndex` vars) (exprToTerm e)
exprToTerm (E.Arr e1 e2) = Arr (exprToTerm e1) (exprToTerm e2)
exprToTerm (E.Pi [] e) = exprToTerm e
exprToTerm (E.Pi (E.TypedVar _ e1 e2 : tvs) e) = Pi (null tvs) (exprToTerm e2) $ case exprToVars e1 of
    Left p -> Name [] $ Scope $ Var $ F $ Var $ Left $ "error at " ++ show p
    Right args ->
        let vars = map E.unArg args
        in Name vars $ abstract (\x -> x `bindEitherMaybe` \v -> v `elemIndex` vars) $ exprToTerm (E.Pi tvs e)
exprToTerm (E.App e1 e2) = App (exprToTerm e1) (exprToTerm e2)
exprToTerm (E.Var x) = Var $ Right (E.unArg x)
exprToTerm (E.Universe (E.U (_,u))) = Universe (parseLevel u)
exprToTerm (E.Paren _ e) = exprToTerm e

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
