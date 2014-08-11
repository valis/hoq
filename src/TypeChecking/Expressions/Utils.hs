module TypeChecking.Expressions.Utils where

import Data.Bifunctor
import Data.Void

import Syntax
import Syntax.ErrorDoc
import Semantics
import Semantics.Value
import TypeChecking.Context
import TypeChecking.Monad

notInScope :: Show a => Posn -> String -> a -> EMsg f
notInScope pos s a = emsgLC pos ("Not in scope: " ++ (if null s then "" else s ++ " ") ++ show a) enull

inferErrorMsg :: Posn -> String -> EMsg f
inferErrorMsg pos s = emsgLC pos ("Cannot infer type of " ++ s) enull

inferParamsErrorMsg :: Show a => Posn -> a -> EMsg f
inferParamsErrorMsg pos d = emsgLC pos ("Cannot infer parameters of data constructor " ++ show d) enull

argsErrorMsg :: Posn -> String -> EMsg f
argsErrorMsg pos s = emsgLC pos (s ++ " is applied to arguments") enull

expectedArgErrorMsg :: Show a => Posn -> a -> EMsg f
expectedArgErrorMsg lc d = emsgLC lc ("Expected an argument to " ++ show d) enull

prettyOpen :: Ctx String (Type Semantics) Void a -> Term Semantics a -> EDoc (Term Syntax)
prettyOpen ctx term = epretty $ fmap (pretty . either id absurd) $ close ctx (bimap syntax Right term)

checkIsType :: Monad m => Ctx String (Type Semantics) Void a -> Posn -> Term Semantics a -> EDocM m Level
checkIsType _ _ (Apply (Semantics _ (Universe lvl)) _) = return lvl
checkIsType ctx pos t = throwError [emsgLC pos "" $ pretty "Expected type: Type"
                                                 $$ pretty "Actual type:" <+> prettyOpen ctx t]

termPos :: Term (Posn, s) a -> Posn
termPos (Apply (pos, _) _) = pos
termPos _ = error "termPos"
