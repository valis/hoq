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

coverageErrorMsg :: Posn -> Maybe [Posn] -> [EMsg f]
coverageErrorMsg pos Nothing = [emsgLC pos "Incomplete pattern matching" enull]
coverageErrorMsg _ (Just uc) = map (\pos -> emsgLC pos "Unreachable clause" enull) uc

prettyOpen :: Ctx String (Type Semantics) Void a -> Term Semantics a -> EDoc (Term Syntax)
prettyOpen ctx term = epretty $ fmap (pretty . either id absurd) $ close ctx (bimap syntax Right term)

checkIsType :: Monad m => Ctx String (Type Semantics) Void a -> Posn -> Term Semantics a -> EDocM m Sort
checkIsType _ _ (Apply (Semantics _ (Universe k)) _) = return k
checkIsType ctx pos t = throwError [emsgLC pos "" $ pretty "Expected type: Type"
                                                 $$ pretty "Actual type:" <+> prettyOpen ctx t]

termPos :: Term (Posn, s) a -> Posn
termPos (Apply (pos, _) _) = pos
termPos _ = error "termPos"
