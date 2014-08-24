module TypeChecking.Definitions
    ( typeCheckDefs
    ) where

import Control.Monad.Fix
import Data.Void

import Syntax
import Semantics.Value
import Syntax.ErrorDoc
import TypeChecking.Expressions
import TypeChecking.Expressions.Utils
import TypeChecking.Definitions.Records
import TypeChecking.Definitions.DataTypes
import TypeChecking.Definitions.Functions
import TypeChecking.Monad

typeCheckDefs :: MonadFix m => [Def] -> TCM m ()
typeCheckDefs [] = return ()
typeCheckDefs (DefImport{} : defs) = typeCheckDefs defs
typeCheckDefs (DefFixity{} : defs) = typeCheckDefs defs
typeCheckDefs (DefType p@(pos, name) ty : defs) = case span (theSameAs name) defs of
    ([],_) -> do
        warn [Error Other $ emsgLC pos ("Missing a realization of function " ++ show (nameToString name)) enull]
        typeCheckDefs defs
    (defs1,defs2) -> do
        typeCheckFunction p ty (map (\d -> case d of
            DefFun (pos, _) pats expr -> (pos, pats, expr)
            _ -> error "typeCheckDefs") defs1)
            `catchError` \errs -> warn errs >> return ()
        typeCheckDefs defs2
typeCheckDefs (DefFun p@(pos, name) [] (Just expr) : defs) = do
    (term, ty) <- typeCheck expr Nothing
    addFunctionCheck p (SynEval $ closed term) $ Closed (vacuous ty)
    typeCheckDefs defs
typeCheckDefs (DefFun (pos, name) [] Nothing : defs) = do
    warn [Error Other $ emsgLC pos "Expected right hand side" enull]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefFun (pos, name) _ _ : defs) = do
    warn [inferErrorMsg pos "the argument"]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefData dt ty cons conds : defs) = do
    typeCheckDataType dt ty cons conds
    typeCheckDefs defs
typeCheckDefs (DefRecord name params mcon fields conds : defs) = do
    typeCheckRecord name params mcon fields conds
    typeCheckDefs defs

theSameAs :: Name -> Def -> Bool
theSameAs name (DefFun (_, name') _ _) = name == name'
theSameAs _ _ = False
