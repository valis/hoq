module TypeChecking.Definitions
    ( typeCheckDefs
    ) where

import Control.Monad.Fix

import Syntax
import Syntax.ErrorDoc
import TypeChecking.Expressions
import TypeChecking.Definitions.DataTypes
import TypeChecking.Definitions.Functions
import TypeChecking.Monad

typeCheckDefs :: MonadFix m => [Def] -> TCM m ()
typeCheckDefs [] = return ()
typeCheckDefs (DefImport{} : defs) = typeCheckDefs defs
typeCheckDefs (DefType p@(PIdent pos name) ty : defs) =
    case span (theSameAs name) defs of
        ([],_) -> do
            warn [emsgLC pos ("Missing a realization of function " ++ show name) enull]
            typeCheckDefs defs
        (defs1,defs2) -> do
            typeCheckFunction p ty (map (\d -> case d of
                DefFun (PIdent pos _) pats expr -> (pos, pats, expr)
                _ -> error "typeCheckDefs") defs1)
                `catchError` \errs -> warn errs >> return ()
            typeCheckDefs defs2
typeCheckDefs (DefFun p@(PIdent pos name) [] (Just expr) : defs) = do
    (term, ty) <- typeCheck expr Nothing
    addFunctionCheck p (FunSyn () name $ closed term) ty
    typeCheckDefs defs
typeCheckDefs (DefFun (PIdent pos name) [] Nothing : defs) = do
    warn [emsgLC pos "Expected right hand side" enull]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefFun (PIdent pos name) _ _ : defs) = do
    warn [inferErrorMsg pos "the argument"]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefData dt ty cons conds : defs) = do
    typeCheckDataType dt ty cons conds
    typeCheckDefs defs

theSameAs :: String -> Def -> Bool
theSameAs name (DefFun (PIdent _ name') _ _) = name == name'
theSameAs _ _ = False
