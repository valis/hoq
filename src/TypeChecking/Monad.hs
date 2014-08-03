module TypeChecking.Monad
    ( EDocM, ScopeM, TCM, runTCM
    , addFunctionCheck, addDataTypeCheck, addConstructorCheck
    , module TypeChecking.Monad.Warn
    , module TypeChecking.Monad.Scope
    , lift
    ) where

import Data.Void
import Control.Monad
import Control.Monad.Trans(lift)

import TypeChecking.Monad.Warn
import TypeChecking.Monad.Scope
import Syntax
import Semantics
import Semantics.Value
import Syntax.ErrorDoc

type EDocM = WarnT [EMsg (Term Syntax)]
type ScopeM = ScopeT (Term Semantics Void) (Type Semantics Void)
    (Scope String (Term Semantics) Void) (Scope String (Term Semantics) Void, Level)
type TCM m = EDocM (ScopeM m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runScopeT . runWarnT

multipleDeclaration :: (Int,Int) -> String -> EMsg f
multipleDeclaration pos var = emsgLC pos ("Multiple declarations of " ++ show var) enull

addFunctionCheck :: Monad m => PIdent -> Term Semantics Void -> Type Semantics Void -> TCM m ()
addFunctionCheck (PIdent pos var) te ty = do
    mr <- lift (getEntry var Nothing)
    case mr of
        [] -> lift (addFunction var te ty)
        _  -> warn [multipleDeclaration pos var]

addDataTypeCheck :: Monad m => PIdent -> Type Semantics Void -> Int -> TCM m ()
addDataTypeCheck (PIdent pos var) ty b = do
    mr <- lift (getEntry var Nothing)
    case mr of
        FunctionE{} : _ -> warn [multipleDeclaration pos var]
        DataTypeE{} : _ -> warn [multipleDeclaration pos var]
        _               -> lift (addDataType var ty b)

addConstructorCheck :: Monad m => PIdent -> String -> Int
    -> Scope String (Term Semantics) Void -> Scope String (Term Semantics) Void -> Level -> TCM m ()
addConstructorCheck (PIdent pos var) dt n te ty lvl = do
    mr <- lift $ getEntry var (Just dt)
    case mr of
        FunctionE{}     : _ -> warn [multipleDeclaration pos var]
        ConstructorE{}  : _ -> warn [multipleDeclaration pos var]
        _                   -> lift $ addConstructor var dt n te (ty,lvl)
