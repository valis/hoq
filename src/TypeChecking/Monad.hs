module TypeChecking.Monad
    ( EDocM, TCM, runTCM
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
type TCM m = EDocM (ScopeT m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runScopeT . runWarnT

multipleDeclaration :: Posn -> String -> EMsg f
multipleDeclaration pos var = emsgLC pos ("Multiple declarations of " ++ show var) enull

addFunctionCheck :: Monad m => PIdent -> SEval -> Type Semantics Void -> TCM m ID
addFunctionCheck (PIdent pos var) e ty = do
    mr <- lift (getEntry var Nothing)
    if null mr then lift (addFunction var e ty) else throwError [multipleDeclaration pos var]

addDataTypeCheck :: Monad m => PIdent -> Int -> Type Semantics Void -> TCM m ID
addDataTypeCheck (PIdent pos var) n ty = do
    mf <- lift (getFunction var)
    md <- lift (getDataType var)
    if null mf && null md then lift (addDataType var n ty) else throwError [multipleDeclaration pos var]

addConstructorCheck :: Monad m => PIdent -> ID -> Int -> Int -> SEval -> Type Semantics Void -> TCM m ()
addConstructorCheck (PIdent pos var) dt i n e ty = do
    mf <- lift (getFunction var)
    mc <- lift $ getConstructor var (Just dt)
    if null mf && null mc then lift (addConstructor var dt i n e ty) else warn [multipleDeclaration pos var]
