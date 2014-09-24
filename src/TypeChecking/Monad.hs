module TypeChecking.Monad
    ( EDocM, TCM, runTCM
    , addFunctionCheck, addDataTypeCheck
    , addConstructorCheck, addFieldCheck
    , module TypeChecking.Monad.Warn
    , module TypeChecking.Monad.Scope
    , lift
    ) where

import Control.Monad
import Control.Monad.Trans(lift)

import TypeChecking.Expressions.Utils
import TypeChecking.Monad.Warn
import TypeChecking.Monad.Scope
import Syntax hiding (Clause)
import Semantics
import Semantics.Value
import Semantics.Pattern
import Syntax.ErrorDoc

type EDocM = WarnT [Error]
type TCM m = EDocM (ScopeT m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runScopeT . runWarnT

multipleDeclaration :: Posn -> Name -> Error
multipleDeclaration pos var = Error Other $ emsgLC pos ("Multiple declarations of " ++ show (nameToPrefix var)) enull

addFunctionCheck :: Monad m => PName -> SEval -> Closed (Type Semantics) -> TCM m ID
addFunctionCheck (pos, var) e ty = do
    mr <- lift (getEntry var Nothing)
    if null mr then lift (addFunction var e ty) else throwError [multipleDeclaration pos var]

addDataTypeCheck :: Monad m => PName -> Int -> Closed (Type Semantics) -> TCM m ID
addDataTypeCheck (pos, var) n ty = do
    mf <- lift (getFunction var)
    md <- lift (getDataType var)
    if null mf && null md then lift (addDataType var n ty) else throwError [multipleDeclaration pos var]

addConstructorCheck :: Monad m => PName -> (ID, Name) -> Int -> [ClauseInCtx] -> [[ClauseInCtx]] -> Closed (Type Semantics) -> TCM m ()
addConstructorCheck (pos, var) dt i e es ty = do
    mf <- lift (getFunction var)
    mc <- lift $ getConstructor var $ Just (fst dt, [])
    if null mf && null mc then lift (addConstructor var dt i e es ty) else warn [multipleDeclaration pos var]

addFieldCheck :: Monad m => PIdent -> ID -> Int -> SEval -> Closed (Type Semantics) -> TCM m ()
addFieldCheck (PIdent pos fn) dtID ind e ty = do
    mind <- lift (getField fn dtID)
    case mind of
        Nothing -> lift (addField fn dtID ind e ty)
        Just{} -> warn [multipleDeclaration pos $ Ident fn]
