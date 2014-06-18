module TypeChecking.Monad
    ( EDocM, TCM, runTCM
    , checkDef, addDefCheck, addDefRecCheck
    , module TypeChecking.Monad.Warn
    , module TypeChecking.Monad.Scope
    , lift
    ) where

import Control.Monad
import Control.Monad.Trans(lift)

import TypeChecking.Monad.Warn
import TypeChecking.Monad.Scope
import Syntax.Term
import Syntax.Expr
import Syntax.ErrorDoc

type EDocM = WarnT [EMsg Term]
type TCM m = EDocM (ScopeT Term m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runScopeT . runWarnT

checkDef :: Monad m => Arg -> TCM m ()
checkDef arg = do
    let var = unArg arg
    mr <- lift (getEntry var)
    case mr of
        Nothing -> return ()
        Just _  -> throwError [emsgLC (argGetPos arg) ("Multiple declarations of " ++ show var) enull]

addDefCheck :: Monad m => Arg -> Term String -> Term String -> TCM m ()
addDefCheck arg te ty = do
    checkDef arg
    lift $ addDef (unArg arg) te ty

addDefRecCheck :: Monad m => Arg -> Term String -> Term String -> TCM m ()
addDefRecCheck arg te ty = do
    checkDef arg
    lift $ addDefRec (unArg arg) te ty
