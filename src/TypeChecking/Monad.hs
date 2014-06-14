module TypeChecking.Monad
    ( EDocM, TCM, runTCM
    , module TypeChecking.Monad.Warn
    , module TypeChecking.Monad.Scope
    , lift
    ) where

import Control.Monad
import Control.Monad.Trans(lift)

import TypeChecking.Monad.Warn
import TypeChecking.Monad.Scope
import Syntax.Term
import Syntax.ErrorDoc

type EDocM = WarnT [EMsg Term]
type TCM m = EDocM (ScopeT Term m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runScopeT . runWarnT
