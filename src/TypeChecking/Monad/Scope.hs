{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecking.Monad.Scope
    ( ScopeT, runScopeT
    , addDef, addDefRec, deleteDef
    , substInTerm, getEntry
    ) where

import Control.Monad
import Control.Monad.State
import Control.Applicative
import Data.List

newtype ScopeT f m a = ScopeT { unScopeT :: StateT [(String, (f String, f String))] m a }
    deriving (Functor,Monad,MonadTrans,MonadIO,Applicative)

modTerm :: Monad f => ((f String, f String) -> f String) -> f String ->  [(String, (f String, f String))] -> f String
modTerm f t list = t >>= \v -> maybe (return v) f (lookup v list)

addDef :: (Monad f, Monad m) => String -> f String -> f String -> ScopeT f m ()
addDef v te ty = ScopeT $ modify $ \list -> (v, (modTerm fst te list, modTerm snd ty list)) : list

addDefRec :: (Monad f, Monad m) => String -> f String -> f String -> ScopeT f m ()
addDefRec v te ty = ScopeT $ modify $ \list ->
    let list' = (v, (modTerm fst te list', modTerm snd ty list)) : list
    in list'

deleteDef :: (Monad f, Monad m) => String -> ScopeT f m ()
deleteDef var = ScopeT $ modify $ deleteBy (\(v1,_) (v2,_) -> v1 == v2) (var, error "")

substInTerm :: (Monad f, Monad m) => f String -> ScopeT f m (f String)
substInTerm t = ScopeT $ liftM (modTerm fst t) get

getEntry :: Monad m => String -> ScopeT f m (Maybe (f String, f String))
getEntry v = ScopeT $ liftM (lookup v) get

runScopeT :: Monad m => ScopeT f m a -> m a
runScopeT (ScopeT f) = evalStateT f []
