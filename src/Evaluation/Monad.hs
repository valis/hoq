{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Evaluation.Monad
    ( EvalT, runEvalT
    , Eval, runEval
    , addDef, addDefRec, substInTerm
    , getEntry
    ) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

newtype EvalT v f m a = EvalT { unEval :: StateT [(v, f v)] m a }
    deriving (Functor,Monad,MonadTrans,MonadIO)
type Eval v f = EvalT v f Identity

addDef :: (Eq v, Monad f, Monad m) => v -> f v -> EvalT v f m ()
addDef v t = EvalT $ modify $ \list -> (v, t >>= \v -> maybe (return v) id (lookup v list)) : list

addDefRec :: (Eq v, Monad f, Monad m) => v -> f v -> EvalT v f m ()
addDefRec v t = EvalT $ modify $ \list ->
    let list' = (v, t >>= \v -> maybe (return v) id (lookup v list')) : list
    in list'

substInTerm :: (Eq v, Monad f, Monad m) => f v -> EvalT v f m (f v)
substInTerm t = EvalT $ liftM (\list -> t >>= \v -> maybe (return v) id (lookup v list)) get

getEntry :: (Eq v, Monad m) => v -> EvalT v f m (Maybe (f v))
getEntry v = EvalT $ liftM (lookup v) get

runEvalT :: Monad m => EvalT v f m a -> m a
runEvalT (EvalT f) = evalStateT f []

runEval :: Eval v f a -> a
runEval = runIdentity . runEvalT
