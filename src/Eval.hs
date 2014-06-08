{-# LANGUAGE KindSignatures, GeneralizedNewtypeDeriving #-}

module Eval
    ( EvalT, runEvalT
    , Eval, runEval
    , Ref
    , definition, getEntry
    ) where

import Bound
import Control.Monad
import Control.Monad.State
import Control.Monad.Identity

newtype EvalT v d f m a = EvalT { unEval :: StateT [(v, Ref v d f)] m a } deriving (Functor,Monad)
type Eval v d f = EvalT v d f Identity
newtype Ref v d (f :: * -> *) = Ref { unRef :: d f (Either v (Ref v d f)) }

definition :: (Eq v, Bound d, Monad f, Monad m) => v -> d f v -> EvalT v d f m ()
definition v d = EvalT $ modify $ \list -> (v, Ref $ d >>>= \v -> return $ maybe (Left v) Right $ lookup v list) : list

getEntry :: (Eq v, Monad m) => v -> EvalT v d f m (Maybe (d f (Either v (Ref v d f))))
getEntry v = EvalT $ liftM (fmap unRef . lookup v) get

runEvalT :: Monad m => EvalT v d f m a -> m a
runEvalT (EvalT f) = evalStateT f []

runEval :: Eval v d f a -> a
runEval = runIdentity . runEvalT
