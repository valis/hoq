{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances, FlexibleInstances, MultiParamTypeClasses #-}

module Evaluation.Monad
    ( EvalT, runEvalT
    , WarnT, warn, runWarnT
    , addDef, addDefRec, substInTerm
    , getEntry
    ) where

import Control.Monad
import Control.Monad.State
import Control.Monad.Error.Class
import Control.Applicative
import Data.Monoid hiding ((<>))

newtype WarnT w m a = WarnT { runWarnT :: m (w, Maybe a) }

instance Functor m => Functor (WarnT w m) where
    fmap f (WarnT m) = WarnT $ fmap (\(w, ma) -> (w, fmap f ma)) m

instance (Monoid w, Applicative m) => Applicative (WarnT w m) where
    pure a = WarnT $ pure (mempty, Just a)
    WarnT f <*> WarnT a = WarnT $ (\(w1, mf) (w2, ma) -> (w1 `mappend` w2, mf <*> ma)) <$> f <*> a

instance (Monoid w, Monad m) => Monad (WarnT w m) where
    return a      = WarnT $ return (mempty, Just a)
    WarnT m >>= k = WarnT $ m >>= \(w, ma) -> case ma of
        Nothing -> return (w, Nothing)
        Just a  -> runWarnT (k a)

instance (Monoid w, Monad m) => MonadError w (WarnT w m) where
    throwError w = WarnT $ return (w, Nothing)
    catchError (WarnT m) h = WarnT $ m >>= \(w, ma) -> case ma of
        Nothing -> runWarnT (h w)
        Just _  -> return (w, ma)

instance Monoid w => MonadTrans (WarnT w) where
    lift m = WarnT $ liftM (\a -> (mempty, Just a)) m

instance (Monoid w, MonadIO m) => MonadIO (WarnT w m) where
    liftIO m = WarnT $ liftM (\a -> (mempty, Just a)) (liftIO m)

warn :: Monad m => w -> WarnT w m ()
warn w = WarnT $ return (w, Just ())

newtype EvalT v f m a = EvalT { unEvalT :: StateT [(v, f v)] m a }
    deriving (Functor,Monad,MonadTrans,MonadIO,Applicative)

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
