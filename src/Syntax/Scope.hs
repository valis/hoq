{-# LANGUAGE RankNTypes, ExistentialQuantification #-}

module Syntax.Scope where

import Prelude.Extras
import Control.Monad
import Control.Applicative
import Data.Monoid
import Data.Foldable
import Data.Traversable

newtype Closed f = Closed (forall a. f a)
data SomeEq f = forall a. Eq a => SomeEq (f a)

data Scoped a = Free a | Bound deriving Eq

instance Functor Scoped where
    fmap _ Bound    = Bound
    fmap f (Free a) = Free (f a)

instance Foldable Scoped where
    foldMap _ Bound    = mempty
    foldMap f (Free a) = f a

instance Traversable Scoped where
    traverse _ Bound    = pure Bound
    traverse f (Free a) = Free <$> f a

instance Applicative Scoped where
    pure              = Free
    Bound  <*> _      = Bound
    _      <*> Bound  = Bound
    Free f <*> Free a = Free (f a)

class MonadF t where
    (>>>=) :: Monad f => t f a -> (a -> f b) -> t f b

data Scope1 s f a = Scope1 s (f (Scoped a))

instance (Eq1 f, Eq a) => Eq (Scope1 s f a) where
    Scope1 _ t1 == Scope1 _ t2 = t1 ==# t2

instance Functor f => Functor (Scope1 s f) where
    fmap f (Scope1 s t) = Scope1 s $ fmap (fmap f) t

instance Foldable f => Foldable (Scope1 s f) where
    foldMap f (Scope1 _ t) = foldMap (foldMap f) t

instance Traversable f => Traversable (Scope1 s f) where
    traverse f (Scope1 s t) = Scope1 s <$> traverse (traverse f) t

instance MonadF (Scope1 s) where
    Scope1 s t >>>= k = Scope1 s $ t >>= \v -> case v of
        Bound  -> return Bound
        Free a -> liftM Free (k a)

instantiate1 :: Monad f => f a -> f (Scoped a) -> f a
instantiate1 s t = t >>= \v -> case v of
    Bound  -> s
    Free a -> return a

data Scope s f a = ScopeTerm (f a) | Scope s (Scope s f (Scoped a))

instance Functor f => Functor (Scope s f) where
    fmap f (ScopeTerm t) = ScopeTerm (fmap f t)
    fmap f (Scope s   t) = Scope s $ fmap (fmap f) t

instance Foldable f => Foldable (Scope s f) where
    foldMap f (ScopeTerm t) = foldMap f t
    foldMap f (Scope _   t) = foldMap (foldMap f) t

instance Traversable f => Traversable (Scope s f) where
    traverse f (ScopeTerm t) = ScopeTerm <$> traverse f t
    traverse f (Scope s   t) = Scope s   <$> traverse (traverse f) t

instance MonadF (Scope s) where
    ScopeTerm t >>>= k = ScopeTerm (t >>=  k)
    Scope s   t >>>= k = Scope s $ t >>>= \v -> case v of
        Bound  -> return Bound
        Free a -> liftM Free (k a)

instantiateScope :: Monad f => f a -> Scope s f (Scoped a) -> Scope s f a
instantiateScope t s = s >>>= \v -> case v of
    Bound  -> t
    Free a -> return a

instantiate :: Monad f => [f a] -> Scope s f a -> f a
instantiate t (ScopeTerm s) = s
instantiate [] _ = error "instantiate"
instantiate (t:ts) (Scope _ s) = instantiate ts (instantiateScope t s)
