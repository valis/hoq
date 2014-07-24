{-# LANGUAGE RankNTypes #-}

module Syntax.Scope where

import Prelude.Extras
import Control.Monad
import Control.Applicative
import Data.Maybe
import Data.Monoid
import Data.Foldable
import Data.Traversable

newtype Closed f = Closed { open :: forall a. f a }

data Scoped p a = Free a | Bound p

instance Eq a => Eq (Scoped p a) where
    Bound _ == Bound _ = True
    Free a == Free a' = a == a'
    _ == _ = False

instance Functor (Scoped p) where
    fmap _ (Bound p) = Bound p
    fmap f (Free a)  = Free (f a)

instance Foldable (Scoped p) where
    foldMap _ (Bound _) = mempty
    foldMap f (Free a)  = f a

instance Traversable (Scoped p) where
    traverse _ (Bound p) = pure (Bound p)
    traverse f (Free a)  = Free <$> f a

instance Applicative (Scoped p) where
    pure = Free
    Bound p <*> _ = Bound p
    _ <*> Bound p = Bound p
    Free f <*> Free a = Free (f a)

mapScoped :: (p -> p') -> Scoped p a -> Scoped p' a
mapScoped f (Bound p) = Bound (f p)
mapScoped _ (Free a)  = Free a

class MonadF t where
    (>>>=) :: Monad f => t f a -> (a -> f b) -> t f b

data Scope1 s p f a = Scope1 s (f (Scoped p a))

unScope1 :: Scope1 s p f a -> f (Scoped p a)
unScope1 (Scope1 _ t) = t

instance (Eq1 f, Eq a) => Eq (Scope1 s p f a) where
    Scope1 _ t1 == Scope1 _ t2 = t1 ==# t2

instance Functor f => Functor (Scope1 s p f) where
    fmap f (Scope1 s t) = Scope1 s $ fmap (fmap f) t

instance Foldable f => Foldable (Scope1 s p f) where
    foldMap f (Scope1 _ t) = foldMap (foldMap f) t

instance Traversable f => Traversable (Scope1 s p f) where
    traverse f (Scope1 s t) = Scope1 s <$> traverse (traverse f) t

instance MonadF (Scope1 s p) where
    Scope1 s t >>>= k = Scope1 s $ t >>= \v -> case v of
        Bound p -> return (Bound p)
        Free a  -> liftM Free (k a)

abstract1 :: (Functor f, Eq a) => (a -> Maybe p) -> f a -> f (Scoped p a)
abstract1 f = fmap $ \a -> case f a of
    Just p  -> Bound p
    Nothing -> Free a

instantiate1 :: Monad f => f a -> f (Scoped p a) -> f a
instantiate1 s t = t >>= \v -> case v of
    Bound _ -> s
    Free a  -> return a

data Scope s p f a = ScopeTerm (f a) | Scope s (Scope s p f (Scoped p a))

instance (Eq1 f, Eq a) => Eq (Scope s p f a) where
    ScopeTerm t1 == ScopeTerm t2 = t1 ==# t2
    Scope _ t1 == Scope _ t2 = t1 == t2
    _ == _ = False

instance Functor f => Functor (Scope s p f) where
    fmap f (ScopeTerm t) = ScopeTerm (fmap f t)
    fmap f (Scope s   t) = Scope s $ fmap (fmap f) t

instance Foldable f => Foldable (Scope s p f) where
    foldMap f (ScopeTerm t) = foldMap f t
    foldMap f (Scope _   t) = foldMap (foldMap f) t

instance Traversable f => Traversable (Scope s p f) where
    traverse f (ScopeTerm t) = ScopeTerm <$> traverse f t
    traverse f (Scope s   t) = Scope s   <$> traverse (traverse f) t

instance MonadF (Scope s p) where
    ScopeTerm t >>>= k = ScopeTerm (t >>=  k)
    Scope s   t >>>= k = Scope s $ t >>>= \v -> case v of
        Bound p -> return (Bound p)
        Free a  -> liftM Free (k a)

instantiateScope :: Monad f => f a -> Scope s p f (Scoped p a) -> Scope s p f a
instantiateScope t s = s >>>= \v -> case v of
    Bound _ -> t
    Free a  -> return a

instantiate :: Monad f => [f a] -> Scope s p f a -> f a
instantiate t (ScopeTerm s) = s
instantiate [] _ = error "instantiate"
instantiate (t:ts) (Scope _ s) = instantiate ts (instantiateScope t s)

closed :: Traversable f => f a -> Closed f
closed t = Closed $ fromJust $ traverse (const Nothing) t

mapScope :: (s -> t) -> Scope s p f a -> Scope t p f a
mapScope _ (ScopeTerm t) = ScopeTerm t
mapScope f (Scope s t)   = Scope (f s) (mapScope f t)
