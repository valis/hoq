{-# LANGUAGE GADTs, RankNTypes #-}

module Syntax.Context where

import Prelude.Extras
import Control.Monad
import Control.Applicative
import Data.Monoid
import Data.Foldable
import Data.Traversable

data Scoped a = Free a | Bound deriving (Show,Eq)

instance Functor Scoped where
    fmap _ Bound    = Bound
    fmap f (Free a) = Free (f a)

instance Foldable Scoped where
    foldMap _ Bound    = mempty
    foldMap f (Free a) = f a

instance Traversable Scoped where
    traverse _ Bound    = pure Bound
    traverse f (Free a) = Free <$> f a

data Ctx s b a where
    Nil  :: Ctx s b b
    Snoc :: Ctx s b a -> s -> Ctx s b (Scoped a)

liftCtx :: Ctx s b a -> Ctx s (Scoped b) (Scoped a)
liftCtx Nil = Nil
liftCtx (Snoc ctx s) = Snoc (liftCtx ctx) s

liftBase :: Ctx s b a -> b -> a
liftBase Nil = id
liftBase (Snoc ctx _) = Free . liftBase ctx

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

instantiate1 :: Monad f => f a -> Scope1 s f a -> f a
instantiate1 s (Scope1 _ t) = t >>= \v -> case v of
    Bound  -> s
    Free a -> return a

data Scope s f b where
    Scope :: Ctx s b a -> f a -> Scope s f b

instance Functor f => Functor (Scope s f) where
    fmap f (Scope ctx t) = go f ctx $ \ctx' g -> Scope ctx' (fmap g t)
      where
        go :: (b -> c) -> Ctx s b a -> (forall d. Ctx s c d -> (a -> d) -> r) -> r
        go f Nil c = c Nil f
        go f (Snoc ctx s) c = go f ctx $ \ctx' f' -> c (Snoc ctx' s) (fmap f')

instance Foldable f => Foldable (Scope s f) where
    foldMap f (Scope ctx t) = go f ctx t
      where
        go :: (Monoid m, Foldable f) => (b -> m) -> Ctx s b a -> f a -> m
        go f Nil t = foldMap f t
        go f (Snoc ctx s) t = go (\v -> case v of
            Bound  -> mempty
            Free a -> f a) (liftCtx ctx) t

instance Traversable f => Traversable (Scope s f) where
    traverse f (Scope ctx t) = go f ctx $ \ctx' f' -> Scope ctx' <$> traverse f' t
      where
        go :: Applicative p => (b -> p c) -> Ctx s b a -> (forall d. Ctx s c d -> (a -> p d) -> r) -> r
        go f Nil c = c Nil f
        go f (Snoc ctx s) c = go f ctx $ \ctx' f' -> c (Snoc ctx' s) $ \v -> case v of
            Bound  -> pure Bound
            Free a -> Free <$> f' a

instance MonadF (Scope s) where
    Scope ctx t >>>= k = go k ctx $ \ctx' k' -> Scope ctx' (t >>= k')
      where
        go :: Monad f => (b -> f c) -> Ctx s b a -> (forall d. Ctx s c d -> (a -> f d) -> r) -> r
        go k Nil c = c Nil k
        go k (Snoc ctx s) c = go k ctx $ \ctx' k' -> c (Snoc ctx' s) $ \v -> case v of
            Bound  -> return Bound
            Free a -> liftM Free (k' a)
