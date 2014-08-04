{-# LANGUAGE RankNTypes #-}

module Syntax.Term
    ( Term(..), Scoped(..)
    , cterm, bapps
    , abstract1, instantiate1
    , Closed(..), closed
    ) where

import Data.Maybe
import Data.Monoid
import Data.Foldable
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Control.Applicative
import Control.Monad

data Term p a
    = Var a
    | Apply p [Term p a]
    | Lambda (Term p (Scoped a))

instance Functor  (Term p) where fmap = fmapDefault
instance Foldable (Term p) where foldMap = foldMapDefault
instance Bifunctor  Term where bimap = bimapDefault
instance Bifoldable Term where bifoldMap = bifoldMapDefault
instance Traversable (Term p) where traverse = bitraverse pure

instance Bitraversable Term where
    bitraverse _ g (Var a) = Var <$> g a
    bitraverse f g (Apply p ts) = Apply <$> f p <*> traverse (bitraverse f g) ts
    bitraverse f g (Lambda t) = Lambda <$> bitraverse f (traverse g) t

instance Applicative (Term p) where
    pure  = Var
    (<*>) = ap

instance Monad (Term p) where
    return           = Var
    Var a      >>= k = k a
    Apply p ts >>= k = Apply p $ map (>>= k) ts
    Lambda s   >>= k = Lambda $ s >>= \v -> case v of
        Free a -> fmap Free (k a)
        Bound  -> return Bound

cterm :: p -> Term p a
cterm p = Apply p []

bapps :: Term s a -> [Term s a] -> Term s a
bapps (Lambda t) (t1:ts) = bapps (instantiate1 t1 t) ts
bapps t _ = t

newtype Closed f = Closed { open :: forall a. f a }

data Scoped a = Free a | Bound

instance Eq a => Eq (Scoped a) where
    Bound == Bound = True
    Free a == Free a' = a == a'
    _ == _ = False

instance Functor Scoped where
    fmap _ Bound = Bound
    fmap f (Free a)  = Free (f a)

instance Foldable Scoped where
    foldMap _ Bound = mempty
    foldMap f (Free a)  = f a

instance Traversable Scoped where
    traverse _ Bound = pure Bound
    traverse f (Free a)  = Free <$> f a

instance Applicative Scoped where
    pure = Free
    Bound <*> _ = Bound
    _ <*> Bound = Bound
    Free f <*> Free a = Free (f a)

abstract1 :: (Functor f, Eq a) => a -> f a -> f (Scoped a)
abstract1 a = fmap $ \a' -> if a == a' then Bound else Free a'

instantiate1 :: Monad f => f a -> f (Scoped a) -> f a
instantiate1 s t = t >>= \v -> case v of
    Bound   -> s
    Free a  -> return a

closed :: Traversable f => f a -> Closed f
closed t = Closed $ fromJust $ traverse (const Nothing) t
