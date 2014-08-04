module Syntax.Term
    ( Term(..)
    , cterm, bapps
    , module Syntax.Scope
    ) where

import Data.Foldable
import Data.Traversable
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Control.Applicative
import Control.Monad

import Syntax.Scope

data Term p a
    = Var a
    | Apply p [Term p a]
    | Lambda (Scope1 (Term p) a)

instance Functor  (Term p) where fmap = fmapDefault
instance Foldable (Term p) where foldMap = foldMapDefault
instance Bifunctor  Term where bimap = bimapDefault
instance Bifoldable Term where bifoldMap = bifoldMapDefault
instance Traversable (Term p) where traverse = bitraverse pure

instance Bitraversable Term where
    bitraverse _ g (Var a) = Var <$> g a
    bitraverse f g (Apply p ts) = Apply <$> f p <*> traverse (bitraverse f g) ts
    bitraverse f g (Lambda (Scope1 t)) = Lambda . Scope1 <$> bitraverse f (traverse g) t

instance Applicative (Term p) where
    pure  = Var
    (<*>) = ap

instance Monad (Term p) where
    return           = Var
    Var a      >>= k = k a
    Apply p ts >>= k = Apply p $ map (>>= k) ts
    Lambda s   >>= k = Lambda (s >>>= k)

cterm :: p -> Term p a
cterm p = Apply p []

bapps :: Term s a -> [Term s a] -> Term s a
bapps (Lambda (Scope1 t)) (t1:ts) = bapps (instantiate1 t1 t) ts
bapps t _ = t
