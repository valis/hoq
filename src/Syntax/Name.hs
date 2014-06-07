module Syntax.Name
    ( Name(..), Names, names
    , abstractName, abstractNames
    , instantiateName, instantiateNames
    ) where

import Prelude.Extras
import Bound
import Data.List
import Data.Maybe

data Name n b f a = Name { name :: n, scope :: Scope b f a }
type Names n = Name [n] Int

instance (Eq b, Monad f, Eq1 f, Eq a) => Eq (Name n b f a) where
    Name _ s1 == Name _ s2 = s1 == s2

instance Bound (Name n b) where
    Name n s >>>= k = Name n (s >>>= k)

type Ctx n = [(n,Int)]

names :: Names n f a -> [n]
names = name

renameName :: Eq n => n -> Ctx n -> (Ctx n, Maybe Int)
renameName n0 = go
  where
    go [] = ([(n0,0)], Nothing)
    go ((n,c):ns)
        | n == n0 = ((n,c+1):ns, Just c)
        | otherwise =
            let (ns', c') = go ns
            in ((n,c):ns', c')

renameNames :: Eq n => [n] -> Ctx n -> (Ctx n, [Maybe Int])
renameNames [] ctx = (ctx, [])
renameNames (n:ns) ctx =
    let (ctx1, c ) = renameName  n  ctx
        (ctx2, cs) = renameNames ns ctx1
    in  (ctx2, c:cs)

abstractName :: (Monad f, Eq a) => (n -> a) -> n -> f a -> Name n () f a
abstractName f n = Name n . abstract1 (f n)

abstractNames :: (Monad f, Eq a) => (n -> a) -> [n] -> f a -> Names n f a
abstractNames f ns = Name ns . abstract (\a -> listToMaybe $ reverse $ findIndices (\n -> f n == a) ns)

instantiateName :: (Eq n, Monad f) => Ctx n -> (n -> Maybe Int -> a) -> Name n b f a -> (a, Ctx n, f a)
instantiateName ctx f (Name n s) =
    let (ctx', c) = renameName n ctx
        a = f n c
    in (a, ctx', instantiate1 (return a) s)

instantiateNames :: (Eq n, Monad f) => Ctx n -> (n -> Maybe Int -> a) -> Names n f a -> ([a], Ctx n, f a)
instantiateNames ctx f (Name ns s) =
    let (ctx', cs) = renameNames ns ctx
        as = zipWith f ns cs
    in (as, ctx', instantiate (map return as !!) s)
