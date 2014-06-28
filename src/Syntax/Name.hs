module Syntax.Name
    ( Name(..), Names
    , abstractName, abstractNames
    , instantiateName, instantiateNames
    , instantiateNames1
    , abstractVar, abstractVars
    , instantiateVar, instantiateVars
    , instantiateSomeVars
    ) where

import Prelude.Extras
import Bound
import Data.List
import Data.Maybe
import Control.Monad

data Name n b f a = Name { name :: n, scope :: Scope b f a } deriving Show
type Names n = Name [n] Int

instance (Eq b, Monad f, Eq1 f, Eq a) => Eq (Name n b f a) where
    Name _ s1 == Name _ s2 = s1 == s2

instance Bound (Name n b) where
    Name n (Scope s) >>>= k = Name n $ Scope $ s >>= \v -> case v of
        B b -> return (B b)
        F t -> liftM (F . return) (t >>= k)

instance Functor f => Functor (Name n b f) where
    fmap f (Name n s) = Name n (fmap f s)

type Ctx n = [(n,Int)]

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

instantiateNames1 :: (Eq n, Monad f) => f a -> Names n f a -> Either (Names n f a) (f a)
instantiateNames1 _ (Name [] _)     = error "instantiateNames1"
instantiateNames1 t (Name [_] s)    = Right (instantiate1 t s)
instantiateNames1 t (Name (_:ns) (Scope s)) = Left $ Name ns $ Scope $ s >>= \v -> return $ case v of
    B i | i == length ns -> F t
    _                    -> v

abstractVar :: Monad f => n -> f (Var Int a) -> Name n () f (Var Int a)
abstractVar n t = Name n $ Scope $ t >>= \v -> return $ case v of
    B 0 -> B ()
    B i -> F $ return $ B (i - 1)
    F a -> F $ return (F a)

abstractVars :: Monad f => [n] -> f (Var Int a) -> Names n f (Var Int a)
abstractVars ns t = Name ns $ Scope $ t >>= \v ->
    let l = length ns
    in return $ case v of
        B i | i < l     -> B i
            | otherwise -> F $ return $ B (i - l)
        F a             -> F $ return (F a)

instantiateVar :: Monad f => Name n () f (Var Int a) -> f (Var Int a)
instantiateVar (Name _ (Scope t)) = t >>= \v -> case v of
    B _  -> return (B 0)
    F t' -> t' >>= \v' -> return $ case v' of
        B i -> B (i + 1)
        F a -> F a

instantiateVars :: Monad f => Names n f (Var Int a) -> f (Var Int a)
instantiateVars (Name ns (Scope t)) = t >>= \v -> case v of
    B i  -> return (B i)
    F t' -> t' >>= \v' -> return $ case v' of
        B i -> B (i + length ns)
        F a -> F a

instantiateSomeVars :: Monad f => Int -> Names n f (Var Int a) -> Names n f (Var Int a)
instantiateSomeVars k (Name ns (Scope t)) = Name (drop k ns) $ Scope $ t >>= \v -> return $ case v of
    B i | i < k     -> B i
        | otherwise -> F $ return $ B (i - k)
    F t'            -> F $ t' >>= \v' -> return $ case v' of
                                                B i -> B (i + k)
                                                F a -> F a
