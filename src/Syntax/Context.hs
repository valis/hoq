{-# LANGUAGE GADTs #-}

module Syntax.Context where

import Bound
import Control.Monad
import Control.Monad.Identity

data Ctx i s f b a where
    Nil  :: Ctx i s f b b
    Snoc :: Ctx i s f b a -> s -> f a -> Ctx i s f b (Var i a)

lookupIndex :: Monad f => (s -> Maybe i) -> Ctx i s f b a -> Maybe (f a, f a)
lookupIndex c Nil = Nothing
lookupIndex c (Snoc ctx s t) = case c s of
    Just i  -> Just (return $ B i, liftM F t)
    Nothing -> fmap (\(te, ty) -> (liftM F te, liftM F ty)) (lookupIndex c ctx)

liftBase :: Ctx i s f b a -> b -> a
liftBase Nil = id
liftBase (Snoc ctx _ _) = F . liftBase ctx

close :: Monad f => (s -> i -> b) -> Ctx i s g b a -> f a -> f b
close c Nil            t = t
close c (Snoc ctx s _) t = close c ctx $ t >>= \v -> return $ case v of
    B i -> liftBase ctx (c s i)
    F a -> a
