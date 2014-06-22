{-# LANGUAGE GADTs #-}

module Syntax.Context where

import Bound
import Control.Monad

data Ctx i s f b a where
    Nil  :: Ctx i s f b b
    Snoc :: Ctx i s f b a -> s -> f a -> Ctx i s f b (Var i a)

data CtxFrom i s f a where
    CtxFrom :: Eq b => Ctx i s f a b -> CtxFrom i s f a

data TermInCtx i s f a where
    TermInCtx :: Eq b => Ctx i s f a b -> f b -> TermInCtx i s f a

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

(+++) :: Ctx i s f a b -> Ctx i s f b c -> Ctx i s f a c
ctx +++ Nil = ctx
ctx +++ Snoc ctx' s t = Snoc (ctx +++ ctx') s t

contextNames :: Ctx i s f a b -> [s]
contextNames Nil = []
contextNames (Snoc ctx s _) = s : contextNames ctx

abstractTermInCtx :: Monad f => Ctx Int [s] f a b -> f b -> f (Var Int a)
abstractTermInCtx Nil t = liftM F t
abstractTermInCtx (Snoc ctx s _) t = go (length s) ctx t
  where
    go :: Monad f => Int -> Ctx Int [s] f a b -> f (Var Int b) -> f (Var Int a)
    go _ Nil t = t
    go n (Snoc ctx s _) t = go (n + length s) ctx $ t >>= \v -> return $ case v of
        B i     -> B i
        F (B i) -> B (i + n)
        F (F a) -> F a
