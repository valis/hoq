{-# LANGUAGE GADTs #-}

module TypeChecking.Context where

import Control.Monad

import Syntax.Scope

data Ctx s f b a where
    Nil  :: Ctx s f b b
    Snoc :: Ctx s f b a -> s -> f a -> Ctx s f b (Scoped a)

(+++) :: Ctx s f a b -> Ctx s f b c -> Ctx s f a c
ctx +++ Nil = ctx
ctx +++ Snoc ctx' s t = Snoc (ctx +++ ctx') s t

lookupCtx :: (Monad g, Functor f, Eq s) => s -> Ctx s f b a -> Maybe (g a, f a)
lookupCtx _ Nil = Nothing
lookupCtx s (Snoc ctx s' t) = if s == s'
    then Just (return Bound, fmap Free t)
    else fmap (\(te, ty) -> (liftM Free te, fmap Free ty)) (lookupCtx s ctx)

close :: Monad f => Ctx b g b a -> f a -> f b
close Nil            t = t
close (Snoc ctx s _) t = close ctx $ t >>= \v -> return $ case v of
    Bound  -> liftBase ctx s
    Free a -> a

liftBase :: Ctx s f b a -> b -> a
liftBase Nil = id
liftBase (Snoc ctx _ _) = Free . liftBase ctx

liftCtx :: Functor f => Ctx s f b a -> Ctx s f (Scoped b) (Scoped a)
liftCtx Nil = Nil
liftCtx (Snoc ctx s t) = Snoc (liftCtx ctx) s (fmap Free t)

abstractTermInCtx :: Ctx s g b a -> f a -> Scope s f b
abstractTermInCtx ctx term = go ctx (ScopeTerm term)
  where
    go :: Ctx s g b a -> Scope s f a -> Scope s f b
    go Nil t = t
    go (Snoc ctx s _) t = go ctx (Scope s t)
