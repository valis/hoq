{-# LANGUAGE GADTs #-}

module TypeChecking.Context where

import Control.Monad

import Syntax.Term

data Ctx s f b a where
    Nil  :: Ctx s f b b
    Snoc :: Ctx s f b a -> s -> f a -> Ctx s f b (Scoped a)

(+++) :: Ctx s f a b -> Ctx s f b c -> Ctx s f a c
ctx +++ Nil = ctx
ctx +++ Snoc ctx' s t = Snoc (ctx +++ ctx') s t

lengthCtx :: Ctx s f b a -> Int
lengthCtx Nil = 0
lengthCtx (Snoc ctx _ _) = lengthCtx ctx + 1

lookupCtx :: (Monad g, Functor f, Eq s) => s -> Ctx s f b a -> Maybe (g a, f a)
lookupCtx _ Nil = Nothing
lookupCtx b (Snoc ctx s t) = if s == b
    then Just (return Bound, fmap Free t)
    else fmap (\(te, ty) -> (liftM Free te, fmap Free ty)) (lookupCtx b ctx)

ctxToVars :: Ctx s f b a -> [a]
ctxToVars = reverse . go
  where
    go :: Ctx s f b a -> [a]
    go Nil = []
    go (Snoc ctx s _) = Bound : map Free (go ctx)

close :: Functor f => Ctx c g b a -> f (Either c a) -> f (Either c b)
close Nil            t = t
close (Snoc ctx s _) t = close ctx $ fmap (\v -> case v of
    Left c          -> Left c
    Right Bound     -> Left s
    Right (Free a)  -> Right a) t

liftBase :: Ctx s f b a -> b -> a
liftBase Nil = id
liftBase (Snoc ctx _ _) = Free . liftBase ctx

toBase :: Ctx s f b a -> a -> Maybe b
toBase Nil b = Just b
toBase Snoc{} Bound = Nothing
toBase (Snoc ctx _ _) (Free a) = toBase ctx a

ctxVars :: Ctx s f b a -> [s]
ctxVars = reverse . go
  where
    go :: Ctx s f b a -> [s]
    go Nil = []
    go (Snoc ctx v _) = v : go ctx

abstractTerm :: Ctx s f b a -> Term p a -> Term p b
abstractTerm Nil term = term
abstractTerm (Snoc ctx v _) term = abstractTerm ctx (Lambda term)
