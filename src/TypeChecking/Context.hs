{-# LANGUAGE GADTs #-}

module TypeChecking.Context where

import Control.Monad

import Syntax.Scope

data Ctx s p f b a where
    Nil  :: Ctx s p f b b
    Snoc :: Ctx s p f b a -> s -> f a -> Ctx s p f b (Scoped p a)

(+++) :: Ctx s p f a b -> Ctx s p f b c -> Ctx s p f a c
ctx +++ Nil = ctx
ctx +++ Snoc ctx' s t = Snoc (ctx +++ ctx') s t

lengthCtx :: Ctx s p f b a -> Int
lengthCtx Nil = 0
lengthCtx (Snoc ctx _ _) = lengthCtx ctx + 1

lookupCtx :: Functor f => a -> Ctx s p f b a -> Either b (p, f a)
lookupCtx b Nil = Left b
lookupCtx a (Snoc ctx _ t) = case a of
    Bound p -> Right (p, fmap Free t)
    Free a' -> fmap (fmap $ fmap Free) (lookupCtx a' ctx)

ctxToVars :: Monad g => (s -> p) -> Ctx s p f b a -> [g a]
ctxToVars f = reverse . go f
  where
    go :: Monad g => (s -> p) -> Ctx s p f b a -> [g a]
    go _ Nil = []
    go f (Snoc ctx s _) = return (Bound $ f s) : map (liftM Free) (go f ctx)

close :: Functor f => Ctx c p g b a -> f (Either c a) -> f (Either c b)
close Nil            t = t
close (Snoc ctx s _) t = close ctx $ fmap (\v -> case v of
    Left c          -> Left c
    Right (Bound _) -> Left s
    Right (Free a)  -> Right a) t

liftBase :: Ctx s p f b a -> b -> a
liftBase Nil = id
liftBase (Snoc ctx _ _) = Free . liftBase ctx

toBase :: Ctx s p f b a -> (b -> p) -> a -> p
toBase Nil f a = f a
toBase Snoc{} _ (Bound p) = p
toBase (Snoc ctx _ _) f (Free a) = toBase ctx f a

abstractTermInCtx :: Ctx s p g b a -> f a -> Scope s p f b
abstractTermInCtx ctx term = go ctx (ScopeTerm term)
  where
    go :: Ctx s p g b a -> Scope s p f a -> Scope s p f b
    go Nil t = t
    go (Snoc ctx s _) t = go ctx (Scope s t)

abstractCtxTerm :: (Functor f, Eq a) => p -> (s -> c) -> Ctx s p g c b -> Ctx s p g b a -> f b -> f a
abstractCtxTerm p f ctx ctx' = go p ctx' $ \s a -> liftBase (ctx +++ ctx') (f s) == a
  where
    go :: Functor f => p -> Ctx s p g b a -> (s -> a -> Bool) -> f b -> f a
    go _ Nil _ term = term
    go p (Snoc ctx s _) f term =
        let f' s a = f s (Free a)
        in fmap (\a -> if f' s a then Bound p else Free a) (go p ctx f' term)
