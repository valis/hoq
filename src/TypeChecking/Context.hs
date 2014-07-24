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

lookupCtx :: (Monad g, Functor f) => (s -> b -> Bool) -> (b -> p) -> a -> Ctx s p f b a -> Either (b, Maybe (g a, f a)) (p, f a)
lookupCtx cmp f a ctx = case maybeToBase a ctx of
    Left b -> Left (b, go cmp f b ctx)
    Right r -> Right r
  where
    maybeToBase :: Functor f => a -> Ctx s p f b a -> Either b (p, f a)
    maybeToBase b Nil = Left b
    maybeToBase a (Snoc ctx _ t) = case a of
        Bound p -> Right (p, fmap Free t)
        Free a' -> fmap (fmap $ fmap Free) (maybeToBase a' ctx)
    
    go :: (Monad g, Functor f) => (s -> b -> Bool) -> (b -> p) -> b -> Ctx s p f b a -> Maybe (g a, f a)
    go _ _ b Nil = Nothing
    go cmp f b (Snoc ctx s t) = if cmp s b
        then Just (return $ Bound (f b), fmap Free t)
        else fmap (\(te, ty) -> (liftM Free te, fmap Free ty)) (go cmp f b ctx)

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

toBase :: Ctx s p f b a -> a -> Either p b
toBase Nil b = Right b
toBase Snoc{} (Bound p) = Left p
toBase (Snoc ctx _ _) (Free a) = toBase ctx a

abstractTermInCtx :: Ctx s p g b a -> f a -> Scope s p f b
abstractTermInCtx ctx term = go ctx (ScopeTerm term)
  where
    go :: Ctx s p g b a -> Scope s p f a -> Scope s p f b
    go Nil t = t
    go (Snoc ctx s _) t = go ctx (Scope s t)
