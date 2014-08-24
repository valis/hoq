{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Expressions.Telescopes
    ( typeCheckTelescope
    , SomeEq(..)
    , replaceSort
    , findOccurrence
    ) where

import Data.Void
import Data.Bifoldable

import Syntax as S
import Semantics
import Semantics.Value as V
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Expressions.Utils
import Normalization

data SomeEq f = forall a. Eq a => SomeEq (f a)

extendCtx :: (Functor t, Eq a) => [s] -> Ctx s t b a -> t a -> SomeEq (Ctx s t b)
extendCtx [] ctx _ = SomeEq ctx
extendCtx (x:xs) ctx t = extendCtx xs (Snoc ctx x t) (fmap Free t)

typeCheckTelescope :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> [Tele] -> Term Semantics a
    -> TCM m (SomeEq (Ctx String (Type Semantics) Void), Type Semantics a)
typeCheckTelescope ctx [] term = return (SomeEq ctx, Type term $ Set NoLevel)
typeCheckTelescope ctx (VarsTele vars expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    k1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    case extendCtx (map getName vars) Nil (Type r1 k1) of
        SomeEq ctx' -> do
            (rctx, Type r2 k2) <- typeCheckTelescope (ctx +++ ctx') tele $ fmap (liftBase ctx') term
            let sem = Semantics (S.Pi Explicit $ reverse $ ctxVars ctx') (V.Pi k1 k2)
            return (rctx, Type (Apply sem [r1, abstractTerm ctx' r2]) $ dmax k1 k2)
typeCheckTelescope ctx (TypeTele expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    k1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    (rctx, Type r2 k2) <- typeCheckTelescope ctx tele term
    return (rctx, Type (Apply (Semantics (S.Pi Explicit []) $ V.Pi k1 k2) [r1,r2]) $ dmax k1 k2)

replaceSort :: Term Semantics a -> Sort -> Term Semantics a
replaceSort (Apply (Semantics p (V.Pi k1 k2)) [a,b]) k = Apply (Semantics p $ V.Pi k1 $ dmax k2 k) [a, replaceSort b k]
replaceSort (Lambda t) k = Lambda (replaceSort t k)
replaceSort _ k = universe k

findOccurrence :: Eq a => ID -> Term Semantics a -> Maybe Int
findOccurrence dt (Apply (Semantics _ V.Pi{}) [a,b]) =
    case (findOccurrence dt $ nf WHNF a, findOccurrence dt $ nf WHNF b) of
        (Nothing, Nothing) -> Nothing
        (Nothing, Just b') -> Just b'
        (Just a', Nothing) -> Just (succ a')
        (Just a', Just b') -> Just $ max (succ a') b'
findOccurrence dt (Lambda t) = findOccurrence dt (nf WHNF t)
findOccurrence dt t = if dt `elem` collectDataTypes t then Just 0 else Nothing

collectDataTypes :: Term Semantics a -> [ID]
collectDataTypes = biconcatMap (\t -> case t of
    Semantics _ (DataType dt _) -> [dt]
    _                           -> []) (const [])
