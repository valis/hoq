{-# LANGUAGE FlexibleInstances #-}
    
module Semantics
    ( Semantics(..), Type(..)
    , SCon, SValue, SEval
    , cmpTerms, pcmpTerms
    , dropOnePi, iCon, universe
    , path, interval
    , module Syntax.Term
    ) where

import Prelude.Extras
import Control.Monad
import Data.Traversable(sequenceA)

import Syntax.Term
import qualified Syntax as S
import Semantics.Value

data Semantics = Semantics
    { syntax :: S.Syntax
    , value :: SValue
    }

type SCon = Con (Closed (Term Semantics))
type SValue = Value (Closed (Term Semantics))
type SEval = Eval (Closed (Term Semantics))

instance Eq Semantics where
    s1 == s2 = value s1 == value s2

data Type p a = Type { getType :: Term p a, getSort :: Sort }

instance Functor (Type p) where
    fmap f (Type t k) = Type (fmap f t) k

cmpTerms :: (a -> b -> Bool) -> Term Semantics a -> Term Semantics b -> Maybe [(a, b, Term Semantics a, Term Semantics b)]
cmpTerms f t@(Var a as) t'@(Var a' as') = fmap ((if f a a' then [] else [(a, a', t, t')]) ++) (cmpTermsList f as as')
cmpTerms f (Lambda t) (Lambda t') = cmpTerms (cmpScoped f) t t' >>= lowerResult
cmpTerms f (Apply (Semantics (S.Lam (_:vs)) Lam) [Lambda t]) (Apply (Semantics (S.Lam (_:vs')) Lam) [Lambda t']) =
    cmpTerms (cmpScoped f) (Apply (Semantics (S.Lam vs) Lam) [t]) (Apply (Semantics (S.Lam vs') Lam) [t']) >>= lowerResult
cmpTerms f (Apply (Semantics (S.Lam (_:vs)) Lam) [Lambda t]) t' =
    cmpTerms (cmpScoped f) (Apply (Semantics (S.Lam vs) Lam) [t]) (apps (fmap Free t') [bvar]) >>= lowerResult
cmpTerms f (Apply (Semantics _ Lam) [t]) t' = cmpTerms f t t'
cmpTerms f t t'@(Apply (Semantics _ Lam) _) = fmap (map $ \(a,b,ta,tb) -> (b,a,tb,ta)) $ cmpTerms (\a b -> f b a) t' t
cmpTerms f t@(Apply (Semantics _ Pi{}) _) t'@(Apply (Semantics _ Pi{}) _) =
    pcmpTerms f t t' >>= \(o,l) -> if o == EQ then Just l else Nothing
cmpTerms f (Apply (Semantics _ (Con PCon)) ts) (Apply (Semantics _ (Con PCon)) ts') = cmpTermsList f ts ts'
cmpTerms f (Apply (Semantics _ (Con PCon)) [Apply (Semantics _ Lam) [Lambda (Apply (Semantics _ At) [_, _, t, Var Bound []])]]) t' =
    cmpTerms (cmpScoped f) t (fmap Free t') >>= lowerResult
cmpTerms f t t'@(Apply (Semantics _ (Con PCon)) _) = fmap (map $ \(a,b,ta,tb) -> (b,a,tb,ta)) $ cmpTerms (\a b -> f b a) t' t
cmpTerms f (Apply (Semantics _ At) (_:_:ts)) (Apply (Semantics _ At) (_:_:ts')) = cmpTermsList f ts ts'
cmpTerms f (Apply s ts) (Apply s' ts') = if s == s' then cmpTermsList f ts ts' else Nothing
cmpTerms _ _ _ = Nothing

cmpTermsList :: (a -> b -> Bool) -> [Term Semantics a] -> [Term Semantics b] -> Maybe [(a, b, Term Semantics a, Term Semantics b)]
cmpTermsList f as as' = fmap concat $ sequence $ zipWith (cmpTerms f) as as'

cmpScoped :: (a -> b -> Bool) -> Scoped a -> Scoped b -> Bool
cmpScoped f (Free a) (Free b) = f a b
cmpScoped _ Bound Bound = True
cmpScoped _ _ _ = False

lowerResult :: [(Scoped a, Scoped b, Term Semantics (Scoped a), Term Semantics (Scoped b))]
            -> Maybe [(a, b, Term Semantics a, Term Semantics b)]
lowerResult l = forM l $ \(sa,sb,sta,stb) -> case (sa, sb, sequenceA sta, sequenceA stb) of
    (Free a, Free b, Free ta, Free tb) -> Just (a, b, ta, tb)
    _ -> Nothing

pcmpTerms :: (a -> b -> Bool) -> Term Semantics a -> Term Semantics b
    -> Maybe (Ordering, [(a, b, Term Semantics a, Term Semantics b)])
pcmpTerms f (Apply (Semantics (S.Pi vs) p@Pi{}) [a, b@Lambda{}]) (Apply (Semantics (S.Pi vs') p'@Pi{}) [a', b'@Lambda{}]) =
    contraCovariant (pcmpTerms f a a') (go f vs a b vs' a' b')
  where
    go :: (a -> b -> Bool) -> [String] -> Term Semantics a -> Term Semantics a -> [String] -> Term Semantics b -> Term Semantics b
        -> Maybe (Ordering, [(a, b, Term Semantics a, Term Semantics b)])
    go f (_:vs) a (Lambda b) (_:vs') a' (Lambda b') = plowerResult $ go (cmpScoped f) vs (fmap Free a) b vs' (fmap Free a') b'
    go f vs a b@Lambda{} _ _ b' = pcmpTerms f (Apply (Semantics (S.Pi vs) p) [a, b]) b'
    go f _ _ b vs' a' b'@Lambda{} = pcmpTerms f b $ Apply (Semantics (S.Pi vs') p') [a', b']
    go f _ _ b _ _ b' = pcmpTerms f b b'
pcmpTerms f (Apply (Semantics (S.Pi vs) p@Pi{}) [a, Lambda b]) (Apply (Semantics (S.Pi vs') p'@Pi{}) [a', b']) =
    contraCovariant (pcmpTerms f a a') $ plowerResult $ pcmpTerms (cmpScoped f) b (fmap Free b')
pcmpTerms f (Apply (Semantics _ Pi{}) [a, b]) (Apply (Semantics _ Pi{}) [a', Lambda b']) =
    contraCovariant (pcmpTerms f a a') $ plowerResult $ pcmpTerms (cmpScoped f) (fmap Free b) b'
pcmpTerms f (Apply (Semantics _ Pi{}) [a, b]) (Apply (Semantics _ Pi{}) [a', b']) =
    contraCovariant (pcmpTerms f a a') (pcmpTerms f b b')
pcmpTerms f (Apply (Semantics _ (Universe k)) _) (Apply (Semantics _ (Universe k')) _) = fmap (\o -> (o, [])) (pcompare k k')
pcmpTerms f t t' = fmap (\l -> (EQ, l)) (cmpTerms f t t')

plowerResult :: Maybe (Ordering, [(Scoped a, Scoped b, Term Semantics (Scoped a), Term Semantics (Scoped b))])
    -> Maybe (Ordering, [(a, b, Term Semantics a, Term Semantics b)])
plowerResult r = do
    (o,l) <- r
    l' <- lowerResult l
    return (o,l')

contraCovariant :: Maybe (Ordering, [w]) -> Maybe (Ordering, [w]) -> Maybe (Ordering, [w])
contraCovariant (Just (LT,la)) (Just (r,lb)) | r == EQ || r == GT = Just (GT, la ++ lb)
contraCovariant (Just (EQ,la)) (Just (r,lb))                      = Just (r,  la ++ lb)
contraCovariant (Just (GT,la)) (Just (r,lb)) | r == LT || r == EQ = Just (LT, la ++ lb)
contraCovariant _ _                                               = Nothing

instance Eq a => Eq (Term Semantics a) where
    t == t' = cmpTerms (==) t t' == Just []

instance Eq1 (Term Semantics) where (==#) = (==)

instance Eq a => Eq (Type Semantics a) where
    Type t _ == Type t' _ = t == t'

instance Eq a => POrd (Term Semantics a) where
    pcompare t t' = pcmpTerms (==) t t' >>= \(o,l) -> if null l then Just o else Nothing

dropOnePi :: Semantics -> Term Semantics a -> Term Semantics a -> (String, Term Semantics (Scoped a))
dropOnePi (Semantics (S.Pi [v]) _) a (Lambda b) = (v, b)
dropOnePi (Semantics (S.Pi (v:vs)) s) a (Lambda b) = (v, Apply (Semantics (S.Pi vs) s) [fmap Free a, b])
dropOnePi _ _ b = ("_", fmap Free b)

iCon :: ICon -> Term Semantics a
iCon ILeft  = capply $ Semantics (S.Name S.Prefix $ S.Ident "left")  $ Con (ICon ILeft)
iCon IRight = capply $ Semantics (S.Name S.Prefix $ S.Ident "right") $ Con (ICon IRight)

path :: [Term Semantics a] -> Term Semantics a
path = Apply $ Semantics (S.Name S.Prefix $ S.Ident "path") (Con PCon)

interval :: Term Semantics a
interval = capply $ Semantics (S.Name S.Prefix $ S.Ident "I") Interval

universe :: Sort -> Term Semantics a
universe k = capply $ Semantics (S.Name S.Prefix $ S.Ident $ show k) (Universe k)
