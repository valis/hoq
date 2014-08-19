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
import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable,traverse,sequenceA,fmapDefault,foldMapDefault)

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

instance Functor  (Type p) where fmap = fmapDefault
instance Foldable (Type p) where foldMap = foldMapDefault

instance Traversable (Type p) where
    traverse f (Type t k) = fmap (\t' -> Type t' k) (traverse f t)

cmpTerms :: Eq a => Term Semantics a -> Term Semantics (Either k a) -> Maybe [(k, Maybe (Term Semantics a))]
cmpTerms (Var a as) (Var (Right a') as') = if a == a' then cmpTermsList as as' else Nothing
cmpTerms t (Var (Left k) []) = Just [(k, Just t)]
cmpTerms _ (Var (Left k) _) = Just [(k, Nothing)]
cmpTerms (Lambda t) (Lambda t') = fmap lowerResult $ cmpTerms t (fmap sequenceA t')
cmpTerms (Apply (Semantics (S.Lam (_:vs)) Lam) [Lambda t]) (Apply (Semantics (S.Lam (_:vs')) Lam) [Lambda t']) =
    fmap lowerResult $ cmpTerms (Apply (Semantics (S.Lam vs) Lam) [t]) (Apply (Semantics (S.Lam vs') Lam) [fmap sequenceA t'])
cmpTerms (Apply (Semantics (S.Lam (_:vs)) Lam) [Lambda t]) t' =
    fmap lowerResult $ cmpTerms (Apply (Semantics (S.Lam vs) Lam) [t]) (apps (fmap (sequenceA . Free) t') [fmap Right bvar])
cmpTerms (Apply (Semantics _ Lam) [t]) t' = cmpTerms t t'
cmpTerms t (Apply (Semantics (S.Lam (_:vs')) Lam) [Lambda t']) =
    fmap lowerResult $ cmpTerms (apps (fmap Free t) [bvar]) (Apply (Semantics (S.Lam vs') Lam) [fmap sequenceA t'])
cmpTerms t (Apply (Semantics _ Lam) [t']) = cmpTerms t t'
cmpTerms t@(Apply (Semantics _ Pi{}) _) t'@(Apply (Semantics _ Pi{}) _) =
    pcmpTerms t t' >>= \(o,l) -> if o == EQ then Just l else Nothing
cmpTerms (Apply (Semantics _ (Con PCon)) ts) (Apply (Semantics _ (Con PCon)) ts') = cmpTermsList ts ts'
cmpTerms (Apply (Semantics _ (Con PCon)) [Apply (Semantics _ Lam) [Lambda (Apply (Semantics _ At) [_, _, t, Var Bound []])]]) t' =
    fmap lowerResult $ cmpTerms t (fmap (sequenceA . Free) t')
cmpTerms t (Apply (Semantics _ (Con PCon)) [Apply (Semantics _ Lam) [Lambda (Apply (Semantics _ At) [_, _, t', Var Bound []])]]) =
    fmap lowerResult $ cmpTerms (fmap Free t) (fmap sequenceA t')
cmpTerms (Apply (Semantics _ At) (_:_:ts)) (Apply (Semantics _ At) (_:_:ts')) = cmpTermsList ts ts'
cmpTerms (Apply s ts) (Apply s' ts') = if s == s' then cmpTermsList ts ts' else Nothing
cmpTerms _ _ = Nothing

cmpTermsList :: Eq a => [Term Semantics a] -> [Term Semantics (Either k a)] -> Maybe [(k, Maybe (Term Semantics a))]
cmpTermsList as as' = fmap concat $ sequence (zipWith cmpTerms as as')

lowerResult :: [(k, Maybe (Term Semantics (Scoped a)))] -> [(k, Maybe (Term Semantics a))]
lowerResult = map $ \(k,mt) -> (k, mt >>= \t -> case sequenceA t of
    Free t' -> return t'
    Bound -> Nothing)

pcmpTerms :: Eq a => Term Semantics a -> Term Semantics (Either k a) -> Maybe (Ordering, [(k, Maybe (Term Semantics a))])
pcmpTerms (Apply (Semantics (S.Pi e vs) p@Pi{}) [a, b@Lambda{}]) (Apply (Semantics (S.Pi e' vs') p'@Pi{}) [a', b'@Lambda{}]) =
    contraCovariant (pcmpTerms a a') (go vs a b vs' a' b')
  where
    go :: Eq a => [String] -> Term Semantics a -> Term Semantics a
               -> [String] -> Term Semantics (Either k a) -> Term Semantics (Either k a)
               -> Maybe (Ordering, [(k, Maybe (Term Semantics a))])
    go (_:vs) a (Lambda b) (_:vs') a' (Lambda b') =
        plowerResult $ go vs (fmap Free a) b vs' (fmap (sequenceA . Free) a') (fmap sequenceA b')
    go vs a b@Lambda{} _ _ b' = pcmpTerms (Apply (Semantics (S.Pi e vs) p) [a, b]) b'
    go _ _ b vs' a' b'@Lambda{} = pcmpTerms b $ Apply (Semantics (S.Pi e' vs') p') [a', b']
    go _ _ b _ _ b' = pcmpTerms b b'
pcmpTerms (Apply (Semantics S.Pi{} p@Pi{}) [a, Lambda b]) (Apply (Semantics S.Pi{} p'@Pi{}) [a', b']) =
    contraCovariant (pcmpTerms a a') $ plowerResult $ pcmpTerms b $ fmap (sequenceA . Free) b'
pcmpTerms (Apply (Semantics _ Pi{}) [a, b]) (Apply (Semantics _ Pi{}) [a', Lambda b']) =
    contraCovariant (pcmpTerms a a') $ plowerResult $ pcmpTerms (fmap Free b) (fmap sequenceA b')
pcmpTerms (Apply (Semantics _ Pi{}) [a, b]) (Apply (Semantics _ Pi{}) [a', b']) =
    contraCovariant (pcmpTerms a a') (pcmpTerms b b')
pcmpTerms (Apply (Semantics _ (Universe k)) _) (Apply (Semantics _ (Universe k')) _) = fmap (\o -> (o, [])) (pcompare k k')
pcmpTerms t t' = fmap (\l -> (EQ, l)) (cmpTerms t t')

plowerResult :: Maybe (Ordering, [(k, Maybe (Term Semantics (Scoped a)))]) -> Maybe (Ordering, [(k, Maybe (Term Semantics a))])
plowerResult = fmap $ \(o,l) -> (o, lowerResult l)

contraCovariant :: Maybe (Ordering, [w]) -> Maybe (Ordering, [w]) -> Maybe (Ordering, [w])
contraCovariant (Just (LT,la)) (Just (r,lb)) | r == EQ || r == GT = Just (GT, la ++ lb)
contraCovariant (Just (EQ,la)) (Just (r,lb))                      = Just (r,  la ++ lb)
contraCovariant (Just (GT,la)) (Just (r,lb)) | r == LT || r == EQ = Just (LT, la ++ lb)
contraCovariant _ _                                               = Nothing

instance Eq a => Eq (Term Semantics a) where
    t == t' = case cmpTerms t (fmap Right t') of
        Just [] -> True
        _       -> False

instance Eq1 (Term Semantics) where (==#) = (==)

instance Eq a => Eq (Type Semantics a) where
    Type t _ == Type t' _ = t == t'

instance Eq a => POrd (Term Semantics a) where
    pcompare t t' = pcmpTerms t (fmap Right t') >>= \(o,l) -> if null l then Just o else Nothing

dropOnePi :: Semantics -> Term Semantics a -> Term Semantics a -> (String, Term Semantics (Scoped a))
dropOnePi (Semantics (S.Pi _ [v]) _) a (Lambda b) = (v, b)
dropOnePi (Semantics (S.Pi e (v:vs)) s) a (Lambda b) = (v, Apply (Semantics (S.Pi e vs) s) [fmap Free a, b])
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
