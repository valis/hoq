{-# LANGUAGE FlexibleInstances #-}

module Semantics
    ( Semantics(..), Type(..)
    , SValue, SEval
    , isInj
    , cmpTerms, pcmpTerms
    , dropOnePi, universe
    , iConSem, iCon
    , pathSem, path, interval
    , module Syntax.Term
    ) where

import Data.Foldable(Foldable(..))
import Data.Traversable(Traversable,traverse,sequenceA,fmapDefault,foldMapDefault)
import Data.Bifunctor

import Syntax.Term
import qualified Syntax as S
import Semantics.Value

data Semantics = Semantics
    { syntax :: S.Syntax
    , value :: SValue
    }

type SValue = Value (Closed (Term Semantics))
type SEval = Eval (Closed (Term Semantics))

instance Eq Semantics where
    s1 == s2 = value s1 == value s2

data Type p a = Type { getType :: Term p a, getSort :: Sort }

instance Functor  (Type p) where fmap = fmapDefault
instance Foldable (Type p) where foldMap = foldMapDefault

instance Traversable (Type p) where
    traverse f (Type t k) = fmap (\t' -> Type t' k) (traverse f t)

isInj :: Value t -> Bool
isInj Lam = True
isInj Pi{} = True
isInj PCon = True
isInj ICon{} = True
isInj (DCon _ _ _ []) = True
isInj DCon{} = False
isInj CCon = True
isInj FunCall{} = False
isInj Universe{} = True
isInj DataType{} = True
isInj Interval{} = True
isInj Path{} = True
isInj At{} = False
isInj Coe{} = False
isInj Iso{} = False
isInj Squeeze{} = False
isInj Case{} = False
isInj Conds{} = False
isInj FieldAcc{} = False

cmpTerms :: Eq a => Term Semantics (Either k a) -> Term Semantics (Either n a)
    -> (Bool, ([(k, Term Semantics a)], [(n, Term Semantics a)]))
cmpTerms (Lambda t) (Lambda t') = flowerResult $ cmpTerms (fmap sequenceA t) (fmap sequenceA t')
cmpTerms (Lambda t) t' = cmpTerms (Lambda t) (Lambda $ apps (fmap Free t') [bvar])
cmpTerms t (Lambda t') = cmpTerms (Lambda $ apps (fmap Free t) [bvar]) (Lambda t')
cmpTerms (Apply (Semantics (S.Lam (_:vs)) Lam) [Lambda t]) (Apply (Semantics (S.Lam (_:vs')) Lam) [Lambda t']) =
    flowerResult $ cmpTerms (Apply (Semantics (S.Lam vs) Lam) [fmap sequenceA t]) (Apply (Semantics (S.Lam vs') Lam) [fmap sequenceA t'])
cmpTerms (Apply (Semantics (S.Lam (_:vs)) Lam) [Lambda t]) t' =
    flowerResult $ cmpTerms (Apply (Semantics (S.Lam vs) Lam) [fmap sequenceA t]) (apps (fmap (sequenceA . Free) t') [fmap Right bvar])
cmpTerms (Apply (Semantics _ Lam) [t]) t' = cmpTerms t t'
cmpTerms t (Apply (Semantics (S.Lam (_:vs')) Lam) [Lambda t']) =
    flowerResult $ cmpTerms (apps (fmap (sequenceA . Free) t) [fmap Right bvar]) (Apply (Semantics (S.Lam vs') Lam) [fmap sequenceA t'])
cmpTerms t (Apply (Semantics _ Lam) [t']) = cmpTerms t t'
cmpTerms (Var (Right a) as) (Var (Right a') as') = if a == a' then cmpTermsList as as' else (False, ([],[]))
cmpTerms (Var (Left k) []) t' = (True, (case sequenceA t' of { Left{} -> []; Right r -> [(k,r)] }, []))
cmpTerms t (Var (Left k) []) = (True, ([], case sequenceA t of { Left{} -> []; Right r -> [(k,r)] }))
cmpTerms (Var Left{} _) _ = (True, ([], []))
cmpTerms _ (Var Left{} _) = (True, ([], []))
cmpTerms t@(Apply (Semantics _ Pi{}) _) t'@(Apply (Semantics _ Pi{}) _) = first (== Just EQ) (pcmpTerms t t')
cmpTerms (Apply (Semantics _ PCon) ts) (Apply (Semantics _ PCon) ts') = cmpTermsList ts ts'
cmpTerms (Apply (Semantics _ PCon) [Apply (Semantics _ Lam) [Lambda (Apply (Semantics _ At) [_, _, t, Var Bound []])]]) t' =
    flowerResult $ cmpTerms (fmap sequenceA t) (fmap (sequenceA . Free) t')
cmpTerms t (Apply (Semantics _ PCon) [Apply (Semantics _ Lam) [Lambda (Apply (Semantics _ At) [_, _, t', Var Bound []])]]) =
    flowerResult $ cmpTerms (fmap (sequenceA . Free) t) (fmap sequenceA t')
cmpTerms (Apply (Semantics _ At) (_:_:ts)) (Apply (Semantics _ At) (_:_:ts')) = cmpTermsList ts ts'
cmpTerms (Apply (Semantics _ (DCon dt i k _)) ts) (Apply (Semantics _ (DCon dt' i' k' _)) ts') | dt == dt' && i == i' =
    cmpTermsList (drop k ts) (drop k' ts')
cmpTerms (Apply (Semantics _ Conds{}) (t:_)) t' = cmpTerms t t'
cmpTerms t (Apply (Semantics _ Conds{}) (t':_)) = cmpTerms t t'
cmpTerms (Apply (Semantics _ (FieldAcc i _ k _)) (t:ts)) (Apply (Semantics _ (FieldAcc i' _ k' _)) (t':ts')) | i == i' =
    cmpTermsList (t : drop k ts) (t' : drop k' ts')
cmpTerms (Apply s ts) (Apply s' ts') = if s == s'
    then cmpTermsList ts ts'
    else (not (isInj $ value s) && hasLefts ts || not (isInj $ value s') && hasLefts ts', ([],[]))
  where
    hasLefts :: [Term Semantics (Either k a)] -> Bool
    hasLefts = any $ \t -> case sequenceA t of
        Left{} -> True
        Right{} -> False
cmpTerms _ _ = (False,([],[]))

cmpTermsList :: Eq a => [Term Semantics (Either k a)] -> [Term Semantics (Either n a)]
    -> (Bool, ([(k, Term Semantics a)], [(n, Term Semantics a)]))
cmpTermsList as as' = bimap and (bimap concat concat . unzip) $ unzip (zipWith cmpTerms as as')

flowerResult :: (b, ([(k, Term Semantics (Scoped a))], [(n, Term Semantics (Scoped a))]))
    -> (b, ([(k, Term Semantics a)], [(n, Term Semantics a)]))
flowerResult (b, (t1,t2)) = (b, (lowerResult t1, lowerResult t2))

lowerResult :: [(k, Term Semantics (Scoped a))] -> [(k, Term Semantics a)]
lowerResult ts = ts >>= \(k,t) -> case sequenceA t of
    Free t' -> [(k,t')]
    Bound -> []

pcmpTerms :: Eq a => Term Semantics (Either k a) -> Term Semantics (Either n a)
    -> (Maybe Ordering, ([(k, Term Semantics a)], [(n, Term Semantics a)]))
pcmpTerms (Apply (Semantics (S.Pi e vs) p@Pi{}) [a, b@Lambda{}]) (Apply (Semantics (S.Pi e' vs') p'@Pi{}) [a', b'@Lambda{}]) =
    fcontraCovariant (pcmpTerms a a') (go vs a b vs' a' b')
  where
    go :: Eq a => [String] -> Term Semantics (Either k a) -> Term Semantics (Either k a)
               -> [String] -> Term Semantics (Either n a) -> Term Semantics (Either n a)
               -> (Maybe Ordering, ([(k, Term Semantics a)], [(n, Term Semantics a)]))
    go (_:vs) a (Lambda b) (_:vs') a' (Lambda b') = flowerResult $
        go vs (fmap (sequenceA . Free) a) (fmap sequenceA b) vs' (fmap (sequenceA . Free) a') (fmap sequenceA b')
    go vs a b@Lambda{} _ _ b' = pcmpTerms (Apply (Semantics (S.Pi e vs) p) [a, b]) b'
    go _ _ b vs' a' b'@Lambda{} = pcmpTerms b $ Apply (Semantics (S.Pi e' vs') p') [a', b']
    go _ _ b _ _ b' = pcmpTerms b b'
pcmpTerms (Apply (Semantics S.Pi{} p@Pi{}) [a, Lambda b]) (Apply (Semantics S.Pi{} p'@Pi{}) [a', b']) =
    fcontraCovariant (pcmpTerms a a') $ flowerResult $ pcmpTerms (fmap sequenceA b) (fmap (sequenceA . Free) b')
pcmpTerms (Apply (Semantics _ Pi{}) [a, b]) (Apply (Semantics _ Pi{}) [a', Lambda b']) =
    fcontraCovariant (pcmpTerms a a') $ flowerResult $ pcmpTerms (fmap (sequenceA . Free) b) (fmap sequenceA b')
pcmpTerms (Apply (Semantics _ Pi{}) [a, b]) (Apply (Semantics _ Pi{}) [a', b']) =
    fcontraCovariant (pcmpTerms a a') (pcmpTerms b b')
pcmpTerms (Apply (Semantics _ (Universe k)) _) (Apply (Semantics _ (Universe k')) _) = (pcompare k k', ([], []))
pcmpTerms t t' = first (\b -> if b then Just EQ else Nothing) (cmpTerms t t')

contraCovariant :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
contraCovariant (Just LT) (Just r) | r == EQ || r == GT = Just GT
contraCovariant (Just EQ) (Just r)                      = Just r
contraCovariant (Just GT) (Just r) | r == LT || r == EQ = Just LT
contraCovariant _ _                                     = Nothing

fcontraCovariant :: (Maybe Ordering, ([u],[v])) -> (Maybe Ordering, ([u],[v])) -> (Maybe Ordering, ([u],[v]))
fcontraCovariant (mo1,(us1,vs1)) (mo2,(us2,vs2)) = (contraCovariant mo1 mo2, (us1 ++ us2, vs1 ++ vs2))

instance Eq a => Eq (Term Semantics a) where
    t == t' = fst $ cmpTerms (fmap Right t) (fmap Right t')

instance Eq a => Eq (Type Semantics a) where
    Type t _ == Type t' _ = t == t'

instance Eq a => POrd (Term Semantics a) where
    pcompare t t' = fst $ pcmpTerms (fmap Right t) (fmap Right t')

dropOnePi :: Semantics -> Term Semantics a -> Term Semantics a -> (String, Term Semantics (Scoped a))
dropOnePi (Semantics (S.Pi _ [v]) _) a (Lambda b) = (v, b)
dropOnePi (Semantics (S.Pi e (v:vs)) s) a (Lambda b) = (v, Apply (Semantics (S.Pi e vs) s) [fmap Free a, b])
dropOnePi _ _ b = ("_", fmap Free b)

iConSem :: ICon -> Semantics
iConSem ILeft  = Semantics (S.Name S.Prefix $ S.Ident "left")  (ICon ILeft)
iConSem IRight = Semantics (S.Name S.Prefix $ S.Ident "right") (ICon IRight)

iCon :: ICon -> Term Semantics a
iCon = capply . iConSem

pathSem :: Semantics
pathSem = Semantics (S.Name S.Prefix $ S.Ident "path") PCon

path :: [Term Semantics a] -> Term Semantics a
path = Apply pathSem

interval :: Term Semantics a
interval = capply $ Semantics (S.Name S.Prefix $ S.Ident "I") Interval

universe :: Sort -> Term Semantics a
universe k = capply $ Semantics (S.Name S.Prefix $ S.Ident $ show k) (Universe k)
