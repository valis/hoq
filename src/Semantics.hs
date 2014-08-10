{-# LANGUAGE FlexibleInstances #-}
    
module Semantics
    ( Semantics(..), Type(..)
    , SCon, SValue, SEval
    , lessOrEqual, pcompare
    , dropOnePi, iCon, universe
    , module Syntax.Term
    ) where

import Prelude.Extras

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

data Type p a = Type { getType :: Term p a, getLevel :: Level }

instance Functor (Type p) where
    fmap f (Type t l) = Type (fmap f t) l

instance Eq a => Eq (Term Semantics a) where
    Var a as == Var a' as' = a == a' && as == as'
    Lambda t == Lambda t' = t == t'
    Apply s@(Semantics _ Lam) [Lambda t] == Apply s'@(Semantics _ Lam) [Lambda t'] = Apply s [t] == Apply s' [t']
    Apply s@(Semantics _ Lam) [Lambda t] == t' = Apply s [t] == apps (fmap Free t') [cvar Bound]
    Apply (Semantics _ Lam) [t] == t' = t == t'
    t == t'@(Apply (Semantics _ Lam) _) = t' == t
    t@(Apply (Semantics _ Pi{}) _) == t'@(Apply (Semantics _ Pi{}) _) = pcompare t t' == Just EQ
    Apply (Semantics _ (Con PCon)) ts == Apply (Semantics _ (Con PCon)) ts' = ts == ts'
    Apply (Semantics _ (Con PCon)) [Apply (Semantics _ Lam) [Lambda (Apply (Semantics _ At) [_, _, t, Var Bound []])]] == t' = t == fmap Free t'
    t == t'@(Apply (Semantics _ (Con PCon)) _) = t' == t
    Apply (Semantics _ At) (_:_:ts) == Apply (Semantics _ At) (_:_:ts') = ts == ts'
    Apply s ts == Apply s' ts' = s == s' && ts == ts'
    _ == _ = False

instance Eq1 (Term Semantics) where (==#) = (==)

instance Eq a => Eq (Type Semantics a) where
    Type t _ == Type t' _ = t == t'

pcompare :: Eq a => Term Semantics a -> Term Semantics a -> Maybe Ordering
pcompare (Apply t ts) (Apply t' ts') = go t ts t' ts'
  where
    go :: Eq a => Semantics -> [Term Semantics a] -> Semantics -> [Term Semantics a] -> Maybe Ordering
    go p@(Semantics _ Pi{}) [a, Lambda b] p'@(Semantics _ Pi{}) [a', Lambda b'] =
        go p [fmap Free a, b] p' [fmap Free a', b']
    go p@(Semantics _ Pi{}) [a, b] p'@(Semantics _ Pi{}) [a', Lambda b'] =
        go p [fmap Free a, fmap Free b] p' [fmap Free a', b']
    go p@(Semantics _ Pi{}) [a, Lambda b] p'@(Semantics _ Pi{}) [a', b'] =
        go p [fmap Free a, b] p' [fmap Free a', fmap Free b']
    go p@(Semantics _ Pi{}) [a, b] p'@(Semantics _ Pi{}) [a', b'] = contraCovariant (pcompare a a') (pcompare b b')
    go (Semantics _ (Universe u)) _ (Semantics _ (Universe u')) _ = Just $ compare (level u) (level u')
    go t ts t' ts' = if Apply t ts == Apply t' ts' then Just EQ else Nothing
pcompare t t' = if t == t' then Just EQ else Nothing

contraCovariant :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
contraCovariant (Just LT) (Just r) | r == EQ || r == GT = Just GT
contraCovariant (Just EQ) r                             = r
contraCovariant (Just GT) (Just r) | r == LT || r == EQ = Just LT
contraCovariant _ _                                     = Nothing

lessOrEqual :: Eq a => Term Semantics a -> Term Semantics a -> Bool
lessOrEqual t t' = case pcompare t t' of
    Just r | r == EQ || r == LT -> True
    _                           -> False

dropOnePi :: Semantics -> Term Semantics a -> Term Semantics a -> (String, Term Semantics (Scoped a))
dropOnePi (Semantics (S.Pi [v]) _) a (Lambda b) = (v, b)
dropOnePi (Semantics (S.Pi (v:vs)) s) a (Lambda b) = (v, Apply (Semantics (S.Pi vs) s) [fmap Free a, b])
dropOnePi _ _ b = ("_", fmap Free b)

iCon :: ICon -> Term Semantics a
iCon ILeft  = capply $ Semantics (S.Name S.Prefix $ S.Ident "left")  $ Con (ICon ILeft)
iCon IRight = capply $ Semantics (S.Name S.Prefix $ S.Ident "right") $ Con (ICon IRight)

universe :: Level -> Term Semantics a
universe lvl = capply $ Semantics (S.Name S.Prefix $ S.Ident $ show lvl) (Universe lvl)
