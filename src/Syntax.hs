{-# LANGUAGE FlexibleInstances #-}

module Syntax
    ( Syntax(..), Type(..)
    , Level(..), Explicit(..)
    , PatternC, PatternP
    , lessOrEqual
    , apps, capps, collect, dropOnePi
    , module Syntax.Term, module Syntax.Pattern
    
    , RawExpr, Posn, PIdent(..)
    , Clause(..), Con(..)
    , Import, Def(..), Tele(..)
    ) where

import Data.Void
import Prelude.Extras

import Syntax.Term
import Syntax.Pattern

type Posn = (Int, Int)
data PIdent = PIdent { getPos :: Posn, getName :: String }
data Clause = Clause PIdent [PatternP PIdent] RawExpr
type Import = [String]
data Tele = VarsTele [PIdent] RawExpr | TypeTele RawExpr
data Con = ConDef PIdent [Tele]

data Def
    = DefType PIdent RawExpr
    | DefFun PIdent [PatternP PIdent] (Maybe RawExpr)
    | DefData PIdent [Tele] [Con] [Clause]
    | DefImport Import

{-
data Syntax
    = App
    | Lam [String]
    | Pi [String]
    | PathImp
    | Ident String
-}

data Syntax
    = App
    | Lam [String]
    | Pi [String] Level Level
    | Con Int PIdent [([PatternC String], Closed (Scope String (Term Syntax)))]
    | FunCall PIdent [([PatternC String], Closed (Scope String (Term Syntax)))]
    | FunSyn String (Closed (Term Syntax))
    | Universe Level
    | DataType String Int
    | Interval
    | ICon ICon
    | Path Explicit Level
    | PCon
    | At
    | Coe
    | Iso
    | Squeeze
    | Ident String

type RawExpr = Term (Posn, Syntax) Void
data Level = Level Int | NoLevel
data Type p a = Type { getType :: Term p a, getLevel :: Level }
data Explicit = Explicit | Implicit
type PatternP = Pattern Posn (Closed (Scope String (Term (Posn, Syntax))))
type PatternC = Pattern ()   (Closed (Scope String (Term Syntax)))

instance Eq Level where
    l1 == l2 = level l1 == level l2

instance Ord Level where
    compare l1 l2 = compare (level l1) (level l2)

instance Show Level where
    show = show . level

instance Read Level where
    readsPrec _ ('T':'y':'p':'e':s) = case reads s of
        [] -> [(NoLevel, s)]
        is -> map (\(i,r) -> (Level i, r)) is
    readsPrec _ _ = []

instance Enum Level where
    toEnum 0 = NoLevel
    toEnum n = Level n
    fromEnum = level

level :: Level -> Int
level (Level l) = l
level NoLevel = 0

instance Eq PIdent where
    PIdent _ s == PIdent _ s' = s == s'

instance Eq a => Eq (Term Syntax a) where
    Var a == Var a' = a == a'
    Lambda (Scope1 t) == Lambda (Scope1 t') = t == t'
    Apply App ts == Apply App ts' = ts == ts'
    Apply (Lam []) [t] == t' = t == t'
    t == Apply (Lam []) [t'] = t == t'
    Apply (Lam (_:vs)) [Lambda (Scope1 t)] == Apply (Lam (_:vs')) [Lambda (Scope1 t')] = Apply (Lam vs) [t] == Apply (Lam vs) [t']
    Apply (Lam (_:vs)) [Lambda (Scope1 t)] == t' = Apply (Lam vs) [t] == Apply App [fmap Free t', Var Bound]
    t == t'@(Apply Lam{} _) = t' == t
    t@(Apply Pi{} _) == t'@(Apply Pi{} _) = pcompare t t' == Just EQ
    Apply (Con c _ _) ts == Apply (Con c' _ _) ts' = c == c' && ts == ts'
    Apply (FunCall n _) ts == Apply (FunCall n' _) ts' = n == n' && ts == ts'
    Apply (FunSyn n _) ts == Apply (FunSyn n' _) ts' = n == n' && ts == ts'
    Apply (Universe u) ts == Apply (Universe u') ts' = u == u' && ts == ts'
    Apply (DataType d _) ts == Apply (DataType d' _) ts' = d == d' && ts == ts'
    Apply Interval ts == Apply Interval ts' = ts == ts'
    Apply (ICon c) ts == Apply (ICon c') ts' = c == c' && ts == ts'
    Apply (Path Explicit _) ts == Apply (Path Explicit _) ts' = ts == ts'
    Apply (Path _ _) ts == Apply (Path _ _) ts' =
        if length ts < 3 || length ts' < 3 then ts == ts' else tail ts == tail ts'
    Apply PCon ts == Apply PCon ts' = ts == ts'
    Apply PCon [Apply Lam{} [Lambda (Scope1 (Apply At [_,_,t,Var Bound]))]] == t' = t == fmap Free t'
    t == t'@(Apply PCon _) = t' == t
    Apply At (_:_:ts) == Apply At (_:_:ts') = ts == ts'
    Apply Coe ts == Apply Coe ts' = ts == ts'
    Apply Iso ts == Apply Iso ts' = ts == ts'
    Apply Squeeze ts == Apply Squeeze ts' = ts == ts'
    Apply (Ident v) ts == Apply (Ident v') ts' = v == v' && ts == ts'
    _ == _ = False

instance Eq1 (Term Syntax) where (==#) = (==)

instance Eq a => Eq (Type Syntax a) where
    Type t _ == Type t' _ = t == t'

pcompare :: Eq a => Term Syntax a -> Term Syntax a -> Maybe Ordering
pcompare (Apply t ts) (Apply t' ts') = go t ts t' ts'
  where
    go :: Eq a => Syntax -> [Term Syntax a] -> Syntax -> [Term Syntax a] -> Maybe Ordering
    go p@Pi{} [a, Lambda (Scope1 b)] p'@Pi{} [a', Lambda (Scope1 b')] = go p [fmap Free a, b] p' [fmap Free a', b']
    go p@Pi{} [a, b] p'@Pi{} [a', Lambda (Scope1 b')] = go p [fmap Free a, fmap Free b] p' [fmap Free a', b']
    go p@Pi{} [a, Lambda (Scope1 b)] p'@Pi{} [a', b'] = go p [fmap Free a, b] p' [fmap Free a', fmap Free b']
    go p@Pi{} [a, b] p'@Pi{} [a', b'] = contraCovariant (pcompare a a') (pcompare b b')
    go (Universe u) _ (Universe u') _ = Just $ compare (level u) (level u')
    go t ts t' ts' = if Apply t ts == Apply t' ts' then Just EQ else Nothing
pcompare t t' = if t == t' then Just EQ else Nothing

contraCovariant :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
contraCovariant (Just LT) (Just r) | r == EQ || r == GT = Just GT
contraCovariant (Just EQ) r                             = r
contraCovariant (Just GT) (Just r) | r == LT || r == EQ = Just LT
contraCovariant _ _                                     = Nothing

lessOrEqual :: Eq a => Term Syntax a -> Term Syntax a -> Bool
lessOrEqual t t' = case pcompare t t' of
    Just r | r == EQ || r == LT -> True
    _                           -> False

instance Functor (Type p) where
    fmap f (Type t l) = Type (fmap f t) l

apps :: Term Syntax a -> [Term Syntax a] -> Term Syntax a
apps t [] = t
apps t (t':ts) = apps (Apply App [t,t']) ts

capps :: Syntax -> [Term Syntax a] -> Term Syntax a
capps = apps . cterm

collect :: Term Syntax a -> (Maybe Syntax, [Term Syntax a])
collect = go []
  where
    go as (Apply App [t1, t2]) = go (t2:as) t1
    go as (Apply t _) = (Just t, as)
    go as _ = (Nothing, as)

dropOnePi :: Syntax -> Term Syntax a -> Term Syntax a -> (String, Term Syntax (Scoped a))
dropOnePi (Pi [v] l1 l2) a (Lambda (Scope1 b)) = (v, b)
dropOnePi (Pi (v:vs) l1 l2) a (Lambda (Scope1 b)) = (v, Apply (Pi vs l1 l2) [fmap Free a, b])
dropOnePi _ _ b = ("_", fmap Free b)
