{-# LANGUAGE GADTs #-}

module Semantics.Pattern
    ( Pattern(..), Patterns(..)
    , Clause(..), clauseToEval
    , patternToTerm, patternsToTerms
    , patternsLength, (+++)
    , Split(..), patternsSplitAt
    ) where

import Semantics
import Semantics.Value

data Pattern b a where
    PatDCon :: Int -> Int -> [Clause b] -> Patterns b a -> Pattern b a
    PatPCon :: Pattern b a -> Pattern b a
    PatICon :: ICon -> Pattern b b
    PatVar  :: String -> Pattern b (Scoped b)

data Patterns b a where
    Nil :: Patterns b b
    Cons :: Pattern b c -> Patterns c d -> Patterns b d

data Clause b where
    Clause :: Patterns b a -> Term Semantics a -> Clause b

patternToTerm :: Pattern b a -> Term Int String
patternToTerm (PatDCon i _ _ ps) = Apply i (patternsToTerms ps)
patternToTerm (PatPCon p) = Apply 0 [patternToTerm p]
patternToTerm (PatICon ILeft) = capply 0
patternToTerm (PatICon IRight) = capply 1
patternToTerm (PatVar v) = cvar v

patternsToTerms :: Patterns b a -> [Term Int String]
patternsToTerms Nil = []
patternsToTerms (Cons p ps) = patternToTerm p : patternsToTerms ps

clauseToEval :: Clause b -> ([Term Int String], Term Semantics b)
clauseToEval (Clause pats term) = (patternsToTerms pats, abstractTermPats pats term)

abstractTermPats :: Patterns b a -> Term Semantics a -> Term Semantics b
abstractTermPats Nil t = t
abstractTermPats (Cons p ps) t = abstractTermPat p (abstractTermPats ps t)

abstractTermPat :: Pattern b a -> Term Semantics a -> Term Semantics b
abstractTermPat (PatDCon _ _ _ ps) t = abstractTermPats ps t
abstractTermPat (PatPCon p) t = abstractTermPat p t
abstractTermPat PatICon{} t = t
abstractTermPat PatVar{} t = Lambda t

patternsLength :: Patterns a b -> Int
patternsLength Nil = 0
patternsLength (Cons _ ps) = patternsLength ps + 1

(+++) :: Patterns a b -> Patterns b c -> Patterns a c
Nil +++ ps' = ps'
Cons p ps +++ ps' = Cons p (ps +++ ps')

data Split b a where
    Split :: Patterns b c -> Patterns c a -> Split b a

patternsSplitAt :: Patterns b a -> Int -> Split b a
patternsSplitAt pats 0 = Split Nil pats
patternsSplitAt Nil _ = Split Nil Nil
patternsSplitAt (Cons pat pats) k = case patternsSplitAt pats (k - 1) of
    Split pats1 pats2 -> Split (Cons pat pats1) pats2
