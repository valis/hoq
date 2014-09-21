{-# LANGUAGE GADTs #-}

module Semantics.Pattern
    ( Pattern(..), Patterns(..)
    , Clause(..), clauseToEval
    , ClauseEq(..), clauseToClauseEq
    , abstractClause1
    , patternToTerm, patternsToTerms
    , abstractTermPat, abstractTermPats
    , liftBasePat, liftBasePats
    , patternVars, patternsVars
    , patternsLength, (+++)
    , Split(..), patternsSplitAt
    ) where

import Syntax(Syntax)
import Semantics
import Semantics.Value

data Pattern b a where
    PatDCon :: Syntax -> Int -> Int -> [Closed Clause] -> [Term Semantics b] -> Patterns b a -> Pattern b a
    PatPCon :: Pattern b a -> Pattern b a
    PatICon :: ICon -> Pattern b b
    PatVar  :: String -> Pattern b (Scoped b)

data Patterns b a where
    Nil :: Patterns b b
    Cons :: Pattern b c -> Patterns c d -> Patterns b d

data Clause b where
    Clause :: Patterns b a -> Term Semantics a -> Clause b

data ClauseEq b where
    ClauseEq :: Eq a => Patterns b a -> Term Semantics a -> ClauseEq b

clauseToClauseEq :: Eq b => Clause b -> ClauseEq b
clauseToClauseEq (Clause Nil term) = ClauseEq Nil term
clauseToClauseEq (Clause (Cons (PatDCon v i n cs params ps) pats) term) = case clauseToClauseEq $ Clause (ps +++ pats) term of
    ClauseEq pats' term' -> case patternsSplitAt pats' (patternsLength ps) of
        Split pats1 pats2 -> ClauseEq (Cons (PatDCon v i n cs params pats1) pats2) term'
clauseToClauseEq (Clause (Cons (PatPCon pat) pats) term) = case clauseToClauseEq $ Clause (Cons pat pats) term of
    ClauseEq (Cons pat' pats') term' -> ClauseEq (Cons (PatPCon pat') pats') term'
    _ -> error "clauseToClauseEq"
clauseToClauseEq (Clause (Cons (PatICon con) pats) term) = case clauseToClauseEq (Clause pats term) of
    ClauseEq pats' term' -> ClauseEq (Cons (PatICon con) pats') term'
clauseToClauseEq (Clause (Cons (PatVar var) pats) term) = case clauseToClauseEq (Clause pats term) of
    ClauseEq pats' term' -> ClauseEq (Cons (PatVar var) pats') term'

instance Functor Clause where
    fmap f (Clause Nil term) = Clause Nil (fmap f term)
    fmap f (Clause (Cons (PatDCon v i n cs params ps) pats) term) = case fmap f $ Clause (ps +++ pats) term of
        Clause pats' term' -> case patternsSplitAt pats' (patternsLength ps) of
            Split pats1 pats2 -> Clause (Cons (PatDCon v i n cs (map (fmap f) params) pats1) pats2) term'
    fmap f (Clause (Cons (PatPCon pat) pats) term) = case fmap f $ Clause (Cons pat pats) term of
        Clause (Cons pat' pats') term' -> Clause (Cons (PatPCon pat') pats') term'
        _ -> error "fmap: Clause"
    fmap f (Clause (Cons (PatICon con) pats) term) = case fmap f (Clause pats term) of
        Clause pats' term' -> Clause (Cons (PatICon con) pats') term'
    fmap f (Clause (Cons (PatVar  var) pats) term) = case fmap (fmap f) (Clause pats term) of
        Clause pats' term' -> Clause (Cons (PatVar var) pats') term'

abstractClause1 :: Clause (Scoped b) -> Clause b
abstractClause1 (Clause Nil term) = Clause Nil (Lambda term)
abstractClause1 (Clause (Cons (PatDCon v i n cs params ps) pats) term) =
    case abstractClause1 $ Clause (ps +++ pats) term of
        Clause pats' term' -> case patternsSplitAt pats' (patternsLength ps) of
            Split pats1 pats2 -> Clause (Cons (PatDCon v i n cs (map Lambda params) pats1) pats2) term'
abstractClause1 (Clause (Cons (PatPCon pat) pats) term) = case abstractClause1 $ Clause (Cons pat pats) term of
    Clause (Cons pat' pats') term' -> Clause (Cons (PatPCon pat') pats') term'
    _ -> error "abstractClause1"
abstractClause1 (Clause (Cons (PatICon con) pats) term) = case abstractClause1 (Clause pats term) of
    Clause pats' term' -> Clause (Cons (PatICon con) pats') term'
abstractClause1 (Clause (Cons (PatVar  var) pats) term) = case abstractClause1 (Clause pats term) of
    Clause pats' term' -> Clause (Cons (PatVar var) pats') term'

patternToTerm :: Pattern b a -> Term Int String
patternToTerm (PatDCon _ i _ _ _ ps) = Apply i (patternsToTerms ps)
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
abstractTermPat (PatDCon _ _ _ _ _ ps) t = abstractTermPats ps t
abstractTermPat (PatPCon p) t = abstractTermPat p t
abstractTermPat PatICon{} t = t
abstractTermPat PatVar{} t = Lambda t

liftBasePat :: Pattern b a -> b -> a
liftBasePat (PatDCon _ _ _ _ _ pats) = liftBasePats pats
liftBasePat (PatPCon pat) = liftBasePat pat
liftBasePat PatICon{} = id
liftBasePat PatVar{} = Free

liftBasePats :: Patterns b a -> b -> a
liftBasePats Nil = id
liftBasePats (Cons pat pats) = liftBasePats pats . liftBasePat pat

patternVars :: Pattern b a -> [String]
patternVars (PatDCon _ _ _ _ _ pats) = patternsVars pats
patternVars (PatPCon pat) = patternVars pat
patternVars PatICon{} = []
patternVars (PatVar var) = [var]

patternsVars :: Patterns b a -> [String]
patternsVars Nil = []
patternsVars (Cons pat pats) = patternVars pat ++ patternsVars pats

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
