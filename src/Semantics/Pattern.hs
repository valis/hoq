{-# LANGUAGE GADTs, ExistentialQuantification #-}

module Semantics.Pattern
    ( Pattern(..), Patterns(..)
    , Clause(..), clauseToEval
    , ClauseEq(..), clauseToClauseEq
    , ClauseInCtx(..), Some(..)
    , instantiatePats1, instantiatePats
    , instantiatePatsAndLift1, instantiatePatsAndLift
    , instantiateClause
    , patternToTerm, patternsToTerms
    , patternToTermVar, patternsToTermsVar
    , abstractTermPat, abstractTermPats
    , liftBasePat, liftBasePats
    , patternVars, patternsVars
    , patternsLength, (+++)
    , Split(..), patternsSplitAt
    ) where

import Data.Void

import Syntax(Syntax)
import Semantics
import Semantics.Value
import qualified TypeChecking.Context as C

data Pattern b a where
    PatDCon :: Syntax -> Int -> Int -> [ClauseInCtx] -> [Term Semantics b] -> Patterns b a -> Pattern b a
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

data ClauseInCtx = forall b. Eq b => ClauseInCtx (C.Ctx String (Type Semantics) Void b) (Clause b)
data Some f = forall a. Some (f a)

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

(>>>=) :: Patterns b a -> (b -> Term Semantics c) -> Some (Patterns c)
Nil >>>= _ = Some Nil
Cons (PatDCon v i n cs params ps) pats >>>= k = case (ps +++ pats) >>>= k of
    Some pats' -> case patternsSplitAt pats' (patternsLength ps) of
        Split pats1 pats2 -> Some $ Cons (PatDCon v i n cs (map (>>= k) params) pats1) pats2
Cons (PatPCon pat) pats >>>= k = case Cons pat pats >>>= k of
    Some (Cons pat' pats') -> Some $ Cons (PatPCon pat') pats'
    _ -> error "(>>>=): Patterns"
Cons (PatICon con) pats >>>= k = case pats >>>= k of
    Some pats' -> Some $ Cons (PatICon con) pats'
Cons (PatVar var) pats >>>= k =
    case (pats >>>= \v -> case v of
                            Bound  -> return Bound
                            Free b -> fmap Free (k b)) of
        Some pats' -> Some $ Cons (PatVar var) pats'

instantiatePats1 :: Term Semantics b -> Patterns (Scoped b) a -> Some (Patterns b)
instantiatePats1 t ps = ps >>>= \v -> case v of
    Bound  -> t
    Free b -> return b

instantiatePatsAndLift1 :: C.Ctx s f b c -> Term Semantics c -> Patterns (Scoped b) a -> Some (Patterns c)
instantiatePatsAndLift1 ctx t ps = ps >>>= \v -> case v of
    Bound  -> t
    Free b -> return (C.liftBase ctx b)

instantiatePatsAndLift :: C.Ctx s f b c -> C.Ctx s f b d -> [Term Semantics d] -> Patterns c a -> Some (Patterns d)
instantiatePatsAndLift ctx1 ctx2 terms pats = pats >>>= go ctx1 ctx2 terms
  where
    go :: C.Ctx s f b c -> C.Ctx s f b d -> [Term Semantics d] -> c -> Term Semantics d
    go C.Nil ctx2 _ b = return (C.liftBase ctx2 b)
    go C.Snoc{} _ (t:_) Bound = t
    go (C.Snoc ctx1 _ _) ctx2 (_:ts) (Free c) = go ctx1 ctx2 ts c
    go _ _ _ _ = error "instantiatePatsAndLift"

instantiatePats :: C.Ctx s f Void b -> [Term Semantics d] -> Patterns b a -> Some (Patterns d)
instantiatePats ctx terms pats = pats >>>= go ctx terms
  where
    go :: C.Ctx s f Void b -> [Term Semantics d] -> b -> Term Semantics d
    go C.Nil _ b = absurd b
    go C.Snoc{} (t:_) Bound = t
    go (C.Snoc ctx _ _) (_:ts) (Free b) = go ctx ts b
    go _ _ _ = error "instantiatePats"

bindClause :: Clause b -> (b -> Term Semantics c) -> Clause c
bindClause (Clause Nil term) k = Clause Nil (term >>= k)
bindClause (Clause (Cons (PatDCon v i n cs params ps) pats) term) k = case bindClause (Clause (ps +++ pats) term) k of
    Clause pats' term' -> case patternsSplitAt pats' (patternsLength ps) of
        Split pats1 pats2 -> Clause (Cons (PatDCon v i n cs (map (>>= k) params) pats1) pats2) term'
bindClause (Clause (Cons (PatPCon pat) pats) term) k = case bindClause (Clause (Cons pat pats) term) k of
    Clause (Cons pat' pats') term' -> Clause (Cons (PatPCon pat') pats') term'
    _ -> error "bindClause"
bindClause (Clause (Cons (PatICon con) pats) term) k = case bindClause (Clause pats term) k of
    Clause pats' term' -> Clause (Cons (PatICon con) pats') term'
bindClause (Clause (Cons (PatVar var) pats) term) k =
    case (Clause pats term `bindClause` \v -> case v of
                                                Bound  -> return Bound
                                                Free b -> fmap Free (k b)) of
        Clause pats' term' -> Clause (Cons (PatVar var) pats') term'

instantiateClause :: C.Ctx s f Void b -> [Term Semantics d] -> Clause b -> Clause d
instantiateClause ctx terms cl = bindClause cl (go ctx terms)
  where
    go :: C.Ctx s f Void b -> [Term Semantics d] -> b -> Term Semantics d
    go C.Nil _ b = absurd b
    go C.Snoc{} (t:_) Bound = t
    go (C.Snoc ctx _ _) (_:ts) (Free b) = go ctx ts b
    go _ _ _ = error "instantiatePats"

patternToTerm :: Pattern b a -> Term Int String
patternToTerm (PatDCon _ i _ _ _ ps) = Apply i (patternsToTerms ps)
patternToTerm (PatPCon p) = Apply 0 [patternToTerm p]
patternToTerm (PatICon ILeft) = capply 0
patternToTerm (PatICon IRight) = capply 1
patternToTerm (PatVar v) = cvar v

patternsToTerms :: Patterns b a -> [Term Int String]
patternsToTerms Nil = []
patternsToTerms (Cons p ps) = patternToTerm p : patternsToTerms ps

patternToTermVar :: Pattern b a -> Term Int a
patternToTermVar (PatDCon _ i _ _ _ ps) = Apply i (patternsToTermsVar ps)
patternToTermVar (PatPCon p) = Apply 0 [patternToTermVar p]
patternToTermVar (PatICon ILeft) = capply 0
patternToTermVar (PatICon IRight) = capply 1
patternToTermVar (PatVar v) = cvar Bound

patternsToTermsVar :: Patterns b a -> [Term Int a]
patternsToTermsVar Nil = []
patternsToTermsVar (Cons p ps) = fmap (liftBasePats ps) (patternToTermVar p) : patternsToTermsVar ps

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
