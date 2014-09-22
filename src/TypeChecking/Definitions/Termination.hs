{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Termination
    ( checkTermination, CT(..), PatInCtx(..)
    ) where

import qualified Syntax as S
import Semantics.Value
import Semantics
import Syntax.ErrorDoc
import TypeChecking.Context
import TypeChecking.Expressions.Utils

data CT a = Constructor Int | Function ID | Variable a deriving Eq

instance Functor CT where
    fmap _ (Constructor i) = Constructor i
    fmap _ (Function i) = Function i
    fmap f (Variable a) = Variable (f a)

data PatInCtx  = forall a. Eq a => PatInCtx (CT a) [Term Int a] (Term Semantics a)
data PatsInCtx = forall a. Eq a => PatsInCtx       [Term Int a] [Term Semantics a]

checkTermination :: S.Posn -> [PatInCtx] -> [Error]
checkTermination _ [] = []
checkTermination pos clauses = go $ clauses >>= \(PatInCtx name pats term) ->
    map (\(TermsInCtx ctx terms) -> PatsInCtx (map (fmap $ liftBase ctx) pats) terms) (collectFunCalls Nil name term)
  where
    go tc = if any isEmpty tc
            then [Error Other $ emsgLC pos "Termination check failed" enull]
            else if all (\(PatsInCtx pats terms) -> checkTerms pats terms == LT) tc
                 then []
                 else go $ map (\(PatsInCtx pats terms) -> PatsInCtx (tail pats) $ tail terms) tc
    
    isEmpty (PatsInCtx [] _) = True
    isEmpty (PatsInCtx _ []) = True
    isEmpty _ = False

checkTerm :: Eq a => Term Int a -> Term Semantics a -> Ordering
checkTerm (Apply con _) (Apply (Semantics _ (ICon con')) []) | con == iConToInt con' = EQ
  where
    iConToInt ILeft  = 0
    iConToInt IRight = 1
checkTerm (Var a []) (Var a' []) = if a == a' then EQ else GT
checkTerm (Apply i pats) term =
    if minimum (GT : map (\pat -> checkTerm pat term) pats) /= GT
    then LT
    else case term of
        Apply (Semantics _ (DCon i' k _)) terms | i == i' -> checkTerms pats (drop k terms)
        _ -> GT
checkTerm _ _ = GT

checkTerms :: Eq a => [Term Int a] -> [Term Semantics a] -> Ordering
checkTerms [] _ = EQ
checkTerms _ [] = GT
checkTerms (pat:pats) (term:terms) = case checkTerm pat term of
    EQ -> checkTerms pats terms
    r  -> r

data TermsInCtx s f b = forall a. Eq a => TermsInCtx (Ctx s f b a) [Term Semantics a]

collectFunCalls :: Eq a => Ctx String f b a -> CT a -> Term Semantics a -> [TermsInCtx String f b]
collectFunCalls ctx name (Lambda t) = collectFunCalls (Snoc ctx (error "") $ error "") (fmap Free name) t
collectFunCalls ctx name (Var a as) = (if name == Variable a then [TermsInCtx ctx as] else [])
    ++ (as >>= collectFunCalls ctx name)
collectFunCalls ctx name (Apply a as) = (case a of
    Semantics _ (DCon name' _ _) | name == Constructor name' -> [TermsInCtx ctx as]
    Semantics _ (FunCall name' _) | name == Function name' -> [TermsInCtx ctx as]
    _ -> []) ++ (as >>= collectFunCalls ctx name)
