{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Termination
    ( checkTermination, CT(..)
    ) where

import Control.Monad.State
import Data.Foldable(toList)

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

checkTermination :: Eq a => CT a -> S.Posn -> [Term Int s] -> Ctx String f b a -> Term Semantics a -> [Error]
checkTermination name pos pats ctx term = map msg $ collectFunCalls ctx name term >>= \mts -> case mts of
    TermsInCtx ctx' terms -> if evalState (checkTerms ctx' pats terms) (length (pats >>= toList) - 1) == LT then [] else [pos]
  where
    msg :: S.Posn -> Error
    msg pos = Error Other $ emsgLC pos "Termination check failed" enull

checkTerm :: Ctx String f b a -> Term Int s -> Term Semantics a -> State Int Ordering
checkTerm _ (Apply con _) (Apply (Semantics _ (ICon con')) []) | con == iConToInt con' = return EQ
  where
    iConToInt ILeft  = 0
    iConToInt IRight = 1
checkTerm ctx Var{} (Var v []) = do
    s <- get
    put (s - 1)
    return $ if s == index ctx v then EQ else GT
  where
    index :: Ctx String f b a -> a -> Int
    index Nil _ = 0
    index (Snoc ctx _ _) Bound = 0
    index (Snoc ctx _ _) (Free a) = index ctx a + 1
checkTerm ctx (Apply i pats) term = do
    s <- get
    results <- mapM (\pat -> checkTerm ctx pat term) pats
    if minimum (GT:results) /= GT then return LT else case term of
        Apply (Semantics _ (DCon i' k _)) terms | i == i' -> do
            put s
            checkTerms ctx pats (drop k terms)
        _ -> return GT
checkTerm _ _ _ = return GT

checkTerms :: Ctx String f b a -> [Term Int s] -> [Term Semantics a] -> State Int Ordering
checkTerms _ [] _ = return EQ
checkTerms _ _ [] = return EQ
checkTerms ctx (pat:pats) (term:terms) = do
    r <- checkTerm ctx pat term
    case r of
        EQ -> checkTerms ctx pats terms
        _  -> return r

data TermInCtx  s f b = forall a. TermInCtx  (Ctx s f b a) (Term Semantics a)
data TermsInCtx s f b = forall a. TermsInCtx (Ctx s f b a) [Term Semantics a]

collectFunCalls :: Eq a => Ctx String f b a -> CT a -> Term Semantics a -> [TermsInCtx String f b]
collectFunCalls ctx name (Lambda t) = collectFunCalls (Snoc ctx (error "") $ error "") (fmap Free name) t
collectFunCalls ctx name (Var a as) = (if name == Variable a then [TermsInCtx ctx as] else [])
    ++ (as >>= collectFunCalls ctx name)
collectFunCalls ctx name (Apply a as) = (case a of
    Semantics _ (DCon name' _ _) | name == Constructor name' -> [TermsInCtx ctx as]
    Semantics _ (FunCall name' _) | name == Function name' -> [TermsInCtx ctx as]
    _ -> []) ++ (as >>= collectFunCalls ctx name)
