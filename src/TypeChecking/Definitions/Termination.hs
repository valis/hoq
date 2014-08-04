{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Termination
    ( checkTermination
    ) where

import Control.Monad.State

import qualified Syntax as S
import Semantics.Value
import Semantics
import Syntax.ErrorDoc
import TypeChecking.Context

checkTermination :: Either Int ID -> S.Posn -> [PatternC String] -> Closed (Term Semantics) -> [EMsg (Term S.Syntax)]
checkTermination name pos pats (Closed scope) = map msg $ case scopeToCtx Nil scope of
    TermInCtx ctx term -> collectFunCalls ctx name term >>= \mts -> case mts of
        TermsInCtx ctx' terms -> if evalState (checkTerms ctx' pats terms) 0 == LT then [] else [pos]
  where
    msg :: S.Posn -> EMsg (Term S.Syntax)
    msg pos = emsgLC pos "Termination check failed" enull

checkTerm :: Ctx String (Term Semantics) String a -> PatternC String -> Term Semantics a -> State Int Ordering
checkTerm _ (PatternI _ con) (Apply (Semantics _ (ICon con')) []) | con == con' = return EQ
checkTerm ctx (PatternVar _) (Var v []) = do
    s <- get
    put (s + 1)
    return $ if s == lengthCtx ctx - 1 - index ctx v then EQ else GT
  where
    index :: Ctx String (Term Semantics) b a -> a -> Int
    index Nil _ = 0
    index (Snoc ctx _ _) Bound = 0
    index (Snoc ctx _ _) (Free a) = index ctx a + 1
checkTerm ctx (Pattern (PatternCon i _ _ _) pats) term = do
    s <- get
    results <- mapM (\pat -> checkTerm ctx pat term) pats
    if minimum (GT:results) /= GT then return LT else case term of
        Apply (Semantics _ (Con i' _)) terms | i == i' -> do
            put s
            checkTerms ctx pats terms
        _ -> return GT
checkTerm _ _ _ = return GT

checkTerms :: Ctx String (Term Semantics) String a -> [PatternC String] -> [Term Semantics a] -> State Int Ordering
checkTerms _ [] _ = return EQ
checkTerms _ _ [] = return EQ
checkTerms ctx (pat:pats) (term:terms) = do
    r <- checkTerm ctx pat term
    case r of
        EQ -> checkTerms ctx pats terms
        _  -> return r

data TermInCtx  s f b = forall a. TermInCtx  (Ctx s f b a) (f a)
data TermsInCtx s f b = forall a. TermsInCtx (Ctx s f b a) [f a]

scopeToCtx :: Ctx s (Term Semantics) b a -> Term Semantics a -> TermInCtx s (Term Semantics) b
scopeToCtx ctx (Lambda t) = scopeToCtx (Snoc ctx (error "") $ error "") t
scopeToCtx ctx t = TermInCtx ctx t

collectFunCalls :: Ctx String (Term Semantics) b a -> Either Int ID
    -> Term Semantics a -> [TermsInCtx String (Term Semantics) b]
collectFunCalls ctx name (Lambda t) = collectFunCalls (Snoc ctx (error "") $ error "") name t
collectFunCalls ctx name (Var _ as) = as >>= collectFunCalls ctx name
collectFunCalls ctx name (Apply a as) = (case a of
    Semantics _ (Con name' _) | name == Left name' -> [TermsInCtx ctx as]
    Semantics _ (FunCall name' _) | name == Right name' -> [TermsInCtx ctx as]
    _ -> []) ++ (as >>= collectFunCalls ctx name)
