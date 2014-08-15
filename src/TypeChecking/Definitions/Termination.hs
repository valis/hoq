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
import TypeChecking.Expressions.Utils

checkTermination :: Either Int ID -> S.Posn -> [Term (Con t) String] -> Closed (Term Semantics) -> [Error]
checkTermination name pos pats (Closed scope) = map msg $ case scopeToCtx Nil scope of
    TermInCtx ctx term -> collectFunCalls ctx name term >>= \mts -> case mts of
        TermsInCtx ctx' terms -> if evalState (checkTerms ctx' pats terms) 0 == LT then [] else [pos]
  where
    msg :: S.Posn -> Error
    msg pos = Error Other $ emsgLC pos "Termination check failed" enull

checkTerm :: Ctx String (Term Semantics) String a -> Term (Con t) String -> Term Semantics a -> State Int Ordering
checkTerm _ (Apply (ICon con) _) (Apply (Semantics _ (Con (ICon con'))) []) | con == con' = return EQ
checkTerm ctx Var{} (Var v []) = do
    s <- get
    put (s + 1)
    return $ if s == lengthCtx ctx - 1 - index ctx v then EQ else GT
  where
    index :: Ctx String (Term Semantics) b a -> a -> Int
    index Nil _ = 0
    index (Snoc ctx _ _) Bound = 0
    index (Snoc ctx _ _) (Free a) = index ctx a + 1
checkTerm ctx (Apply (DCon i _ _) pats) term = do
    s <- get
    results <- mapM (\pat -> checkTerm ctx pat term) pats
    if minimum (GT:results) /= GT then return LT else case term of
        Apply (Semantics _ (Con (DCon i' _ _))) terms | i == i' -> do
            put s
            checkTerms ctx pats terms
        _ -> return GT
checkTerm _ _ _ = return GT

checkTerms :: Ctx String (Term Semantics) String a -> [Term (Con t) String] -> [Term Semantics a] -> State Int Ordering
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
    Semantics _ (Con (DCon name' _ _)) | name == Left name' -> [TermsInCtx ctx as]
    Semantics _ (FunCall name' _) | name == Right name' -> [TermsInCtx ctx as]
    _ -> []) ++ (as >>= collectFunCalls ctx name)
