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

checkTermination :: Either Int ID -> S.Posn -> [PatternC String] -> Closed (Scope String (Term Semantics)) -> [EMsg (Term S.Syntax)]
checkTermination name pos pats (Closed scope) = map msg $ case scopeToCtx Nil scope of
    TermInCtx ctx term -> collectFunCalls ctx name [] term >>= \mts -> case mts of
        TermsInCtx ctx' terms -> if evalState (checkTerms ctx' pats terms) 0 == LT then [] else [pos]
  where
    msg :: S.Posn -> EMsg (Term S.Syntax)
    msg pos = emsgLC pos "Termination check failed" enull

checkTerm :: Ctx String (Term Semantics) String a -> PatternC String -> Term Semantics a -> State Int Ordering
checkTerm _ (PatternI _ con) (Apply (Semantics _ (ICon con')) []) | con == con' = return EQ
checkTerm ctx (PatternVar _) (Var v) = do
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
    if minimum (GT:results) /= GT then return LT else case collect term of
        (Just (Semantics _ (Con i' _)), terms) | i == i' -> do
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

scopeToCtx :: Ctx s f b a -> Scope s f a -> TermInCtx s f b
scopeToCtx ctx (ScopeTerm t) = TermInCtx ctx t
scopeToCtx ctx (Scope s t) = scopeToCtx (Snoc ctx s $ error "") t

collectFunCalls :: Ctx String (Term Semantics) b a -> Either Int ID -> [Term Semantics a]
    -> Term Semantics a -> [TermsInCtx String (Term Semantics) b]
collectFunCalls ctx name ps (Apply a as) = go ctx ps a as
  where
    go :: Ctx String (Term Semantics) b a -> [Term Semantics a]
        -> Semantics -> [Term Semantics a] -> [TermsInCtx String (Term Semantics) b]
    go ctx ps (Semantics _ App) [t1,t2] = collectFunCalls ctx name (t2:ps) t1 ++ collectFunCalls ctx name [] t2
    go ctx _ s@(Semantics _ Lam) [Lambda (Scope1 t)] = go (Snoc ctx (error "") $ error "") [] s [t]
    go ctx ps (Semantics _ Lam) [t] = collectFunCalls ctx name ps t
    go ctx _ s@(Semantics _ Pi{}) [t1, Lambda (Scope1 t2)] = go (Snoc ctx (error "") $ error "") [] s [fmap Free t1, t2]
    go ctx _ (Semantics _ Pi{}) [t1,t2] = collectFunCalls ctx name [] t1 ++ collectFunCalls ctx name [] t2
    go ctx ps (Semantics _ (Con name' _)) [] = if name == Left name' then [TermsInCtx ctx ps] else []
    go ctx ps (Semantics _ (FunCall name' _)) [] = if name == Right name' then [TermsInCtx ctx ps] else []
    go ctx _ _ as = as >>= collectFunCalls ctx name []
collectFunCalls _ _ _ _ = []
