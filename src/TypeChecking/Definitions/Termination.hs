{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Termination
    ( checkTermination
    ) where

import Control.Monad.State

import Syntax
import Syntax.ErrorDoc
import TypeChecking.Context

checkTermination :: String -> [PatternC String] -> Closed (Scope String (Term Syntax)) -> [EMsg (Term Syntax)]
checkTermination name pats (Closed scope) = map msg $ case scopeToCtx Nil scope of
    TermInCtx ctx term -> collectFunCalls ctx name [] term >>= \(pos,mts) -> case mts of
        TermsInCtx ctx' terms -> if evalState (checkTerms ctx' pats terms) 0 == LT then [] else [pos]
  where
    msg :: Posn -> EMsg (Term Syntax)
    msg pos = emsgLC pos "Termination check failed" enull

checkTerm :: Ctx String (Term Syntax) String a -> PatternC String -> Term Syntax a -> State Int Ordering
checkTerm ctx (PatternI _ con) (Apply (ICon con') []) | con == con' = return EQ
checkTerm ctx (PatternVar _) (Var v) = do
    s <- get
    put (s + 1)
    return $ if s == lengthCtx ctx - 1 - index ctx v then EQ else GT
  where
    index :: Ctx String (Term Syntax) b a -> a -> Int
    index Nil _ = 0
    index (Snoc ctx _ _) Bound = 0
    index (Snoc ctx _ _) (Free a) = index ctx a + 1
checkTerm ctx (Pattern (PatternCon i _ _ _) pats) term = do
    s <- get
    results <- mapM (\pat -> checkTerm ctx pat term) pats
    if minimum (GT:results) /= GT then return LT else case collect term of
        (Just (Con i' _ _), terms) | i == i' -> do
            put s
            checkTerms ctx pats terms
        _ -> return GT
checkTerm _ _ _ = return GT

checkTerms :: Ctx String (Term Syntax) String a -> [PatternC String] -> [Term Syntax a] -> State Int Ordering
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

collectFunCalls :: Ctx String (Term Syntax) b a -> String -> [Term Syntax a]
    -> Term Syntax a -> [(Posn, TermsInCtx String (Term Syntax) b)]
collectFunCalls _ _ _ Var{} = []
collectFunCalls _ _ _ Lambda{} = []
collectFunCalls ctx name ps (Apply a as) = go ctx name ps a as
  where
    go :: Ctx String (Term Syntax) b a -> String -> [Term Syntax a]
        -> Syntax -> [Term Syntax a] -> [(Posn, TermsInCtx String (Term Syntax) b)]
    go ctx name ps App [t1,t2] = collectFunCalls ctx name (t2:ps) t1 ++ collectFunCalls ctx name [] t2
    go ctx name ps (Lam []) [t] = collectFunCalls ctx name ps t
    go ctx name _  (Lam (v:vs)) [Lambda (Scope1 t)] = go (Snoc ctx v $ error "") name [] (Lam vs) [t]
    go ctx name _  (Pi [] _ _) [t1,t2] = collectFunCalls ctx name [] t1 ++ collectFunCalls ctx name [] t2
    go ctx name _ (Pi (v:vs) l1 l2) [t1, Lambda (Scope1 t2)] = go (Snoc ctx v $ error "") name [] (Pi vs l1 l2) [fmap Free t1, t2]
    go ctx name ps (Con _ (PIdent pos name') _) [] = if name == name' then [(pos, TermsInCtx ctx ps)] else []
    go ctx name ps (FunCall (PIdent pos name') _) [] = if name == name' then [(pos, TermsInCtx ctx ps)] else []
    go ctx name _ _ as = as >>= collectFunCalls ctx name []
