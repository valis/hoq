{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Termination
    ( checkTermination
    ) where

import Control.Monad.State

import Syntax
import Syntax.ErrorDoc
import TypeChecking.Context

checkTermination :: String -> [PatternC p String] -> Closed (Scope String (Term p)) -> [EMsg (Term p)]
checkTermination name pats (Closed scope) = map msg $ case scopeToCtx Nil scope of
    TermInCtx ctx term -> collectFunCalls ctx name [] term >>= \(pos,mts) -> case mts of
        TermsInCtx ctx ts -> if evalState (checkTerms ctx pats ts) 0 == LT then [] else [pos]
  where
    msg :: Posn -> EMsg (Term p)
    msg pos = emsgLC pos "Termination check failed" enull

checkTerm :: Ctx String (Term p) String a -> PatternC p String -> Term p a -> State Int Ordering
checkTerm ctx (PatternI _ con) (ICon _ con') | con == con' = return EQ
checkTerm ctx (PatternVar _) (Var v) = do
    s <- get
    put (s + 1)
    return $ if s == lengthCtx ctx - 1 - index ctx v then EQ else GT
  where
    index :: Ctx String (Term p) b a -> a -> Int
    index Nil _ = 0
    index (Snoc ctx _ _) Bound = 0
    index (Snoc ctx _ _) (Free a) = index ctx a + 1
checkTerm ctx (Pattern (PatternCon i _ _ _) pats) term = do
    s <- get
    results <- mapM (\pat -> checkTerm ctx pat term) pats
    if minimum (GT:results) /= GT then return LT else case collect term of
        Con _ i' _ _ terms | i == i' -> do
            put s
            checkTerms ctx pats terms
        _ -> return GT
checkTerm _ _ _ = return GT

checkTerms :: Ctx String (Term p) String a -> [PatternC p String] -> [Term p a] -> State Int Ordering
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

collectFunCalls :: Ctx String (Term p) b a -> String -> [Term p a]
    -> Term p a -> [(Posn, TermsInCtx String (Term p) b)]
collectFunCalls _ _ _  Var{} = []
collectFunCalls ctx name ts (App e1 e2) = collectFunCalls ctx name (e2:ts) e1 ++ collectFunCalls ctx name [] e2
collectFunCalls ctx name _  (Lam _ (Scope1 v e)) = collectFunCalls (Snoc ctx v $ error "") name [] e
collectFunCalls ctx name _  (Pi _ (Type e _) s _) = collectFunCalls ctx name [] e ++ go ctx s
  where
    go :: Ctx String (Term p) b a -> Scope String (Term p) a -> [(Posn, TermsInCtx String (Term p) b)]
    go ctx (ScopeTerm t) = collectFunCalls ctx name [] t
    go ctx (Scope v t) = go (Snoc ctx v $ error "") t
collectFunCalls ctx name ts (Con _ _ (PIdent pos name') _ as) =
    (if name == name' then [(pos, TermsInCtx ctx $ as ++ ts)] else []) ++ (as >>= collectFunCalls ctx name [])
collectFunCalls ctx name ts (FunCall _ (PIdent pos name') _) = if name == name' then [(pos, TermsInCtx ctx ts)] else []
collectFunCalls ctx name _  FunSyn{} = []
collectFunCalls ctx name _  (DataType _ _ _ as) = as >>= collectFunCalls ctx name []
collectFunCalls ctx name _  Universe{} = []
collectFunCalls ctx name _  Interval{} = []
collectFunCalls ctx name _  ICon{} = []
collectFunCalls ctx name _  (Path _ _ me1 es) =
    maybe [] (collectFunCalls ctx name [] . fst) me1 ++ (es >>= collectFunCalls ctx name [])
collectFunCalls ctx name _  (PCon _ me) = maybe [] (collectFunCalls ctx name []) me
collectFunCalls ctx name _  (At _ e3 e4) = collectFunCalls ctx name [] e3 ++ collectFunCalls ctx name [] e4
collectFunCalls ctx name _  (Coe _ es) = es >>= collectFunCalls ctx name []
collectFunCalls ctx name _  (Iso _ es) = es >>= collectFunCalls ctx name []
collectFunCalls ctx name _  (Squeeze _ es) = es >>= collectFunCalls ctx name []
