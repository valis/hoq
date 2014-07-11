{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Termination
    ( checkTermination
    ) where

import Control.Monad.State
import Data.Traversable(sequenceA)

import Syntax.Term
import Syntax.ErrorDoc
import TypeChecking.Context

checkTermination :: String -> [PatternC] -> Closed (Scope String Term) -> [EMsg Term]
checkTermination name pats (Closed scope) = map msg $ case scopeToCtx Nil scope of
    TermInCtx ctx term -> collectFunCalls name [] term >>= \(lc,mts) -> case mts of
        Nothing -> [lc]
        Just ts -> if evalState (checkTerms ctx pats ts) 0 == LT then [] else [lc]
  where
    msg :: (Int,Int) -> EMsg Term
    msg lc = emsgLC lc "Termination check failed" enull

checkTerm :: Ctx String Term String a -> PatternC -> Term a -> State Int Ordering
checkTerm ctx (PatternI con) (ICon con') | con == con' = return EQ
checkTerm ctx (PatternVar _) (Var v) = do
    s <- get
    put (s + 1)
    return $ if s == lengthCtx ctx - 1 - index ctx v then EQ else GT
  where
    index :: Ctx String Term b a -> a -> Int
    index Nil _ = 0
    index (Snoc ctx _ _) Bound = 0
    index (Snoc ctx _ _) (Free a) = index ctx a + 1
checkTerm ctx (Pattern (PatternCon i _ _ _) pats) term = do
    s <- get
    results <- mapM (\pat -> checkTerm ctx pat term) pats
    let result = minimum (GT:results)
    if result /= GT then return LT else case collect term of
        Con i' _ _ _ terms | i == i' -> do
            put s
            checkTerms ctx pats terms
        _ -> return GT
checkTerm _ _ _ = return GT

checkTerms :: Ctx String Term String a -> [PatternC] -> [Term a] -> State Int Ordering
checkTerms _ [] _ = return EQ
checkTerms _ _ [] = return EQ
checkTerms ctx (pat:pats) (term:terms) = do
    r <- checkTerm ctx pat term
    case r of
        EQ -> checkTerms ctx pats terms
        _  -> return r

data TermInCtx s f b = forall a. TermInCtx (Ctx s f b a) (f a)

scopeToCtx :: Ctx s f b a -> Scope s f a -> TermInCtx s f b
scopeToCtx ctx (ScopeTerm t) = TermInCtx ctx t
scopeToCtx ctx (Scope s t) = scopeToCtx (Snoc ctx s $ error "") t

collectFunCalls :: String -> [Term a] -> Term a -> [((Int,Int), Maybe [Term a])]
collectFunCalls _ _  Var{} = []
collectFunCalls name ts (App e1 e2) = collectFunCalls name (e2:ts) e1 ++ collectFunCalls name [] e2
collectFunCalls name _  (Lam (Scope1 _ e)) = map checkScoped $ collectFunCalls name [] e
collectFunCalls name _  (Pi (Type e _) s _) = collectFunCalls name [] e ++ go s
  where
    go :: Scope s Term a -> [((Int,Int), Maybe [Term a])]
    go (ScopeTerm t) = collectFunCalls name [] t
    go (Scope _   s) = map checkScoped (go s)
collectFunCalls name ts (Con _ lc name' _ as) =
    (if name == name' then [(lc, Just $ as ++ ts)] else []) ++ (as >>= collectFunCalls name [])
collectFunCalls name ts (FunCall lc name' _) = if name == name' then [(lc, Just ts)] else []
collectFunCalls name _  FunSyn{} = []
collectFunCalls name _  (DataType _ _ as) = as >>= collectFunCalls name []
collectFunCalls name _  Universe{} = []
collectFunCalls name _  Interval = []
collectFunCalls name _  ICon{} = []
collectFunCalls name _  (Path _ me1 es) = maybe [] (collectFunCalls name []) me1 ++ (es >>= collectFunCalls name [])
collectFunCalls name _  (PCon me) = maybe [] (collectFunCalls name []) me
collectFunCalls name _  (At _ _ e3 e4) = collectFunCalls name [] e3 ++ collectFunCalls name [] e4
collectFunCalls name _  (Coe es) = es >>= collectFunCalls name []
collectFunCalls name _  (Iso es) = es >>= collectFunCalls name []
collectFunCalls name _  (Squeeze es) = es >>= collectFunCalls name []

checkScoped :: ((Int,Int), Maybe [Term (Scoped a)]) -> ((Int,Int), Maybe [Term a])
checkScoped (lc, mt) = (lc, mt >>= \terms -> mapM (scopedToMaybe . sequenceA) terms)

scopedToMaybe :: Scoped a -> Maybe a
scopedToMaybe Bound = Nothing
scopedToMaybe (Free a) = Just a
