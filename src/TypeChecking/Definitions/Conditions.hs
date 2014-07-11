{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Conditions
    ( checkConditions
    ) where

import Control.Monad
import Control.Monad.State
import Data.Maybe

import Syntax.Term
import Syntax.ErrorDoc
import Syntax.PrettyPrinter
import TypeChecking.Context
import Normalization

checkConditions :: (Int,Int) -> Closed Term -> [([PatternC], Closed (Scope String Term))] -> [EMsg Term]
checkConditions lc func cs =
    maybeToList $ msum $ map (\(p, scope) -> fmap (uncurry msg) $ checkPatterns func (map fst cs) p scope) cs
  where
    msg :: Scope String Term String -> Scope String Term String -> EMsg Term
    msg t1 t2 = emsgLC lc "Conditions check failed:" $
        scopeToEDoc t1 <+> pretty "is not equal to" <+> scopeToEDoc t2
    
    scopeToEDoc :: Scope String Term String -> EDoc Term
    scopeToEDoc t = epretty $ fmap pretty $ let (_,_,_,t') = scopeToTerm [] id t in t'

data TermInCtx  f b = forall a. TermInCtx  (Ctx String f b a) (f a)
data TermsInCtx f b = forall a. TermsInCtx (Ctx String f b a) [f a]
data TermsInCtx2 f b = forall a. TermsInCtx2 (Ctx String f b a) [f a] [f a]

checkPatterns :: Closed Term -> [[PatternC]] -> [PatternC] -> Closed (Scope String Term)
    -> Maybe (Scope String Term String, Scope String Term String)
checkPatterns (Closed func) cs pats (Closed scope) =
    listToMaybe $ findSuspiciousPairs cs pats >>= \(TermsInCtx2 ctx terms terms') ->
        let nscope1 = nfAppsScope $ abstractTermInCtx ctx (apps func terms)
            nscope2 = abstractTermInCtx ctx (instantiate terms' scope)
        in if nfScope nscope1 == nfScope nscope2 then [] else [(nscope1,nscope2)]
  where
    nfApps :: Eq a => Term a -> Term a
    nfApps (App a b) = App (nfApps a) (nf WHNF b)
    nfApps (Con i lc name conds terms) = Con i lc name conds $ map (nf WHNF) terms
    nfApps t = t
    
    nfAppsScope :: Eq a => Scope String Term a -> Scope String Term a
    nfAppsScope (ScopeTerm t) = ScopeTerm (nfApps t)
    nfAppsScope (Scope v t) = Scope v (nfAppsScope t)

findSuspiciousPairs :: [[PatternC]] -> [PatternC] -> [TermsInCtx2 Term b]
findSuspiciousPairs _ [] = []
findSuspiciousPairs cs (pat@(PatternI con) : pats) = map ext $ findSuspiciousPairs (mapTail pat cs) pats
  where ext (TermsInCtx2 ctx terms1 terms2) = (TermsInCtx2 ctx (ICon con : terms1) terms2)
findSuspiciousPairs cs (pat@(PatternVar var) : pats) =
    check ILeft ++ check IRight ++ map ext (findSuspiciousPairs (mapTail pat cs) pats)
  where
    ext (TermsInCtx2 ctx terms1 terms2) = TermsInCtx2 (Snoc ctx var $ error "") (Var Bound : map (fmap Free) terms1)
                                                                                (Var Bound : map (fmap Free) terms2)
    check con = if null $ filter (\p -> p == PatternI con) (mapHead cs)
        then []
        else case patternsToTerms pats of
            TermsInCtx ctx terms -> [TermsInCtx2 ctx (ICon con : terms) (ICon con : ctxToVars ctx)]
findSuspiciousPairs cs (pat@(Pattern con@(PatternCon i _ name conds) args) : pats) =
    (conds >>= \(cond,_) -> case unifyPatternLists args cond of
        Nothing -> []
        Just args' -> [ext0 args $ patternsToTerms args']) ++
    map ext1 (findSuspiciousPairs cs' args) ++ case patternsToTerms args of
        TermsInCtx ctx terms -> map (ext2 ctx terms) (findSuspiciousPairs (mapTail pat cs) pats)
  where
    cs' = cs >>= \as -> case as of
            Pattern con' args' : _ | con == con' -> [args']
            _ -> []
    
    ext0 :: [PatternC] -> TermsInCtx Term b -> TermsInCtx2 Term b
    ext0 args (TermsInCtx ctx terms) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx')
            (fmap (liftBase ctx') (Con i (0,0) name conds $ substPatterns args terms) : terms')
            (map (fmap $ liftBase ctx') terms ++ ctxToVars ctx')
    
    ext1 :: TermsInCtx2 Term b -> TermsInCtx2 Term b
    ext1 (TermsInCtx2 ctx terms1 terms2) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Con i (0,0) name conds terms1) : terms')
                                                             (map (fmap $ liftBase ctx') terms2 ++ ctxToVars ctx')
    
    ext2 :: Ctx String Term a b -> [Term b] -> TermsInCtx2 Term b -> TermsInCtx2 Term a
    ext2 ctx terms (TermsInCtx2 ctx' terms1 terms2) =
        TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Con i (0,0) name conds terms) : terms1)
                                   (map (fmap $ liftBase ctx') (ctxToVars ctx) ++ terms2)

unifyPatterns :: PatternC -> PatternC -> Maybe [PatternC]
unifyPatterns (PatternI con) (PatternI con') | con == con' = Just []
unifyPatterns (PatternVar _) p = Just [p]
unifyPatterns p (PatternVar _) = Just (varList p)
unifyPatterns (Pattern con pats) (Pattern con' pats') | con == con' = unifyPatternLists pats pats'
unifyPatterns _ _ = Nothing

unifyPatternLists :: [PatternC] -> [PatternC] -> Maybe [PatternC]
unifyPatternLists pats pats' = fmap concat $ sequence (zipWith unifyPatterns pats pats')

varList :: Pattern c -> [Pattern c]
varList (PatternI _) = []
varList pat@(PatternVar _) = [pat]
varList (Pattern _ pats) = pats >>= varList

substPatterns :: [PatternC] -> [Term a] -> [Term a]
substPatterns pats terms = evalState (mapM substPattern pats) terms
  where
    substPattern :: PatternC -> State [Term a] (Term a)
    substPattern (PatternI con) = return (ICon con)
    substPattern (PatternVar _) = do
        term:terms <- get
        put terms
        return term
    substPattern (Pattern (PatternCon i _ name conds) pats) = do
        terms <- mapM substPattern pats
        return (Con i (0,0) name conds terms)

patternToTerm :: PatternC -> TermInCtx Term a
patternToTerm (PatternI con) = TermInCtx Nil (ICon con)
patternToTerm (PatternVar var) = TermInCtx (Snoc Nil var $ error "") (Var Bound)
patternToTerm (Pattern (PatternCon i _ name conds) pats) = case patternsToTerms pats of
    TermsInCtx ctx' terms -> TermInCtx ctx' $ Con i (0,0) name conds terms

patternsToTerms :: [PatternC] -> TermsInCtx Term a
patternsToTerms [] = TermsInCtx Nil []
patternsToTerms (pat:pats) = case patternToTerm pat of
    TermInCtx ctx' term -> case patternsToTerms pats of
        TermsInCtx ctx'' terms -> TermsInCtx (ctx' +++ ctx'') $ fmap (liftBase ctx'') term : terms

ctxToVars :: Ctx s f b a -> [Term a]
ctxToVars = reverse . go
  where
    go :: Ctx s f b a -> [Term a]
    go Nil = []
    go (Snoc ctx _ _) = Var Bound : map (fmap Free) (go ctx)

mapHead :: [[a]] -> [a]
mapHead cs = cs >>= \as -> if null as then [] else [head as]

mapTail :: Eq a => a -> [[a]] -> [[a]]
mapTail a cs = cs >>= \as -> if null as || not (head as == a) then [] else [tail as]
