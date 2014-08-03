{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Conditions
    ( checkConditions
    ) where

import Control.Monad
import Control.Monad.State
import Data.Maybe
import Data.Bifunctor

import qualified Syntax as S
import Semantics
import Semantics.Value
import Syntax.ErrorDoc
import TypeChecking.Context
import Normalization

checkConditions :: S.Posn -> Closed (Term Semantics) -> [([PatternC String], Closed (Scope String (Term Semantics)))] -> [EMsg (Term S.Syntax)]
checkConditions lc func cs =
    maybeToList $ msum $ map (\(p, scope) -> fmap (uncurry msg) $ checkPatterns func (map fst cs) p scope) cs
  where
    msg :: Scope String (Term Semantics) String -> Scope String (Term Semantics) String -> EMsg (Term S.Syntax)
    msg t1 t2 = emsgLC lc "Conditions check failed:" $ scopeToEDoc t1 <+> pretty "is not equal to" <+> scopeToEDoc t2
    
    scopeToEDoc :: Scope String (Term Semantics) String -> EDoc (Term S.Syntax)
    scopeToEDoc t = epretty $ bimap syntax pretty (scopeToTerm t)

scopeToTerm :: Scope String (Term p) String -> Term p String
scopeToTerm (ScopeTerm t) = t
scopeToTerm (Scope v s) = scopeToTerm $ instantiateScope (Var v) s

data TermInCtx  f b = forall a. TermInCtx  (Ctx String f b a) (f a)
data TermsInCtx f b = forall a. TermsInCtx (Ctx String f b a) [f a]
data TermsInCtx2 f b = forall a. TermsInCtx2 (Ctx String f b a) [f a] [f a]

nfScope :: Eq a => Scope s (Term Semantics) a -> Scope s (Term Semantics) a
nfScope (ScopeTerm t) = ScopeTerm (nf NF t)
nfScope (Scope v s) = Scope v (nfScope s)

checkPatterns :: Closed (Term Semantics) -> [[PatternC String]] -> [PatternC String] -> Closed (Scope String (Term Semantics))
    -> Maybe (Scope String (Term Semantics) String, Scope String (Term Semantics) String)
checkPatterns (Closed func) cs pats (Closed scope) =
    listToMaybe $ findSuspiciousPairs cs pats >>= \(TermsInCtx2 ctx terms terms') ->
        let nscope1 = nfAppsScope $ abstractTermInCtx ctx (apps func terms)
            nscope2 = abstractTermInCtx ctx (instantiate terms' scope)
        in if nfScope nscope1 == nfScope nscope2 then [] else [(nscope1,nscope2)]
  where
    nfApps :: Eq a => Term Semantics a -> Term Semantics a
    nfApps (Apply t@(Semantics _ App) [a, b]) = Apply t [nfApps a, nf WHNF b]
    nfApps t = t
    
    nfAppsScope :: Eq a => Scope String (Term Semantics) a -> Scope String (Term Semantics) a
    nfAppsScope (ScopeTerm t) = ScopeTerm (nfApps t)
    nfAppsScope (Scope v t) = Scope v (nfAppsScope t)

sterm :: SValue -> Term Semantics a
sterm = cterm . Semantics (error "")

findSuspiciousPairs :: [[PatternC String]] -> [PatternC String] -> [TermsInCtx2 (Term Semantics) b]
findSuspiciousPairs _ [] = []
findSuspiciousPairs cs (pat@(PatternEmpty _) : pats) = findSuspiciousPairs (mapTail pat cs) pats
findSuspiciousPairs cs (pat@(PatternI _ con) : pats) = map ext $ findSuspiciousPairs (mapTail pat cs) pats
  where ext (TermsInCtx2 ctx terms1 terms2) = (TermsInCtx2 ctx (sterm (ICon con) : terms1) terms2)
findSuspiciousPairs cs (pat@(PatternVar var) : pats) =
    check ILeft ++ check IRight ++ map ext (findSuspiciousPairs (mapTail pat cs) pats)
  where
    ext (TermsInCtx2 ctx terms1 terms2) = TermsInCtx2 (Snoc ctx var $ error "") (Var Bound : map (fmap Free) terms1)
                                                                                (Var Bound : map (fmap Free) terms2)
    check con = if null $ filter (== PatternI () con) (mapHead cs)
        then []
        else case patternsToTerms pats of
            TermsInCtx ctx terms -> [TermsInCtx2 ctx (sterm (ICon con) : terms) (sterm (ICon con) : ctxToVars ctx)]
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
    
    ext0 :: [PatternC String] -> TermsInCtx (Term Semantics) b -> TermsInCtx2 (Term Semantics) b
    ext0 args (TermsInCtx ctx terms) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx')
            (fmap (liftBase ctx') (capps (Semantics (error "") (Con i conds)) $ substPatterns args terms) : terms')
            (map (fmap $ liftBase ctx') terms ++ ctxToVars ctx')
    
    ext1 :: TermsInCtx2 (Term Semantics) b -> TermsInCtx2 (Term Semantics) b
    ext1 (TermsInCtx2 ctx terms1 terms2) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (capps (Semantics (error "") (Con i conds)) terms1) : terms')
                                                             (map (fmap $ liftBase ctx') terms2 ++ ctxToVars ctx')
    
    ext2 :: Ctx String (Term Semantics) a b -> [Term Semantics b] -> TermsInCtx2 (Term Semantics) b -> TermsInCtx2 (Term Semantics) a
    ext2 ctx terms (TermsInCtx2 ctx' terms1 terms2) =
        TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (capps (Semantics (error "") (Con i conds)) terms) : terms1)
                                   (map (fmap $ liftBase ctx') (ctxToVars ctx) ++ terms2)

unifyPatterns :: PatternC String -> PatternC String -> Maybe [PatternC String]
unifyPatterns (PatternI _ con) (PatternI _ con') | con == con' = Just []
unifyPatterns (PatternVar _) p = Just [p]
unifyPatterns p (PatternVar _) = Just (varList p)
unifyPatterns (Pattern con pats) (Pattern con' pats') | con == con' = unifyPatternLists pats pats'
unifyPatterns _ _ = Nothing

unifyPatternLists :: [PatternC String] -> [PatternC String] -> Maybe [PatternC String]
unifyPatternLists pats pats' = fmap concat $ sequence (zipWith unifyPatterns pats pats')

varList :: Pattern c p s -> [Pattern c p s]
varList PatternEmpty{} = []
varList PatternI{} = []
varList pat@(PatternVar _) = [pat]
varList (Pattern _ pats) = pats >>= varList

substPatterns :: [PatternC String] -> [Term Semantics a] -> [Term Semantics a]
substPatterns pats terms = evalState (mapM substPattern pats) terms
  where
    substPattern :: PatternC String -> State [Term Semantics a] (Term Semantics a)
    substPattern (PatternI _ con) = return $ sterm (ICon con)
    substPattern (PatternVar _) = do
        term:terms <- get
        put terms
        return term
    substPattern (PatternEmpty _) = do
        term:terms <- get
        put terms
        return term
    substPattern (Pattern (PatternCon i _ name conds) pats) = do
        terms <- mapM substPattern pats
        return $ capps (Semantics (error "") (Con i conds)) terms

patternToTerm :: PatternC String -> TermInCtx (Term Semantics) a
patternToTerm (PatternI _ con) = TermInCtx Nil $ sterm (ICon con)
patternToTerm (PatternEmpty _) = TermInCtx (Snoc Nil "_" $ error "") (Var Bound)
patternToTerm (PatternVar var) = TermInCtx (Snoc Nil var $ error "") (Var Bound)
patternToTerm (Pattern (PatternCon i _ name conds) pats) = case patternsToTerms pats of
    TermsInCtx ctx' terms -> TermInCtx ctx' $ capps (Semantics (error "") (Con i conds)) terms

patternsToTerms :: [PatternC String] -> TermsInCtx (Term Semantics) a
patternsToTerms [] = TermsInCtx Nil []
patternsToTerms (pat:pats) = case patternToTerm pat of
    TermInCtx ctx' term -> case patternsToTerms pats of
        TermsInCtx ctx'' terms -> TermsInCtx (ctx' +++ ctx'') $ fmap (liftBase ctx'') term : terms

mapHead :: [[a]] -> [a]
mapHead cs = cs >>= \as -> if null as then [] else [head as]

mapTail :: Eq a => a -> [[a]] -> [[a]]
mapTail a cs = cs >>= \as -> if null as || not (head as == a) then [] else [tail as]
