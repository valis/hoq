{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Conditions
    ( checkConditions
    ) where

import Control.Monad
import Control.Monad.State
import Data.Maybe

import Syntax
import Syntax.ErrorDoc
import TypeChecking.Context
import Normalization

checkConditions :: Posn -> Closed (Term Syntax) -> [([PatternC String], Closed (Scope String (Term Syntax)))] -> [EMsg (Term Syntax)]
checkConditions lc func cs =
    maybeToList $ msum $ map (\(p, scope) -> fmap (uncurry msg) $ checkPatterns func (map fst cs) p scope) cs
  where
    msg :: Scope String (Term Syntax) String -> Scope String (Term Syntax) String -> EMsg (Term Syntax)
    msg t1 t2 = emsgLC lc "Conditions check failed:" $
        scopeToEDoc t1 <+> pretty "is not equal to" <+> scopeToEDoc t2
    
    scopeToEDoc :: Scope String (Term Syntax) String -> EDoc (Term Syntax)
    scopeToEDoc t = epretty $ fmap pretty (scopeToTerm t)

scopeToTerm :: Scope String (Term p) String -> Term p String
scopeToTerm (ScopeTerm t) = t
scopeToTerm (Scope v s) = scopeToTerm $ instantiateScope (Var v) s

data TermInCtx  f b = forall a. TermInCtx  (Ctx String f b a) (f a)
data TermsInCtx f b = forall a. TermsInCtx (Ctx String f b a) [f a]
data TermsInCtx2 f b = forall a. TermsInCtx2 (Ctx String f b a) [f a] [f a]

nfScope :: Eq a => Scope s (Term Syntax) a -> Scope s (Term Syntax) a
nfScope (ScopeTerm t) = ScopeTerm (nf NF t)
nfScope (Scope v s) = Scope v (nfScope s)

checkPatterns :: Closed (Term Syntax) -> [[PatternC String]] -> [PatternC String] -> Closed (Scope String (Term Syntax))
    -> Maybe (Scope String (Term Syntax) String, Scope String (Term Syntax) String)
checkPatterns (Closed func) cs pats (Closed scope) =
    listToMaybe $ findSuspiciousPairs cs pats >>= \(TermsInCtx2 ctx terms terms') ->
        let nscope1 = nfAppsScope $ abstractTermInCtx ctx (apps func terms)
            nscope2 = abstractTermInCtx ctx (instantiate terms' scope)
        in if nfScope nscope1 == nfScope nscope2 then [] else [(nscope1,nscope2)]
  where
    nfApps :: Eq a => Term Syntax a -> Term Syntax a
    nfApps (Apply App [a, b]) = Apply App [nfApps a, nf WHNF b]
    nfApps t = t
    
    nfAppsScope :: Eq a => Scope String (Term Syntax) a -> Scope String (Term Syntax) a
    nfAppsScope (ScopeTerm t) = ScopeTerm (nfApps t)
    nfAppsScope (Scope v t) = Scope v (nfAppsScope t)

findSuspiciousPairs :: [[PatternC String]] -> [PatternC String] -> [TermsInCtx2 (Term Syntax) b]
findSuspiciousPairs _ [] = []
findSuspiciousPairs cs (pat@(PatternEmpty _) : pats) = findSuspiciousPairs (mapTail pat cs) pats
findSuspiciousPairs cs (pat@(PatternI _ con) : pats) = map ext $ findSuspiciousPairs (mapTail pat cs) pats
  where ext (TermsInCtx2 ctx terms1 terms2) = (TermsInCtx2 ctx (cterm (ICon con) : terms1) terms2)
findSuspiciousPairs cs (pat@(PatternVar var) : pats) =
    check ILeft ++ check IRight ++ map ext (findSuspiciousPairs (mapTail pat cs) pats)
  where
    ext (TermsInCtx2 ctx terms1 terms2) = TermsInCtx2 (Snoc ctx var $ error "") (Var Bound : map (fmap Free) terms1)
                                                                                (Var Bound : map (fmap Free) terms2)
    check con = if null $ filter (== PatternI () con) (mapHead cs)
        then []
        else case patternsToTerms pats of
            TermsInCtx ctx terms -> [TermsInCtx2 ctx (cterm (ICon con) : terms) (cterm (ICon con) : ctxToVars ctx)]
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
    
    ext0 :: [PatternC String] -> TermsInCtx (Term Syntax) b -> TermsInCtx2 (Term Syntax) b
    ext0 args (TermsInCtx ctx terms) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx')
            (fmap (liftBase ctx') (capps (Con i (PIdent (0,0) name) conds) $ substPatterns args terms) : terms')
            (map (fmap $ liftBase ctx') terms ++ ctxToVars ctx')
    
    ext1 :: TermsInCtx2 (Term Syntax) b -> TermsInCtx2 (Term Syntax) b
    ext1 (TermsInCtx2 ctx terms1 terms2) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (capps (Con i (PIdent (0,0) name) conds) terms1) : terms')
                                                             (map (fmap $ liftBase ctx') terms2 ++ ctxToVars ctx')
    
    ext2 :: Ctx String (Term Syntax) a b -> [Term Syntax b] -> TermsInCtx2 (Term Syntax) b -> TermsInCtx2 (Term Syntax) a
    ext2 ctx terms (TermsInCtx2 ctx' terms1 terms2) =
        TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (capps (Con i (PIdent (0,0) name) conds) terms) : terms1)
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

substPatterns :: [PatternC String] -> [Term Syntax a] -> [Term Syntax a]
substPatterns pats terms = evalState (mapM substPattern pats) terms
  where
    substPattern :: PatternC String -> State [Term Syntax a] (Term Syntax a)
    substPattern (PatternI _ con) = return $ cterm (ICon con)
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
        return $ capps (Con i (PIdent (0,0) name) conds) terms

patternToTerm :: PatternC String -> TermInCtx (Term Syntax) a
patternToTerm (PatternI _ con) = TermInCtx Nil $ cterm (ICon con)
patternToTerm (PatternEmpty _) = TermInCtx (Snoc Nil "_" $ error "") (Var Bound)
patternToTerm (PatternVar var) = TermInCtx (Snoc Nil var $ error "") (Var Bound)
patternToTerm (Pattern (PatternCon i _ name conds) pats) = case patternsToTerms pats of
    TermsInCtx ctx' terms -> TermInCtx ctx' $ capps (Con i (PIdent (0,0) name) conds) terms

patternsToTerms :: [PatternC String] -> TermsInCtx (Term Syntax) a
patternsToTerms [] = TermsInCtx Nil []
patternsToTerms (pat:pats) = case patternToTerm pat of
    TermInCtx ctx' term -> case patternsToTerms pats of
        TermsInCtx ctx'' terms -> TermsInCtx (ctx' +++ ctx'') $ fmap (liftBase ctx'') term : terms

mapHead :: [[a]] -> [a]
mapHead cs = cs >>= \as -> if null as then [] else [head as]

mapTail :: Eq a => a -> [[a]] -> [[a]]
mapTail a cs = cs >>= \as -> if null as || not (head as == a) then [] else [tail as]
