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

checkConditions :: Posn -> Closed (Term Posn)
    -> [([PatternC Posn String], Closed (Scope String Posn (Term Posn)))] -> [EMsg (Term Posn)]
checkConditions lc func cs =
    maybeToList $ msum $ map (\(p, scope) -> fmap (uncurry msg) $ checkPatterns func (map fst cs) p scope) cs
  where
    msg :: Scope String Posn (Term Posn) String -> Scope String Posn (Term Posn) String -> EMsg (Term Posn)
    msg t1 t2 = emsgLC lc "Conditions check failed:" $
        scopeToEDoc t1 <+> pretty "is not equal to" <+> scopeToEDoc t2
    
    scopeToEDoc :: Scope String Posn (Term Posn) String -> EDoc (Term Posn)
    scopeToEDoc t = epretty $ fmap pretty $ let (_,_,_,t') = scopeToTerm [] id t in t'

data TermInCtx  f b = forall a. TermInCtx  (Ctx String Posn f b a) (f a)
data TermsInCtx f b = forall a. TermsInCtx (Ctx String Posn f b a) [f a]
data TermsInCtx2 f b = forall a. TermsInCtx2 (Ctx String Posn f b a) [f a] [f a]

checkPatterns :: Closed (Term Posn) -> [[PatternC Posn String]] -> [PatternC Posn String] -> Closed (Scope String Posn (Term Posn))
    -> Maybe (Scope String Posn (Term Posn) String, Scope String Posn (Term Posn) String)
checkPatterns (Closed func) cs pats (Closed scope) =
    listToMaybe $ findSuspiciousPairs cs pats >>= \(TermsInCtx2 ctx terms terms') ->
        let nscope1 = nfAppsScope $ abstractTermInCtx ctx (apps func terms)
            nscope2 = abstractTermInCtx ctx (instantiate terms' scope)
        in if nfScope nscope1 == nfScope nscope2 then [] else [(nscope1,nscope2)]
  where
    nfApps :: Eq a => Term Posn a -> Term Posn a
    nfApps (App a b) = App (nfApps a) (nf WHNF b)
    nfApps (Con i lc name conds terms) = Con i lc name conds $ map (nf WHNF) terms
    nfApps t = t
    
    nfAppsScope :: Eq a => Scope String Posn (Term Posn) a -> Scope String Posn (Term Posn) a
    nfAppsScope (ScopeTerm t) = ScopeTerm (nfApps t)
    nfAppsScope (Scope v t) = Scope v (nfAppsScope t)

findSuspiciousPairs :: [[PatternC Posn String]] -> [PatternC Posn String] -> [TermsInCtx2 (Term Posn) b]
findSuspiciousPairs _ [] = []
findSuspiciousPairs cs (pat@(PatternEmpty _) : pats) = findSuspiciousPairs (mapTail pat cs) pats
findSuspiciousPairs cs (pat@(PatternI _ con) : pats) = map ext $ findSuspiciousPairs (mapTail pat cs) pats
  where ext (TermsInCtx2 ctx terms1 terms2) = (TermsInCtx2 ctx (ICon (0,0) con : terms1) terms2)
findSuspiciousPairs cs (pat@(PatternVar var) : pats) =
    check ILeft ++ check IRight ++ map ext (findSuspiciousPairs (mapTail pat cs) pats)
  where
    ext (TermsInCtx2 ctx terms1 terms2) = TermsInCtx2 (Snoc ctx var $ error "") (Var (Bound (0,0)) : map (fmap Free) terms1)
                                                                                (Var (Bound (0,0)) : map (fmap Free) terms2)
    check con = if null $ filter (== PatternI (0,0) con) (mapHead cs)
        then []
        else case patternsToTerms pats of
            TermsInCtx ctx terms -> [TermsInCtx2 ctx (ICon (0,0) con : terms) (ICon (0,0) con : ctxToVars' ctx)]
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
    
    ext0 :: [PatternC Posn String] -> TermsInCtx (Term Posn) b -> TermsInCtx2 (Term Posn) b
    ext0 args (TermsInCtx ctx terms) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx')
            (fmap (liftBase ctx') (Con (0,0) i name conds $ substPatterns args terms) : terms')
            (map (fmap $ liftBase ctx') terms ++ ctxToVars' ctx')
    
    ext1 :: TermsInCtx2 (Term Posn) b -> TermsInCtx2 (Term Posn) b
    ext1 (TermsInCtx2 ctx terms1 terms2) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Con (0,0) i name conds terms1) : terms')
                                                             (map (fmap $ liftBase ctx') terms2 ++ ctxToVars' ctx')
    
    ext2 :: Ctx String Posn (Term Posn) a b -> [Term Posn b] -> TermsInCtx2 (Term Posn) b -> TermsInCtx2 (Term Posn) a
    ext2 ctx terms (TermsInCtx2 ctx' terms1 terms2) =
        TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Con (0,0) i name conds terms) : terms1)
                                   (map (fmap $ liftBase ctx') (ctxToVars' ctx) ++ terms2)

ctxToVars' :: Monad g => Ctx s Posn f b a -> [g a]
ctxToVars' = ctxToVars $ const (0,0)

unifyPatterns :: PatternC Posn String -> PatternC Posn String -> Maybe [PatternC Posn String]
unifyPatterns (PatternI _ con) (PatternI _ con') | con == con' = Just []
unifyPatterns (PatternVar _) p = Just [p]
unifyPatterns p (PatternVar _) = Just (varList p)
unifyPatterns (Pattern con pats) (Pattern con' pats') | con == con' = unifyPatternLists pats pats'
unifyPatterns _ _ = Nothing

unifyPatternLists :: [PatternC Posn String] -> [PatternC Posn String] -> Maybe [PatternC Posn String]
unifyPatternLists pats pats' = fmap concat $ sequence (zipWith unifyPatterns pats pats')

varList :: Pattern c p s -> [Pattern c p s]
varList PatternEmpty{} = []
varList PatternI{} = []
varList pat@(PatternVar _) = [pat]
varList (Pattern _ pats) = pats >>= varList

substPatterns :: [PatternC Posn String] -> [Term Posn a] -> [Term Posn a]
substPatterns pats terms = evalState (mapM substPattern pats) terms
  where
    substPattern :: PatternC Posn String -> State [Term Posn a] (Term Posn a)
    substPattern (PatternI p con) = return (ICon p con)
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
        return (Con (0,0) i name conds terms)

patternToTerm :: PatternC Posn String -> TermInCtx (Term Posn) a
patternToTerm (PatternI p con) = TermInCtx Nil (ICon p con)
patternToTerm (PatternEmpty _) = TermInCtx (Snoc Nil "_" $ error "") $ Var $ Bound (0,0)
patternToTerm (PatternVar var) = TermInCtx (Snoc Nil var $ error "") $ Var $ Bound (0,0)
patternToTerm (Pattern (PatternCon i _ name conds) pats) = case patternsToTerms pats of
    TermsInCtx ctx' terms -> TermInCtx ctx' $ Con (0,0) i name conds terms

patternsToTerms :: [PatternC Posn String] -> TermsInCtx (Term Posn) a
patternsToTerms [] = TermsInCtx Nil []
patternsToTerms (pat:pats) = case patternToTerm pat of
    TermInCtx ctx' term -> case patternsToTerms pats of
        TermsInCtx ctx'' terms -> TermsInCtx (ctx' +++ ctx'') $ fmap (liftBase ctx'') term : terms

mapHead :: [[a]] -> [a]
mapHead cs = cs >>= \as -> if null as then [] else [head as]

mapTail :: Eq a => a -> [[a]] -> [[a]]
mapTail a cs = cs >>= \as -> if null as || not (head as == a) then [] else [tail as]
