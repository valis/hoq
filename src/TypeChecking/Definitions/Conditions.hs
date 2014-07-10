{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Definitions.Conditions
    ( checkConditions
    ) where

import Control.Monad
import Data.Maybe

import Syntax.Term
import Syntax.ErrorDoc
import Syntax.PrettyPrinter
import TypeChecking.Context
import Normalization

checkConditions :: (Int,Int) -> Closed Term -> [([Pattern], Closed (Scope String Term))] -> [EMsg Term]
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

checkPatterns :: Closed Term -> [[Pattern]] -> [Pattern] -> Closed (Scope String Term)
    -> Maybe (Scope String Term String, Scope String Term String)
checkPatterns (Closed func) cs pats (Closed scope) =
    listToMaybe $ findSuspicious cs pats >>= \(TermsInCtx2 ctx terms terms') ->
        let nscope1 = nfScope $ abstractTermInCtx ctx (apps func terms)
            nscope2 = nfScope $ abstractTermInCtx ctx (instantiate terms' scope)
        in if nscope1 == nscope2 then [] else [(nscope1,nscope2)]

findSuspicious :: [[Pattern]] -> [Pattern] -> [TermsInCtx2 Term b]
findSuspicious _ [] = []
findSuspicious cs (pat@(PatternI con) : pats) = map ext $ findSuspicious (mapTail pat cs) pats
  where ext (TermsInCtx2 ctx terms1 terms2) = (TermsInCtx2 ctx (ICon con : terms1) terms2)
findSuspicious cs (pat@(PatternVar var) : pats) =
    check ILeft ++ check IRight ++ map ext (findSuspicious (mapTail pat cs) pats)
  where ext (TermsInCtx2 ctx terms1 terms2) = TermsInCtx2 (Snoc ctx var $ error "") (Var Bound : map (fmap Free) terms1)
                                                                                    (Var Bound : map (fmap Free) terms2)
        check con = if null $ filter (\p -> p `cmpPattern` PatternI con) (mapHead cs)
            then []
            else case patternsToTerms pats of
                TermsInCtx ctx terms -> [TermsInCtx2 ctx (ICon con : terms) (ICon con : ctxToVars ctx)]
findSuspicious cs (pat@(Pattern con@(PatternCon i _ c _) args) : pats) =
    map ext1 (findSuspicious cs' args) ++ case patternsToTerms args of
        TermsInCtx ctx terms -> map (ext2 ctx terms) (findSuspicious (mapTail pat cs) pats)
  where cs' = cs >>= \as -> case as of
                Pattern con' args' : _ | con `cmpPatternCon` con' -> [args']
                _ -> []
        ext1 (TermsInCtx2 ctx terms1 terms2) = case patternsToTerms pats of
            TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Con i c [] terms1) : terms')
                                                                 (map (fmap $ liftBase ctx') terms2 ++ ctxToVars ctx')
        ext2 :: Ctx String Term a b -> [Term b] -> TermsInCtx2 Term b -> TermsInCtx2 Term a
        ext2 ctx terms (TermsInCtx2 ctx' terms1 terms2) =
            TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Con i c [] terms) : terms1)
                                       (map (fmap $ liftBase ctx') (ctxToVars ctx) ++ terms2)

patternToTerm :: Pattern -> TermInCtx Term a
patternToTerm (PatternI con) = TermInCtx Nil (ICon con)
patternToTerm (PatternVar var) = TermInCtx (Snoc Nil var $ error "") (Var Bound)
patternToTerm (Pattern (PatternCon i _ c _) pats) = case patternsToTerms pats of
    TermsInCtx ctx' terms -> TermInCtx ctx' $ Con i c [] terms

patternsToTerms :: [Pattern] -> TermsInCtx Term a
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

mapTail :: Pattern -> [[Pattern]] -> [[Pattern]]
mapTail a cs = cs >>= \as -> if null as || not (head as `cmpPattern` a) then [] else [tail as]
