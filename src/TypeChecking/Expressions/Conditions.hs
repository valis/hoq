{-# LANGUAGE GADTs, ExistentialQuantification, FlexibleInstances #-}

module TypeChecking.Expressions.Conditions
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

instance Eq (Term (s, Con t) a) where
    Apply (_,s) _ == Apply (_,s') _ = s == s'
    Var{} == Var{} = True
    _ == _ = False

checkConditions :: S.Posn -> Closed (Term Semantics) -> [([Term (String,SCon) String], Closed (Term Semantics))] -> [EMsg (Term S.Syntax)]
checkConditions lc func cs =
    maybeToList $ msum $ map (\(p, scope) -> fmap msg $ checkPatterns func (map fst cs) p scope) cs
  where
    msg :: ([String], Term Semantics String, Term Semantics String) -> EMsg (Term S.Syntax)
    msg (vs, t1, t2) = emsgLC lc "Conditions check failed:" $ scopeToEDoc vs t1 <+> pretty "is not equal to" <+> scopeToEDoc vs t2
    
    scopeToEDoc :: [String] -> Term Semantics String -> EDoc (Term S.Syntax)
    scopeToEDoc vs t = epretty $ bimap syntax pretty $ apps t (map cvar vs)

data TermInCtx  f b = forall a. TermInCtx  (Ctx String f b a) (f a)
data TermsInCtx f b = forall a. TermsInCtx (Ctx String f b a) [f a]
data TermsInCtx2 f b = forall a. TermsInCtx2 (Ctx String f b a) [f a] [f a]

checkPatterns :: Closed (Term Semantics) -> [[Term (String,SCon) String]] -> [Term (String,SCon) String]
    -> Closed (Term Semantics) -> Maybe ([String], Term Semantics String, Term Semantics String)
checkPatterns (Closed func) cs pats (Closed scope) =
    listToMaybe $ findSuspiciousPairs cs pats >>= \(TermsInCtx2 ctx terms terms') ->
        let nscope1 = nfApps $ abstractTerm ctx (apps func terms)
            nscope2 = abstractTerm ctx (apps scope terms')
        in if nf NF nscope1 == nf NF nscope2 then [] else [(reverse $ ctxVars ctx, nscope1, nscope2)]
  where
    nfApps :: Eq a => Term Semantics a -> Term Semantics a
    nfApps (Apply a as) = Apply a $ map (nf WHNF) as
    nfApps (Lambda t) = Lambda (nfApps t)
    nfApps t = t

findSuspiciousPairs :: [[Term (String,SCon) String]] -> [Term (String,SCon) String] -> [TermsInCtx2 (Term Semantics) b]
findSuspiciousPairs _ [] = []
findSuspiciousPairs cs (pat@(Var var _) : pats) =
    check ILeft ++ check IRight ++ map ext (findSuspiciousPairs (mapTail pat cs) pats)
  where
    ext (TermsInCtx2 ctx terms1 terms2) = TermsInCtx2 (Snoc ctx var $ error "") (cvar Bound : map (fmap Free) terms1)
                                                                                (cvar Bound : map (fmap Free) terms2)
    check con = if null $ filter (== Apply ("", ICon con) []) (mapHead cs)
        then []
        else case patternsToTerms pats of
            TermsInCtx ctx terms -> [TermsInCtx2 ctx (iCon con : terms) (iCon con : ctxToVars ctx)]
findSuspiciousPairs cs (pat@(Apply (name, con) args) : pats) =
    (case con of
        DCon _ _ (PatEval conds) -> conds >>= \(cond,_) -> case unifyPatternLists args cond of
            Nothing -> []
            Just args' -> [ext0 args $ patternsToTerms args']
        _ -> []) ++
    map ext1 (findSuspiciousPairs cs' args) ++ case patternsToTerms args of
        TermsInCtx ctx terms -> map (ext2 ctx terms) (findSuspiciousPairs (mapTail pat cs) pats)
  where
    cs' = cs >>= \as -> case as of
            Apply (_, con') args' : _ | con == con' -> [args']
            _ -> []
    
    ext0 :: [Term (String,SCon) String] -> TermsInCtx (Term Semantics) b -> TermsInCtx2 (Term Semantics) b
    ext0 args (TermsInCtx ctx terms) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx')
            (fmap (liftBase ctx') (Apply (Semantics (S.Name S.Prefix $ S.Ident name) (Con con)) $ substPatterns args terms) : terms')
            (map (fmap $ liftBase ctx') terms ++ ctxToVars ctx')
    
    ext1 :: TermsInCtx2 (Term Semantics) b -> TermsInCtx2 (Term Semantics) b
    ext1 (TermsInCtx2 ctx terms1 terms2) = case patternsToTerms pats of
        TermsInCtx ctx' terms' -> TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Apply (Semantics (S.Name S.Prefix $ S.Ident name) (Con con)) terms1) : terms')
                                                             (map (fmap $ liftBase ctx') terms2 ++ ctxToVars ctx')
    
    ext2 :: Ctx String (Term Semantics) a b -> [Term Semantics b] -> TermsInCtx2 (Term Semantics) b -> TermsInCtx2 (Term Semantics) a
    ext2 ctx terms (TermsInCtx2 ctx' terms1 terms2) =
        TermsInCtx2 (ctx +++ ctx') (fmap (liftBase ctx') (Apply (Semantics (S.Name S.Prefix $ S.Ident name) (Con con)) terms) : terms1)
                                   (map (fmap $ liftBase ctx') (ctxToVars ctx) ++ terms2)
findSuspiciousPairs _ (Lambda{} : _) = error "findSuspiciousPairs"

unifyPatterns :: Term (String,SCon) String -> Term (String,SCon) String -> Maybe [Term (String,SCon) String]
unifyPatterns (Apply (_,con) pats) (Apply (_,con') pats') | con == con' = unifyPatternLists pats pats'
unifyPatterns Var{} p = Just [p]
unifyPatterns p Var{} = Just (varList p)
unifyPatterns _ _ = Nothing

unifyPatternLists :: [Term (String,SCon) String] -> [Term (String,SCon) String] -> Maybe [Term (String,SCon) String]
unifyPatternLists pats pats' = fmap concat $ sequence (zipWith unifyPatterns pats pats')

varList :: Term (String,SCon) String -> [Term (String,SCon) String]
varList pat@Var{} = [pat]
varList (Apply _ pats) = pats >>= varList
varList _ = []

substPatterns :: [Term (String,SCon) String] -> [Term Semantics a] -> [Term Semantics a]
substPatterns pats terms = evalState (mapM substPattern pats) terms
  where
    substPattern :: Term (String,SCon) String -> State [Term Semantics a] (Term Semantics a)
    substPattern Var{} = do
        term:terms <- get
        put terms
        return term
    substPattern (Apply (name, con) pats) = do
        terms <- mapM substPattern pats
        return $ Apply (Semantics (S.Name S.Prefix $ S.Ident name) (Con con)) terms
    substPattern Lambda{} = error "substPattern"

patternToTerm :: Term (String,SCon) String -> TermInCtx (Term Semantics) a
patternToTerm (Var var _) = TermInCtx (Snoc Nil var $ error "") (cvar Bound)
patternToTerm (Apply (name, con) pats) = case patternsToTerms pats of
    TermsInCtx ctx' terms -> TermInCtx ctx' $ Apply (Semantics (S.Name S.Prefix $ S.Ident name) (Con con)) terms
patternToTerm Lambda{} = error "patternToTerm"

patternsToTerms :: [Term (String,SCon) String] -> TermsInCtx (Term Semantics) a
patternsToTerms [] = TermsInCtx Nil []
patternsToTerms (pat:pats) = case patternToTerm pat of
    TermInCtx ctx' term -> case patternsToTerms pats of
        TermsInCtx ctx'' terms -> TermsInCtx (ctx' +++ ctx'') $ fmap (liftBase ctx'') term : terms

mapHead :: [[a]] -> [a]
mapHead cs = cs >>= \as -> if null as then [] else [head as]

mapTail :: Eq a => a -> [[a]] -> [[a]]
mapTail a cs = cs >>= \as -> if null as || head as /= a then [] else [tail as]
