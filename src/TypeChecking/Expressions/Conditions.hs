{-# LANGUAGE GADTs, ExistentialQuantification #-}

module TypeChecking.Expressions.Conditions
    ( checkConditions
    , patToTerm, patsToTerms
    ) where

import Control.Monad
import Data.Maybe
import Data.Void

import qualified Syntax as S
import Semantics
import Semantics.Value
import Semantics.Pattern as P
import TypeChecking.Context as C
import TypeChecking.Expressions.Utils
import Normalization

checkConditions :: Eq b => Ctx String f Void b -> Term Semantics b -> [(S.Posn, Clause b)] -> [Error]
checkConditions ctx func cs = maybeToList $ msum $
    map (\(pos, Clause p scope) -> fmap (conditionsErrorMsg pos ctx) $ checkPatterns func (map (\(_, c) -> c) cs) p scope) cs

data TermsInCtx2 f b = forall a. TermsInCtx2 (Ctx String f b a) [f a] [f a]
data TermsInCtx f b = forall a. TermsInCtx (Ctx String f b a) [f a]

checkPatterns :: Eq b => Term Semantics b -> [Clause b] -> Patterns b a
    -> Term Semantics a -> Maybe ([String], Term Semantics b, Term Semantics b, Term Semantics b)
checkPatterns func cs pats scope = listToMaybe $
    findSuspiciousPairs (map Some cs) pats >>= \(TermsInCtx2 ctx terms terms') ->
    let nscope1 = nfApps $ abstractTerm ctx $ apps (fmap (liftBase ctx) func) terms
        nscope2 = abstractTerm ctx $ apps (fmap (liftBase ctx) $ abstractTermPats pats scope) terms'
        nscope1' = nf NF nscope1
    in if nscope1' == nf NF nscope2 then [] else [(ctxVars ctx, nscope1, nscope1', nscope2)]
  where
    nfApps :: Eq a => Term Semantics a -> Term Semantics a
    nfApps (Apply a as) = Apply a $ map (nf WHNF) as
    nfApps (Lambda t) = Lambda (nfApps t)
    nfApps (Var a as) = Var a $ map (nf WHNF) as

findSuspiciousPairs :: [Some Clause] -> Patterns b a -> [TermsInCtx2 (Term Semantics) b]
findSuspiciousPairs _ P.Nil = []
findSuspiciousPairs cs (Cons pat@(PatVar var) pats) =
    check ILeft ++ check IRight ++ map ext (findSuspiciousPairs (mapTail pat cs) pats)
  where
    ext (TermsInCtx2 ctx terms1 terms2) =
        TermsInCtx2 (Snoc C.Nil var (error "") C.+++ ctx) (fmap (liftBase ctx) bvar : terms1)
                                                          (fmap (liftBase ctx) bvar : terms2)
    check con = if anyICon con cs
                then case instantiatePats1 (iCon con) pats of
                        Some pats' -> let (ctx,terms) = patsToTerms pats'
                                      in [TermsInCtx2 ctx (iCon con : terms) (iCon con : map return (ctxToVars ctx))]
                else []
    
    anyICon :: ICon -> [Some Clause] -> Bool
    anyICon _ [] = False
    anyICon con (Some (Clause (Cons (PatICon con') _) _) : cs) | con == con' = True
    anyICon con (_ : cs) = anyICon con cs
findSuspiciousPairs cs (Cons pat pats) =
    (case pat of
        PatDCon _ _ _ conds params args -> conds >>= \(ClauseInCtx ctx (Clause cond _)) ->
            case instantiatePats ctx params cond of
                Some cond' -> case unifyPatterns args cond' of
                    Nothing -> []
                    Just args' -> [ext0 args args']
        _ -> []) ++
    map ext1 (findSuspiciousPairs cs' $ getArgs pat) ++
    map (ext2 $ patsToTerms $ getArgs pat) (findSuspiciousPairs (mapTail pat cs) pats)
  where
    getArgs :: Pattern b a -> Patterns b a
    getArgs (PatDCon _ _ _ _ _ pats) = pats
    getArgs (PatPCon pat) = Cons pat P.Nil
    getArgs PatICon{} = P.Nil
    getArgs PatVar{} = error "getArgs"
    
    cs' = cs >>= \(Some (Clause ps _)) -> case ps of
            Cons (PatDCon _ _ _ _ _ pats) _ -> [Some $ Clause pats $ error ""]
            Cons (PatPCon pat) _ -> [Some $ Clause (Cons pat P.Nil) $ error ""]
            _ -> []
    
    ext0 args (TermsInCtx ctx terms) = case instantiatePatsAndLift (fst $ patToTerm pat) ctx terms pats of
        Some pats' -> let (ctx1,terms1) = patsToTerms pats'
                          (ctx2,terms2) = patsToTerms args
                          fapps t = apps (fmap (liftBase ctx) $ abstractTerm ctx2 t) terms
                      in TermsInCtx2 (ctx C.+++ ctx1)
                            (fmap (liftBase ctx1) (apps (fmap (liftBase ctx) $ patToCon pat) $ map fapps terms2) : terms1)
                            (map (fmap $ liftBase ctx1) terms ++ map return (ctxToVars ctx1))
    
    ext1 (TermsInCtx2 ctx terms1 terms2) = case instantiatePatsAndLift (fst $ patToTerm pat) ctx terms2 pats of
        Some pats' -> let (ctx',terms') = patsToTerms pats'
                      in TermsInCtx2 (ctx C.+++ ctx') (fmap (liftBase ctx') (apps (fmap (liftBase ctx) $ patToCon pat) terms1) : terms')
                                                      (map (fmap $ liftBase ctx') terms2 ++ map return (ctxToVars ctx'))
    
    ext2 (ctx, terms) (TermsInCtx2 ctx' terms1 terms2) =
        TermsInCtx2 (ctx C.+++ ctx') (fmap (liftBase ctx') (apps (fmap (liftBase ctx) $ patToCon pat) terms) : terms1)
                                     (map (fmap $ liftBase ctx') (map return $ ctxToVars ctx) ++ terms2)

unifyPatterns :: Patterns b a -> Patterns b c -> Maybe (TermsInCtx (Term Semantics) b)
unifyPatterns P.Nil P.Nil = Just $ TermsInCtx C.Nil []
unifyPatterns pats1 P.Nil =
    let ctx = fst (patsToTerms pats1)
    in Just $ TermsInCtx ctx $ map return (ctxToVars ctx)
unifyPatterns P.Nil pats2 =
    let (ctx,terms) = patsToTerms pats2
    in Just $ TermsInCtx ctx terms
unifyPatterns (Cons (PatDCon _ i1 _ _ _ ps1) pats1) (Cons (PatDCon _ i2 _ _ _ ps2) pats2) | i1 == i2 =
    unifyPatterns (ps1 P.+++ pats1) (ps2 P.+++ pats2)
unifyPatterns (Cons (PatPCon pat1) pats1) (Cons (PatPCon pat2) pats2) = unifyPatterns (Cons pat1 pats1) (Cons pat2 pats2)
unifyPatterns (Cons (PatICon con1) pats1) (Cons (PatICon con2) pats2) | con1 == con2 = unifyPatterns pats1 pats2
unifyPatterns (Cons PatVar{} pats1) (Cons pat2 pats2) =
    let (ctx1,term) = patToTerm pat2
        mapTerms (TermsInCtx ctx2 terms) = TermsInCtx (ctx1 C.+++ ctx2) $ fmap (liftBase ctx2) term : terms
    in case instantiatePatsAndLift1 ctx1 term pats1 of
        Some pats1' -> fmap mapTerms (unifyPatterns pats1' pats2)
unifyPatterns (Cons pat1 pats1) (Cons PatVar{} pats2) =
    let (ctx1,term) = patToTerm pat1
        mapTerms (TermsInCtx ctx2 terms) = TermsInCtx (ctx1 C.+++ ctx2) $
            map (fmap $ liftBase ctx2) (map return $ ctxToVars ctx1) ++ terms
    in case instantiatePatsAndLift1 ctx1 term pats2 of
        Some pats2' -> fmap mapTerms (unifyPatterns pats1 pats2')
unifyPatterns _ _ = Nothing

patToSemantics :: Pattern b a -> Semantics
patToSemantics (PatDCon v i _ cs ps _) = Semantics v $ DCon i (length ps) $
    map (\(ClauseInCtx ctx cl) -> (fst $ clauseToEval cl, closed $ abstractTerm ctx $ snd $ clauseToEval cl)) cs
patToSemantics PatPCon{} = pathSem
patToSemantics (PatICon con) = iConSem con
patToSemantics PatVar{} = error "patToSemantics"

patToCon :: Pattern b a -> Term Semantics b
patToCon p@(PatDCon _ _ _ _ ps _) = Apply (patToSemantics p) ps
patToCon p = capply (patToSemantics p)

patToTerm :: Pattern b a -> (Ctx String f b a, Term Semantics a)
patToTerm pat@(PatDCon _ _ _ _ ps pats) =
    let (ctx,terms) = patsToTerms pats
    in (ctx, Apply (patToSemantics pat) $ map (fmap $ liftBasePats pats) ps ++ terms)
patToTerm (PatPCon pat) =
    let (ctx,term) = patToTerm pat
    in (ctx, path [term])
patToTerm (PatICon con) = (C.Nil, iCon con)
patToTerm (PatVar  var) = (Snoc C.Nil var $ error "", bvar)

patsToTerms :: Patterns b a -> (Ctx String f b a, [Term Semantics a])
patsToTerms P.Nil = (C.Nil, [])
patsToTerms (Cons pat pats) =
    let (ctx1,term)  = patToTerm pat
        (ctx2,terms) = patsToTerms pats
    in (ctx1 C.+++ ctx2, fmap (liftBase ctx2) term : terms)

mapTail :: Pattern b a -> [Some Clause] -> [Some Clause]
mapTail p cs = cs >>= \c -> case (p,c) of
    (PatVar{},  Some (Clause (Cons PatVar{}  ps) t)) -> [Some $ Clause ps t]
    (PatPCon{}, Some (Clause (Cons PatPCon{} ps) t)) -> [Some $ Clause ps t]
    (PatICon{}, Some (Clause (Cons PatICon{} ps) t)) -> [Some $ Clause ps t]
    (PatDCon{}, Some (Clause (Cons PatDCon{} ps) t)) -> [Some $ Clause ps t]
    _ -> []
