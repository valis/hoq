{-# LANGUAGE GADTs, ExistentialQuantification, FlexibleInstances #-}

module TypeChecking.Expressions.Conditions
    ( checkConditions
    ) where

import Control.Monad
import Data.Maybe
import Data.Bifunctor
import Data.Void

import qualified Syntax as S
import Semantics
import Semantics.Value
import Semantics.Pattern as P
import Syntax.ErrorDoc
import TypeChecking.Context as C
import TypeChecking.Expressions.Utils
import Normalization

checkConditions :: Eq b => Ctx String f Void b => Term Semantics b -> [(S.Posn, Clause b)] -> [Error]
checkConditions ctx func cs = maybeToList $ msum $
    map (\(pos, Clause p scope) -> fmap (msg pos ctx) $ checkPatterns func (map (\(_, c) -> c) cs) p scope) cs
  where
    msg :: S.Posn -> Ctx String f Void a -> ([String], Term Semantics a, Term Semantics a, Term Semantics a) -> Error
    msg pos ctx (vs, t1, t2, t3) = Error Conditions $ emsgLC pos "Conditions check failed:"
        $  scopeToEDoc ctx vs t1 <+> pretty "equals to" <+> scopeToEDoc ctx vs t2
        $$ pretty "but should be equal to" <+> scopeToEDoc ctx vs t3
    
    scopeToEDoc :: Ctx String f Void a -> [String] -> Term Semantics a -> EDoc (Term S.Syntax)
    scopeToEDoc ctx vs t = epretty $ bimap syntax pretty $ apps (vacuous $ abstractTerm ctx t) $ map cvar (ctxVars ctx ++ vs)

data Some f = forall a. Some (f a)
data TermsInCtx2 f b = forall a. TermsInCtx2 (Ctx String f b a) [f a] [f a]
data TermsInCtx f b = forall a. TermsInCtx (Ctx String f b a) [f a]

checkPatterns :: Eq b => Term Semantics b -> [Clause b] -> Patterns b a
    -> Term Semantics a -> Maybe ([String], Term Semantics b, Term Semantics b, Term Semantics b)
checkPatterns func cs pats scope = listToMaybe $
    findSuspiciousPairs (map Some cs) pats >>= \(TermsInCtx2 ctx terms terms') ->
    let nscope1 = nfApps $ abstractTerm ctx $ apps (fmap (liftBase ctx) func) terms
        nscope2 = abstractTerm ctx $ apps (fmap (liftBase ctx) $ abstractTermPats pats scope) terms'
        nscope1' = nf NF nscope1
    in if nscope1' == nf NF nscope2 then [] else [(reverse $ ctxVars ctx, nscope1, nscope1', nscope2)]
  where
    nfApps :: Eq a => Term Semantics a -> Term Semantics a
    nfApps (Apply a as) = Apply a $ map (nf WHNF) as
    nfApps (Lambda t) = Lambda (nfApps t)
    nfApps t = t

findSuspiciousPairs :: [Some Clause] -> Patterns b a -> [TermsInCtx2 (Term Semantics) b]
findSuspiciousPairs _ P.Nil = []
findSuspiciousPairs cs (Cons pat@(PatVar var) pats) =
    check ILeft ++ check IRight ++ map ext (findSuspiciousPairs (mapTail pat cs) pats)
  where
    ext (TermsInCtx2 ctx terms1 terms2) =
        TermsInCtx2 (Snoc C.Nil var (error "") C.+++ ctx) (fmap (liftBase ctx) bvar : terms1)
                                                          (fmap (liftBase ctx) bvar : terms2)
    check con = if anyICon con cs
                then case abstractPats1 pats of
                        Some pats' -> let (ctx,terms) = patsToTerms $ appsPats pats' [iCon con]
                                      in [TermsInCtx2 ctx (iCon con : terms) (iCon con : ctxToVars ctx)]
                else []
    
    anyICon :: ICon -> [Some Clause] -> Bool
    anyICon _ [] = False
    anyICon con (Some (Clause (Cons (PatICon con') _) _) : cs) | con == con' = True
    anyICon con (_ : cs) = anyICon con cs
findSuspiciousPairs cs (Cons pat pats) =
    (case pat of
        PatDCon _ _ _ conds params args -> conds >>= \(Closed (Clause cond _)) -> case unifyPatterns args cond of
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
    
    ext0 args (TermsInCtx ctx terms) = case instantiatePats (fst $ patToTerm pat) ctx terms pats of
        Some pats' -> let (ctx1,terms1) = patsToTerms pats'
                          (ctx2,terms2) = patsToTerms args
                          fapps t = apps (fmap (liftBase ctx) $ abstractTerm ctx2 t) terms
                      in TermsInCtx2 (ctx C.+++ ctx1)
                            (fmap (liftBase ctx1) (Apply (patToSemantics pat) $ map fapps terms2) : terms1)
                            (map (fmap $ liftBase ctx1) terms ++ ctxToVars ctx1)
    
    ext1 (TermsInCtx2 ctx terms1 terms2) = case instantiatePats (fst $ patToTerm pat) ctx terms2 pats of
        Some pats' -> let (ctx',terms') = patsToTerms pats'
                      in TermsInCtx2 (ctx C.+++ ctx') (fmap (liftBase ctx') (Apply (patToSemantics pat) terms1) : terms')
                                                      (map (fmap $ liftBase ctx') terms2 ++ ctxToVars ctx')
    
    ext2 :: (Ctx String (Term Semantics) b c, [Term Semantics c])
        -> TermsInCtx2 (Term Semantics) c -> TermsInCtx2 (Term Semantics) b
    ext2 (ctx, terms) (TermsInCtx2 ctx' terms1 terms2) =
        TermsInCtx2 (ctx C.+++ ctx') (fmap (liftBase ctx') (Apply (patToSemantics pat) terms) : terms1)
                                     (map (fmap $ liftBase ctx') (ctxToVars ctx) ++ terms2)

unifyPatterns :: Patterns b a -> Patterns b c -> Maybe (TermsInCtx (Term Semantics) b)
unifyPatterns P.Nil P.Nil = Just $ TermsInCtx C.Nil []
unifyPatterns pats1 P.Nil =
    let ctx = fst (patsToTerms pats1)
    in Just $ TermsInCtx ctx (ctxToVars ctx)
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
    in case abstractPats1 pats1 of
        Some pats1' -> case fmapPats (liftBase ctx1) pats1' of
            Some pats1'' -> fmap mapTerms $ unifyPatterns (appsPats pats1'' [term]) pats2
unifyPatterns (Cons pat1 pats1) (Cons PatVar{} pats2) =
    let (ctx1,term) = patToTerm pat1
        mapTerms (TermsInCtx ctx2 terms) = TermsInCtx (ctx1 C.+++ ctx2) $
            map (fmap $ liftBase ctx2) (ctxToVars ctx1) ++ terms
    in case abstractPats1 pats2 of
        Some pats2' -> case fmapPats (liftBase ctx1) pats2' of
            Some pats2'' -> fmap mapTerms $ unifyPatterns pats1 (appsPats pats2'' [term])
unifyPatterns _ _ = Nothing

abstractPats1 :: Patterns (Scoped b) a -> Some (Patterns b)
abstractPats1 P.Nil = Some P.Nil
abstractPats1 (Cons (PatDCon v i n cs params ps) pats) = case abstractPats1 (ps P.+++ pats) of
    Some pats' -> case patternsSplitAt pats' (patternsLength ps) of
        Split pats1 pats2 -> Some $ Cons (PatDCon v i n cs (map Lambda params) pats1) pats2
abstractPats1 (Cons (PatPCon pat) pats) = case abstractPats1 (Cons pat pats) of
    Some (Cons pat' pats') -> Some $ Cons (PatPCon pat') pats'
    _ -> error "abstractPats1"
abstractPats1 (Cons (PatICon con) pats) = case abstractPats1 pats of
    Some pats' -> Some $ Cons (PatICon con) pats'
abstractPats1 (Cons (PatVar  var) pats) = case abstractPats1 pats of
    Some pats' -> Some $ Cons (PatVar var) pats'

abstractPats :: Ctx s f b c -> Patterns c a -> Some (Patterns b)
abstractPats C.Nil pats = Some pats
abstractPats (Snoc ctx _ _) pats = case abstractPats1 pats of
    Some pats' -> abstractPats ctx pats'

fmapPats :: (b -> d) -> Patterns b a -> Some (Patterns d)
fmapPats _ P.Nil = Some P.Nil
fmapPats f (Cons (PatDCon v i n cs params ps) pats) = case fmapPats f (ps P.+++ pats) of
    Some pats' -> case patternsSplitAt pats' (patternsLength ps) of
        Split pats1 pats2 -> Some $ Cons (PatDCon v i n cs (map (fmap f) params) pats1) pats2
fmapPats f (Cons (PatPCon pat) pats) = case fmapPats f (Cons pat pats) of
    Some (Cons pat' pats') -> Some $ Cons (PatPCon pat') pats'
    _ -> error "fmapPats"
fmapPats f (Cons (PatICon con) pats) = case fmapPats f pats of
    Some pats' -> Some $ Cons (PatICon con) pats'
fmapPats f (Cons (PatVar  var) pats) = case fmapPats (fmap f) pats of
    Some pats' -> Some $ Cons (PatVar var) pats'

appsPats :: Patterns d a -> [Term Semantics d] -> Patterns d a
appsPats pats [] = pats
appsPats P.Nil _ = P.Nil
appsPats (Cons pat pats) terms = Cons (appsPat pat terms) $ appsPats pats $ map (fmap $ liftBasePat pat) terms

appsPat :: Pattern d a -> [Term Semantics d] -> Pattern d a
appsPat pat [] = pat
appsPat (PatDCon v i n cs params ps) terms = PatDCon v i n cs (map (\param -> apps param terms) params) (appsPats ps terms)
appsPat (PatPCon pat) terms = PatPCon (appsPat pat terms)
appsPat (PatICon con) _ = PatICon con
appsPat (PatVar  var) _ = PatVar var

instantiatePats :: Ctx s f b c -> Ctx s f b d -> [Term Semantics d] -> Patterns c a -> Some (Patterns d)
instantiatePats ctx1 ctx2 terms pats = case abstractPats ctx1 pats of
    Some pats1 -> case fmapPats (liftBase ctx2) pats1 of
        Some pats2 -> Some (appsPats pats2 terms)

patToSemantics :: Pattern b a -> Semantics
patToSemantics (PatDCon v i _ cs ps _) = Semantics v $
    DCon i (length ps) $ map (\(Closed c) -> (fst $ clauseToEval c, Closed $ snd $ clauseToEval c)) cs
patToSemantics PatPCon{} = pathSem
patToSemantics (PatICon con) = iConSem con
patToSemantics PatVar{} = error "patToSemantics"

patToTerm :: Pattern b a -> (Ctx String (Term Semantics) b a, Term Semantics a)
patToTerm pat@(PatDCon _ _ _ _ ps pats) =
    let (ctx,terms) = patsToTerms pats
    in (ctx, Apply (patToSemantics pat) $ map (fmap $ liftBasePats pats) ps ++ terms)
patToTerm (PatPCon pat) =
    let (ctx,term) = patToTerm pat
    in (ctx, path [term])
patToTerm (PatICon con) = (C.Nil, iCon con)
patToTerm (PatVar  var) = (Snoc C.Nil var $ error "", bvar)

patsToTerms :: Patterns b a -> (Ctx String (Term Semantics) b a, [Term Semantics a])
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
