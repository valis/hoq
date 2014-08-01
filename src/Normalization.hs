module Normalization
    ( NF(..), nf
    , nfType
    ) where

import Control.Monad
import Data.Traversable

import Syntax

data NF = NF | Step | WHNF deriving Eq

nf :: Eq a => NF -> Term Syntax a -> Term Syntax a
nf mode (Apply t ts) = nfSyntax mode t ts
nf mode (Lambda (Scope1 t)) | mode /= WHNF = Lambda $ Scope1 (nf mode t)
nf _ t = t

nfSyntax :: Eq a => NF -> Syntax -> [Term Syntax a] -> Term Syntax a
nfSyntax mode t ts = go t ts []
  where
    go App [Apply a as, t] ts = go a as (t:ts)
    go (Lam [_]) [Lambda (Scope1 s)] (t:ts) = let Apply a as = instantiate1 t s in goStep a as ts
    go (Lam vs) [Lambda (Scope1 a)] (t:ts) = goStep (Lam $ tail vs) [instantiate1 t a] ts
    go (FunSyn _ (Closed (Apply a as))) _ ts = goStep a as ts
    go t@(Con c n conds) _ ts = case instantiateClauses conds ts of
        Just (Apply a as, ts')  -> goStep a as ts'
        _                       -> capps t (nfs mode ts)
    go t@(FunCall _ []) _ ts = capps t (nfs mode ts)
    go t@(FunCall _ clauses) _ ts = case instantiateClauses clauses ts of
        Just (Apply a as, ts')  -> goStep a as ts'
        _                       -> capps t (nfs mode ts)
    go At [t1@(Apply a1 as1), t2@(Apply a2 as2), t3, t4] ts = case (nf WHNF t3, nf WHNF t4) of
        (_, Apply (ICon ILeft) _)  -> goStep a1 as1 ts
        (_, Apply (ICon IRight) _) -> goStep a2 as2 ts
        (Apply App [Apply PCon _, Apply a3 as3], t4') -> goStep a3 as3 (t4':ts)
        (t3', t4') -> apps (Apply At $ nfs mode [t1, t2, t3', t4']) (nfs mode ts)
    go Coe _ (t1:t2:t3@(Apply a3 as3):t4:ts) =
        let t1' = nf WHNF t1
            t2' = nf NF t2
            t4' = nf NF t4
        in case (t2' == t4' || isStationary t1', t2' == cterm (ICon ILeft)  && t4' == cterm (ICon IRight),
                                                 t2' == cterm (ICon IRight) && t4' == cterm (ICon ILeft), collect t1') of
            (True, _, _, _) -> goStep a3 as3 ts
            (_, True, _, (Just Iso, [_, _, Apply c cs, _, _, _])) -> goStep c cs (t3:ts)
            (_, _, True, (Just Iso, [_, _, _, Apply c cs, _, _])) -> goStep c cs (t3:ts)
            (_, b1, b2, _) | b1 || b2 -> case collect $ nfSyntax NF App [fmap Free t1', Var Bound] of
                (Just Iso, [c1, c2, c3, c4, c5, c6, Var Bound]) -> case map sequenceA [c1,c2,c3,c4,c5,c6] of
                    [Free{}, Free{}, Free (Apply c3' cs3'), Free (Apply c4' cs4'), Free{}, Free{}] ->
                        if b1 then goStep c3' cs3' (t3:ts) else goStep c4' cs4' (t3:ts)
                    _ -> capps Coe $ t1':t2':t3:t4':ts
                _ -> capps Coe $ t1':t2':t3:t4':ts
            _ -> capps Coe $ t1':t2':t3:t4':ts
    go Iso _ ts@[Apply a1 as1, Apply a2 as2, _, _, _, _, t7] = case nf WHNF t7 of
        Apply (ICon ILeft)  _ -> goStep a1 as1 []
        Apply (ICon IRight) _ -> goStep a2 as2 []
        _           -> capps Iso (nfs mode ts)
    go Squeeze _ [t1,t2] = case (nf WHNF t1, nf WHNF t2) of
        (Apply (ICon ILeft)  _, _) -> cterm (ICon ILeft)
        (Apply (ICon IRight) _, j) -> if mode == Step then j else nf mode j
        (_, Apply (ICon ILeft)  _) -> cterm (ICon ILeft)
        (i, Apply (ICon IRight) _) -> if mode == Step then i else nf mode i
    go a as ts = apps (Apply a $ nfs mode as) (nfs mode ts)
    
    goStep a as ts = if mode == Step then apps (Apply a as) ts else go a as ts

nfType :: Eq a => NF -> Type Syntax a -> Type Syntax a
nfType mode (Type t lvl) = Type (nf mode t) lvl

isStationary :: Eq a => Term Syntax a -> Bool
isStationary t = case sequenceA $ nfSyntax NF App [fmap Free t, Var Bound] of
    Free _  -> True
    Bound   -> False

nfs :: Eq a => NF -> [Term Syntax a] -> [Term Syntax a]
nfs WHNF terms = terms
nfs mode terms = map (nf mode) terms

instantiatePat :: Eq a => [PatternC s] -> Scope b (Term Syntax) a -> [Term Syntax a] -> Maybe (Term Syntax a, [Term Syntax a])
instantiatePat [] (ScopeTerm term) terms = Just (term, terms)
instantiatePat (PatternVar _ : pats) (Scope _ scope) (term:terms) = instantiatePat pats (instantiateScope term scope) terms
instantiatePat (PatternI _ con : pats) scope (term:terms) = case nf WHNF term of
    Apply (ICon i) _ | i == con -> instantiatePat pats scope terms
    _ -> Nothing
instantiatePat (Pattern (PatternCon con _ _ _) pats1 : pats) scope (term:terms) = case collect (nf WHNF term) of
    (Just (Con i n _), terms1) | i == con -> instantiatePat (pats1 ++ pats) scope (terms1 ++ terms)
    _ -> Nothing
instantiatePat _ _ _ = Nothing

instantiateClauses :: Eq a => [([PatternC s], Closed (Scope b (Term Syntax)))]
    -> [Term Syntax a] -> Maybe (Term Syntax a, [Term Syntax a])
instantiateClauses clauses terms = msum $ map (\(pats, Closed scope) -> instantiatePat pats scope terms) clauses
