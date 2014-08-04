module Normalization
    ( NF(..), nf
    , nfType
    ) where

import Control.Monad
import Data.Traversable

import Semantics
import qualified Syntax as S
import Semantics.Value

data NF = NF | Step | WHNF deriving Eq

nf :: Eq a => NF -> Term Semantics a -> Term Semantics a
nf mode (Apply t ts) = nfSemantics mode t ts
nf mode (Lambda t) | mode /= WHNF = Lambda (nf mode t)
nf _ t = t

nfSemantics :: Eq a => NF -> Semantics -> [Term Semantics a] -> Term Semantics a
nfSemantics mode t ts = go t ts []
  where
    go (Semantics _ App) [a@Var{}, t] ts = apps a $ nfs mode (t:ts)
    go (Semantics _ App) [Apply a as, t] ts = go a as (t:ts)
    go (Semantics (S.Lam (_:vs)) Lam) [Lambda a@Lambda{}] (t:ts) =
        goStep (Apply (Semantics (S.Lam $ tail vs) Lam) [instantiate1 t a]) ts
    go (Semantics _ Lam) [Lambda s] (t:ts) = goStep (instantiate1 t s) ts
    go t@(Semantics _ (Con c (PatEval conds))) _ ts = case instantiateClauses conds ts of
        Just (t', ts')  -> goStep t' ts'
        _               -> capps t (nfs mode ts)
    go (Semantics _ (FunCall _ (SynEval (Closed t)))) _ ts = goStep t ts
    go t@(Semantics _ (FunCall _ (PatEval clauses))) _ ts = case instantiateClauses clauses ts of
        Just (t', ts')  -> goStep t' ts'
        _               -> capps t (nfs mode ts)
    go t@(Semantics _ At) [t1,t2,t3,t4] ts = case (nf WHNF t3, nf WHNF t4) of
        (_, Apply (Semantics _ (ICon ILeft))  _) -> goStep t1 ts
        (_, Apply (Semantics _ (ICon IRight)) _) -> goStep t2 ts
        (Apply (Semantics _ PCon) [t3'], t4')    -> goStep t3' (t4':ts)
        (t3', t4')                               -> apps (Apply t $ nfs mode [t1, t2, t3', t4']) (nfs mode ts)
    go t@(Semantics _ Coe) _ (t1:t2:t3:t4:ts) =
        let t1' = nf WHNF t1
            t2' = nf NF t2
            t4' = nf NF t4
            isICon c (Apply (Semantics _ (ICon c')) _) = c == c'
            isICon _ _ = False
            r = capps t $ if mode == WHNF then t1':t2':t3:t4':ts else nf mode t1' : t2' : nf mode t3 : t4' : map (nf mode) ts
        in case (t2' == t4' || isStationary t1', isICon ILeft  t2' && isICon IRight t4',
                                                 isICon IRight t2' && isICon ILeft  t4', collect t1') of
            (True, _, _, _) -> goStep t3 ts
            (_, True, _, (Just (Semantics _ Iso), [_,_,c,_,_,_])) -> goStep c (t3:ts)
            (_, _, True, (Just (Semantics _ Iso), [_,_,_,c,_,_])) -> goStep c (t3:ts)
            (_, b1, b2, _) | b1 || b2 -> case collect $ nfSemantics NF (Semantics S.App App) [fmap Free t1', Var Bound] of
                (Just (Semantics _ Iso), [c1, c2, c3, c4, c5, c6, Var Bound]) -> case map sequenceA [c1,c2,c3,c4,c5,c6] of
                    [Free{}, Free{}, Free c3', Free c4', Free{}, Free{}] -> if b1 then goStep c3' (t3:ts) else goStep c4' (t3:ts)
                    _ -> r
                _ -> r
            _ -> r
    go t@(Semantics _ Iso) _ ts@[t1,t2,_,_,_,_,t7] = case nf WHNF t7 of
        Apply (Semantics _ (ICon ILeft))  _ -> goStep t1 []
        Apply (Semantics _ (ICon IRight)) _ -> goStep t2 []
        _                                   -> capps t (nfs mode ts)
    go t@(Semantics _ Squeeze) _ [t1,t2] = case (nf WHNF t1, nf WHNF t2) of
        (Apply t@(Semantics _ (ICon ILeft))  _, _)  -> cterm t
        (Apply (Semantics _ (ICon IRight)) _, j)    -> if mode == Step then j else nf mode j
        (_, Apply t@(Semantics _ (ICon ILeft))  _)  -> cterm t
        (i, Apply (Semantics _ (ICon IRight)) _)    -> if mode == Step then i else nf mode i
        (t1',t2')                                   -> capps t $ nfs mode [t1',t2']
    go a as ts = apps (Apply a $ nfs mode as) (nfs mode ts)
    
    goTerm (Apply a as) ts = go a as ts
    goTerm t ts = apps t (nfs mode ts)
    
    goStep t ts = if mode == Step then apps t ts else goTerm t ts

nfType :: Eq a => NF -> Type Semantics a -> Type Semantics a
nfType mode (Type t lvl) = Type (nf mode t) lvl

isStationary :: Eq a => Term Semantics a -> Bool
isStationary t = case sequenceA $ nfSemantics NF (Semantics S.App App) [fmap Free t, Var Bound] of
    Free _  -> True
    Bound   -> False

nfs :: Eq a => NF -> [Term Semantics a] -> [Term Semantics a]
nfs WHNF terms = terms
nfs mode terms = map (nf mode) terms

instantiatePat :: Eq a => [PatternC s] -> Term Semantics a -> [Term Semantics a] -> Maybe (Term Semantics a, [Term Semantics a])
instantiatePat [] Lambda{} _ = Nothing
instantiatePat [] term terms = Just (term, terms)
instantiatePat (PatternVar _ : pats) (Lambda s) (term:terms) = instantiatePat pats (instantiate1 term s) terms
instantiatePat (PatternI _ con : pats) s (term:terms) = case nf WHNF term of
    Apply (Semantics _ (ICon i)) _ | i == con -> instantiatePat pats s terms
    _ -> Nothing
instantiatePat (Pattern (PatternCon con _ _ _) pats1 : pats) s (term:terms) = case collect (nf WHNF term) of
    (Just (Semantics _ (Con i _)), terms1) | i == con -> instantiatePat (pats1 ++ pats) s (terms1 ++ terms)
    _ -> Nothing
instantiatePat _ _ _ = Nothing

instantiateClauses :: Eq a => [([PatternC s], Closed (Term Semantics))]
    -> [Term Semantics a] -> Maybe (Term Semantics a, [Term Semantics a])
instantiateClauses clauses terms = msum $ map (\(pats, Closed s) -> instantiatePat pats s terms) clauses
