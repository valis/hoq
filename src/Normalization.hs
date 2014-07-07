module Normalization
    ( NF(..), nf
    ) where

import Control.Monad
import Data.Traversable

import Syntax.Term

data NF = NF | HNF | WHNF deriving Eq

nf :: Eq a => NF -> Term a -> Term a
nf mode e = go e []
  where
    go (App a b)          ts = go a (b:ts)
    go e@Var{}            ts = apps e (nfs mode ts)
    go e@Universe{}       _  = e
    go (Pi a b)           _  | mode == NF = Pi (nf NF a) (nfScope b)
      where
        nfScope :: Eq a => Scope s Term a -> Scope s Term a
        nfScope (ScopeTerm t) = ScopeTerm (nf NF t)
        nfScope (Scope v   s) = Scope v (nfScope s)
    go e@Pi{}             _  = e
    go e@Interval         _  = e
    go e@(ICon _)         _  = e
    go (PCon Nothing)     [] = PCon Nothing
    go (PCon Nothing)  (e:_) = PCon $ Just  $ if mode == NF then nf NF e else e
    go (PCon (Just e))    _  = PCon $ Just  $ if mode == NF then nf NF e else e
    go (Con c n [] es)    [] = Con c n []   $ nfs mode es
    go (Con c n [] es)    ts = Con c n []   $ nfs mode (es ++ ts)
    go (DataType d e es)  [] = DataType d e $ nfs mode es
    go (DataType d e es)  ts = DataType d e $ nfs mode (es ++ ts)
    go (Path h ma es)     [] = Path h (if mode == NF then fmap (nf NF) ma else ma) $ nfs mode es
    go (Path h ma es)     ts = Path h (if mode == NF then fmap (nf NF) ma else ma) $ nfs mode (es ++ ts)
    go (Lam (Scope1 v t)) [] = Lam $ Scope1 v $ if mode == WHNF then t else nf mode t
    go (Lam s)        (t:ts) = go (instantiate1 t s) ts
    go (FunSyn _ term)    ts = go term ts
    go (Con c n conds es) ts =
        let es' = if null ts then es else es ++ ts in
        case instantiateCases conds es' of
            Just (r,ts') -> go r ts'
            Nothing      -> Con c n conds (if mode == NF then map (nf NF) es' else es')
    go fc@(FunCall _ []) ts = apps fc (nfs mode ts)
    go fc@(FunCall _ cases) ts = case instantiateCases cases ts of
        Just (r,ts') -> go r ts'
        Nothing      -> apps fc (nfs mode ts)
    go (At a b e1 e2) ts = case (nf WHNF e1, nf WHNF e2) of
        (_, ICon ILeft)      -> go a ts
        (_, ICon IRight)     -> go b ts
        (PCon (Just t1), t2) -> go t1 (t2:ts)
        (t1, t2)             -> apps (At (go a []) (go b []) (go t1 []) (go t2 [])) (nfs mode ts)
    go (Coe es) ts = case es ++ ts of
        es'@(e1:e2:e3:e4:es'') ->
            let e1' = nf WHNF e1
                e2' = nf NF e2
                e4' = nf NF e4
            in case (e2' == e4' || isStationary e1', e2' == ICon ILeft && e4' == ICon IRight,
                                                     e2' == ICon IRight && e4' == ICon ILeft, e1') of
                (True, _, _, _) -> go e3 es''
                (_, b1, b2, Iso [t1,t2,t3,t4,t5,t6]) | b1 || b2 -> go (App (if b1 then t3 else t4) e3) es''
                (_, b1, b2, _) | b1 || b2 -> case nf NF $ App (fmap Free e1') (Var Bound) of
                    Iso [t1,t2,t3,t4,t5,t6, Var Bound] -> case sequenceA $ Iso [t1,t2,t3,t4,t5,t6] of
                        Free (Iso [t1',t2',t3',t4',t5',t6']) -> go (App (if b1 then t3' else t4') e3) es''
                        _ -> Coe (nfs mode es')
                    _ -> Coe (nfs mode es')
                _ -> Coe (nfs mode es')
        es' -> Coe (nfs mode es')
    go (Iso es) ts = case map (nf WHNF) (es ++ ts) of
        t1:t2:t3:t4:t5:t6: ICon ILeft  : _ -> go t1 []
        t1:t2:t3:t4:t5:t6: ICon IRight : _ -> go t2 []
        _                                  -> Iso $ nfs mode (es ++ ts)
    go (Squeeze es) ts = case map (nf WHNF) (es ++ ts) of
        ICon ILeft  : _ : _ -> ICon ILeft
        ICon IRight : j : _ -> if mode == WHNF then j else nf mode j
        _ : ICon ILeft  : _ -> ICon ILeft
        i : ICon IRight : _ -> if mode == WHNF then i else nf mode i
        es'                 -> Squeeze $ nfs mode (es ++ ts)

isStationary :: Eq a => Term a -> Bool
isStationary t = case sequenceA (nf NF $ App (fmap Free t) $ Var Bound) of
    Free _ -> True
    Bound  -> False

nfs :: Eq a => NF -> [Term a] -> [Term a]
nfs NF terms = map (nf NF) terms
nfs _  terms = terms

instantiatePat :: Eq a => [Pattern] -> Scope () Term a -> [Term a] -> Maybe (Term a, [Term a])
instantiatePat [] (ScopeTerm term) terms = Just (term, terms)
instantiatePat (PatternAny : pats) scope (_:terms) = instantiatePat pats scope terms
instantiatePat (PatternVar : pats) (Scope _ scope) (term:terms) = instantiatePat pats (instantiate term scope) terms
instantiatePat (PatternI con : pats) scope (term:terms) = case nf WHNF term of
    ICon i | i == con -> instantiatePat pats scope terms
    _ -> Nothing
instantiatePat (Pattern con pats1 : pats) scope (term:terms) = case nf WHNF term of
    Con i n _ terms1 | i == con -> instantiatePat (pats1 ++ pats) scope (terms1 ++ terms)
    _ -> Nothing
instantiatePat _ _ _ = Nothing

instantiateCases :: Eq a => [([Pattern], Closed (Scope () Term))] -> [Term a] -> Maybe (Term a, [Term a])
instantiateCases cases terms = msum $ map (\(pats, Closed scope) -> instantiatePat pats scope terms) cases
