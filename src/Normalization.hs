module Normalization
    ( NF(..), nf
    , nfType, nfScope
    ) where

import Control.Monad
import Data.Traversable

import Syntax.Term

data NF = NF | HNF | WHNF deriving Eq

nf :: Eq a => NF -> Term p a -> Term p a
nf mode e = go e []
  where
    go (App a b)            ts = go a (b:ts)
    go e@Var{}              ts = apps e (nfs mode ts)
    go e@Universe{}         _  = e
    go (Pi p a b lvl)       _  | mode == NF = Pi p (nfType NF a) (nfScope b) lvl
    go e@Pi{}               _  = e
    go e@Interval{}         _  = e
    go e@ICon{}             _  = e
    go (PCon p Nothing)     [] = PCon p Nothing
    go (PCon p Nothing)  (e:_) = PCon p $ Just $ if mode == NF then nf NF e else e
    go (PCon p (Just e))    _  = PCon p $ Just $ if mode == NF then nf NF e else e
    go (Con p c n [] es)    [] = Con p c n [] $ nfs mode es
    go (Con p c n [] es)    ts = Con p c n [] $ nfs mode (es ++ ts)
    go (DataType p d e es)  [] = DataType p d e $ nfs mode es
    go (DataType p d e es)  ts = DataType p d e $ nfs mode (es ++ ts)
    go (Path p h ma es)     [] = Path p h (if mode == NF then fmap (nf NF) ma else ma) $ nfs mode es
    go (Path p h ma es)     ts = Path p h (if mode == NF then fmap (nf NF) ma else ma) $ nfs mode (es ++ ts)
    go (Lam p (Scope1 v t)) [] = Lam p $ Scope1 v $ if mode == WHNF then t else nf mode t
    go (Lam _ (Scope1 _ s)) (t:ts) = go (instantiate1 t s) ts
    go (FunSyn _ _ term)    ts = go term ts
    go (Con p c n conds es) ts =
        let es' = if null ts then es else es ++ ts in
        case instantiateCases conds es' of
            Just (r,ts') -> go r ts'
            Nothing      -> Con p c n conds (if mode == NF then map (nf NF) es' else es')
    go fc@(FunCall _ _ []) ts = apps fc (nfs mode ts)
    go fc@(FunCall _ _ clauses) ts = case instantiateCases clauses ts of
        Just (r,ts') -> go r ts'
        Nothing      -> apps fc (nfs mode ts)
    go (At mab e1 e2) ts = case (mab, nf WHNF e1, nf WHNF e2) of
        (_, PCon _ (Just t1), t2)       -> go t1 (t2:ts)
        (Just (a,_), _, ICon _ ILeft)   -> go a ts
        (Just (_,b), _, ICon _ IRight)  -> go b ts
        (Nothing   , t1, t2)            -> apps (At Nothing (go t1 []) (go t2 [])) (nfs mode ts)
        (Just (a,b), t1, t2)            -> apps (At (Just (go a [], go b [])) (go t1 []) (go t2 [])) (nfs mode ts)
    go (Coe p es) ts = case es ++ ts of
        es'@(e1:e2:e3:e4:es'') ->
            let e1' = nf WHNF e1
                e2' = nf NF e2
                e4' = nf NF e4
            in case (e2' == e4' || isStationary e1', e2' == ICon (error "") ILeft  && e4' == ICon (error "") IRight,
                                                     e2' == ICon (error "") IRight && e4' == ICon (error "") ILeft, e1') of
                (True, _, _, _) -> go e3 es''
                (_, b1, b2, Iso _ [t1,t2,t3,t4,t5,t6]) | b1 || b2 -> go (App (if b1 then t3 else t4) e3) es''
                (_, b1, b2, _) | b1 || b2 -> case nf NF $ App (fmap Free e1') (Var Bound) of
                    Iso p [t1,t2,t3,t4,t5,t6, Var Bound] -> case sequenceA $ Iso p [t1,t2,t3,t4,t5,t6] of
                        Free (Iso _ [t1',t2',t3',t4',t5',t6']) -> go (App (if b1 then t3' else t4') e3) es''
                        _ -> Coe p (nfs mode es')
                    _ -> Coe p (nfs mode es')
                _ -> Coe p (nfs mode es')
        es' -> Coe p (nfs mode es')
    go (Iso p es) ts = case map (nf WHNF) (es ++ ts) of
        t1:t2:t3:t4:t5:t6: ICon _ ILeft  : _ -> go t1 []
        t1:t2:t3:t4:t5:t6: ICon _ IRight : _ -> go t2 []
        _                                    -> Iso p $ nfs mode (es ++ ts)
    go (Squeeze p es) ts = case map (nf WHNF) (es ++ ts) of
        ICon p' ILeft : _ : _ -> ICon p' ILeft
        ICon _ IRight : j : _ -> if mode == WHNF then j else nf mode j
        _ : ICon p' ILeft : _ -> ICon p' ILeft
        i : ICon _ IRight : _ -> if mode == WHNF then i else nf mode i
        es'                   -> Squeeze p $ nfs mode (es ++ ts)

nfType :: Eq a => NF -> Type p a -> Type p a
nfType mode (Type t lvl) = Type (nf mode t) lvl

nfScope :: Eq a => Scope s (Term p) a -> Scope s (Term p) a
nfScope (ScopeTerm t) = ScopeTerm (nf NF t)
nfScope (Scope v   s) = Scope v (nfScope s)

isStationary :: Eq a => Term p a -> Bool
isStationary t = case sequenceA (nf NF $ App (fmap Free t) $ Var Bound) of
    Free _ -> True
    Bound  -> False

nfs :: Eq a => NF -> [Term p a] -> [Term p a]
nfs NF terms = map (nf NF) terms
nfs _  terms = terms

instantiatePat :: Eq a => [Pattern p c s] -> Scope b (Term p) a -> [Term p a] -> Maybe (Term p a, [Term p a])
instantiatePat [] (ScopeTerm term) terms = Just (term, terms)
instantiatePat (PatternVar _ : pats) (Scope _ scope) (term:terms) = instantiatePat pats (instantiateScope term scope) terms
instantiatePat (PatternI _ con : pats) scope (term:terms) = case nf WHNF term of
    ICon _ i | i == con -> instantiatePat pats scope terms
    _ -> Nothing
instantiatePat (Pattern (PatternCon con _ _ _) pats1 : pats) scope (term:terms) = case nf WHNF term of
    Con _ i n _ terms1 | i == con -> instantiatePat (pats1 ++ pats) scope (terms1 ++ terms)
    _ -> Nothing
instantiatePat _ _ _ = Nothing

instantiateCases :: Eq a => [([Pattern p c s], Closed (Scope b (Term p)))] -> [Term p a] -> Maybe (Term p a, [Term p a])
instantiateCases clauses terms = msum $ map (\(pats, Closed scope) -> instantiatePat pats scope terms) clauses
