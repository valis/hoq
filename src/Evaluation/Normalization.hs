module Evaluation.Normalization where

import Bound
import Data.Maybe
import Control.Monad

import Syntax.Term
import Evaluation.Monad

data RTDef f a = RTCon Int | RTDef [Name [RTPattern] Int f a] | RTSyn (f a)
data RTPattern = RTPattern Int [RTPattern] | RTPatternVar

instance Bound RTDef where
    RTCon i     >>>= _ = RTCon i
    RTDef cases >>>= k = RTDef $ map (\(Name name term) -> Name name (term >>>= k)) cases
    RTSyn term  >>>= k = RTSyn (term >>= k)

data NF = NF | WNF | WHNF

nf :: NF -> Term (String, Maybe (Ref String RTDef Term)) -> Term (String, Maybe (Ref String RTDef Term))
nf mode (Var (_, Just (Ref (RTSyn t)))) = nf mode t
nf _ e@Var{}              = e
nf _ e@Universe{}         = e
nf WHNF e@Lam{}           = e
nf mode r@(Lam (Name v s))  = r -- Lam $ Name v $ toScope $ nf mode (fromScope s)
nf NF r@(Pi b e (Name v s)) = r -- Pi b (nf NF e) $ Name v $ toScope $ nf NF (fromScope s)
nf _ e@Pi{}               = e
nf NF (Arr e1 e2)         = Arr (nf NF e1) (nf NF e2)
nf _ e@Arr{}              = e
nf NF (Con c n es)        = Con c n $ map (nf NF) es
nf _ e@Con{}              = e
nf mode (App e1 e2)       = go e1 [e2]
  where
    go (App a b) t = go a (b:t)
    go e t = case nf mode e of
        Lam (Name vars e') ->
            let lvars = length vars
                (t1,t2) = splitAt lvars t
                lt1 = length t1
            in if lt1 < lvars
                then Lam $ Name (drop lt1 vars) $ Scope $ flip fmap (unscope e') $ \var -> case var of
                    B b -> if b < lt1 then F (t1 !! b) else B (b - lt1)
                    _ -> var
                else nf mode $ apps (instantiate (t1 !!) e') t2
        v@(Var (_, Just (Ref (RTSyn term)))) -> nf mode (apps term t)
        v@(Var (_, Just (Ref (RTDef cases@(Name pats _ : _))))) ->
            let lpats = length pats
                (t1,t2) = splitAt lpats t
                lt1 = length t1
            in if lt1 < lpats
                then apps v (nfs mode t)
                else nf mode $ apps (instantiateCases cases $ map (nf mode) t1) t2
        e' -> apps e' (nfs mode t)

nfs :: NF -> [Term (String, Maybe (Ref String RTDef Term))] -> [Term (String, Maybe (Ref String RTDef Term))]
nfs WHNF terms = terms
nfs mode terms = map (nf mode) terms

instantiatePat :: Eq v => [RTPattern] -> [Term (v,a)] -> Maybe [Term (v,a)]
instantiatePat [] [] = Just []
instantiatePat (RTPatternVar : pats) (term:terms) = fmap (term:) (instantiatePat pats terms)
instantiatePat (RTPattern con pats1 : pats) (term:terms) = case term of
    Con i n terms1 | i == con -> liftM2 (++) (instantiatePat pats1 terms1) (instantiatePat pats terms)
    _ -> Nothing
instantiatePat _ _ = Nothing

instantiateCases :: Eq v => [Name [RTPattern] Int Term (v,a)] -> [Term (v,a)] -> Term (v,a)
instantiateCases cases terms = fromJust $ msum $ flip map cases $ \(Name pats term) ->
    fmap (\ts -> instantiate (ts !!) term) (instantiatePat pats terms)
