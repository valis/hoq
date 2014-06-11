module Evaluation.Normalization
    ( NF(..), nf
    ) where

import Bound
import Control.Monad

import Syntax.Term
import Evaluation.Monad

data NF = NF | WNF | WHNF deriving Eq

nf :: NF -> Term a -> Term a
nf mode e = go e []
  where
    go (App a b)            ts = go a (b:ts)
    go e@Var{}              ts = apps e (nfs mode ts)
    go e@Universe{}         _  = e
    go (Pi b e (Name v s))  _  | mode == NF = Pi b (nf NF e) $ Name v $ toScope $ nf NF (fromScope s)
    go e@Pi{}               _  = e
    go (Arr e1 e2)          _  | mode == NF = Arr (nf NF e1) (nf NF e2)
    go e@Arr{}              _  = e
    go (Con c n es)         [] = Con c n $ if mode == NF then map (nf NF) es else es
    go (Con c n es)         ts = Con c n $ if mode == NF then map (nf NF) (es ++ ts) else es ++ ts
    go (Lam (Name vars e)) ts =
        let lvars = length vars
            (t1,t2) = splitAt lvars ts
            lt1 = length t1
            nfm = if mode == WHNF then id else nf mode
        in if lt1 < lvars
            then Lam $ Name (drop lt1 vars) $ Scope $ nfm $ flip fmap (unscope e) $ \var -> case var of
                B b -> if b < lt1 then F (t1 !! b) else B (b - lt1)
                _ -> var
            else go (instantiate (t1 !!) e) t2
    go (FunSyn _ term) ts = go term ts
    go fc@(FunCall _ []) ts = apps fc (nfs mode ts)
    go fc@(FunCall _ cases@(Name pats _ : _)) ts =
        let lpats = length pats
            (t1,t2) = splitAt lpats ts
            lt1 = length t1
        in case (lt1 < lpats, instantiateCases cases t1) of
            (True , _      ) -> apps fc (nfs mode ts)
            (False, Just r ) -> go r t2
            (False, Nothing) -> apps fc (nfs mode ts)

nfs :: NF -> [Term a] -> [Term a]
nfs NF terms = map (nf NF) terms
nfs _  terms = terms

instantiatePat :: [RTPattern] -> [Term a] -> Maybe [Term a]
instantiatePat [] [] = Just []
instantiatePat (RTPatternVar : pats) (term:terms) = fmap (term:) (instantiatePat pats terms)
instantiatePat (RTPattern con pats1 : pats) (term:terms) = case nf WHNF term of
    Con i n terms1 | i == con -> liftM2 (++) (instantiatePat pats1 terms1) (instantiatePat pats terms)
    _ -> Nothing
instantiatePat _ _ = Nothing

instantiateCases :: [Names RTPattern Term a] -> [Term a] -> Maybe (Term a)
instantiateCases cases terms = msum $ flip map cases $ \(Name pats term) ->
    fmap (\ts -> instantiate (ts !!) term) (instantiatePat pats terms)
