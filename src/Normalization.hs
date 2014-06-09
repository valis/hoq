module Normalization where

import Data.Maybe
import Control.Monad

import Syntax.Term
import Eval

data NF = NF | WNF | WHNF

nf :: NF -> Term (String, Maybe (Ref String Def Term)) -> Term (String, Maybe (Ref String Def Term))
nf mode (Var (_, Just (Ref (Syn _ t)))) = nf mode t
nf _ e@Var{}              = e
nf _ e@Universe{}         = e
nf WHNF e@Lam{}           = e
nf mode r@(Lam (Name v s))  = r -- Lam $ Name v $ toScope $ nf mode (fromScope s)
nf NF r@(Pi b e (Name v s)) = r -- Pi b (nf NF e) $ Name v $ toScope $ nf NF (fromScope s)
nf _ e@Pi{}               = e
nf NF (Arr e1 e2)         = Arr (nf NF e1) (nf NF e2)
nf _ e@Arr{}              = e
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
        v@(Var (_, Just (Ref (Syn _ term)))) -> nf mode (apps term t)
        v@(Var (_, Just (Ref (Def _ cases@(Name pats _ : _))))) ->
            let lpats = length pats
                (t1,t2) = splitAt lpats t
                lt1 = length t1
            in if lt1 < lpats
                then apps v (nfs mode t)
                else nf mode $ nf mode $ apps (instantiateCases cases $ map (nf mode) t1) t2
        e' -> apps e' (nfs mode t)

nfs :: NF -> [Term (String, Maybe (Ref String Def Term))] -> [Term (String, Maybe (Ref String Def Term))]
nfs WHNF terms = terms
nfs mode terms = map (nf mode) terms

instantiatePat :: Eq v => [Pattern v] -> [Term (v,a)] -> Maybe [Term (v,a)]
instantiatePat [] [] = Just []
instantiatePat (Pattern _ [] : pats) (term:terms) = fmap (term:) (instantiatePat pats terms)
instantiatePat (Pattern con pats1 : pats) (term:terms) = case collect [] term of
    (Var (v,_), terms1) | v == con -> liftM2 (++) (instantiatePat pats1 terms1) (instantiatePat pats terms)
    _ -> Nothing
  where
    collect acc (App e1 e2) = collect (e2:acc) e1
    collect acc e = (e, reverse acc)
instantiatePat _ _ = Nothing

instantiateCases :: Eq v => [Name [Pattern v] Int Term (v,a)] -> [Term (v,a)] -> Term (v,a)
instantiateCases cases terms = fromJust $ msum $ flip map cases $ \(Name pats term) ->
    fmap (\ts -> instantiate (ts !!) term) (instantiatePat pats terms)
