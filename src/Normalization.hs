module Normalization where

import Syntax.Term
import Eval

data NF = NF | WNF | WHNF

nf :: NF -> Term (v, Maybe (Ref v Def Term)) -> Term (v, Maybe (Ref v Def Term))
nf _ (Var (_, Just (Ref (Syn _ t)))) = t
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
        v@(Var (_, Just (Ref (Def _ (Name args term))))) ->
            let largs = length args
                (t1,t2) = splitAt largs t
                lt1 = length t1
            in if lt1 < largs
                then apps v t
                else nf mode $ apps (instantiate (t1 !!) term) t2
        e' -> apps e' t
