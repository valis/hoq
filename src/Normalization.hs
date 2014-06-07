module Normalization where

import Syntax.Term
import Syntax.Name

whnf :: Term a -> Term a
whnf e@Var{}      = e
whnf e@Universe{} = e
whnf e@Lam{}      = e
whnf e@Pi{}       = e
whnf e@Arr{}      = e
whnf (App e1 e2)  = go e1 [e2]
  where
    go (App a b) t = go a (b:t)
    go e t = case whnf e of
        Lam (Name vars e') ->
            let (t1,t2) = splitAt (length vars) t
            in whnf $ apps (instantiate (t1 !!) e') t2
        e'    -> apps e' t
