module Normalization where

import Syntax.Term

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
            let lvars = length vars
                (t1,t2) = splitAt lvars t
                lt1 = length t1
            in if lt1 < lvars
                then Lam $ Name (drop lt1 vars) $ Scope $ flip fmap (unscope e') $ \var -> case var of
                    B b | b >= lvars - lt1 -> F $ t1 !! (lvars - b - 1)
                    _ -> var
                else whnf $ apps (instantiate (t1 !!) e') t2
        e' -> apps e' t
