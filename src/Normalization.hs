module Normalization
    ( NF(..), nf
    ) where

import Control.Monad
import Data.Traversable

import Syntax.Term

data NF = NF | HNF | WHNF deriving Eq

nf :: (Show a, Eq a) => NF -> Term a -> Term a
nf mode e = go e []
  where
    go (App a b)            ts = go a (b:ts)
    go e@Var{}              ts = apps e (nfs mode ts)
    go e@Universe{}         _  = e
    go (Pi b e (Name v s))  _  | mode == NF = Pi b (nf NF e) $ Name v $ toScope $ nf NF (fromScope s)
    go e@Pi{}               _  = e
    go (Arr e1 e2)          _  | mode == NF = Arr (nf NF e1) (nf NF e2)
    go e@Arr{}              _  = e
    go e@Interval           _  = e
    go e@(ICon _)           _  = e
    go (PCon Nothing)       [] = PCon Nothing
    go (PCon Nothing)    (e:_) = PCon $ Just $ if mode == NF then nf NF e                else e
    go (PCon (Just e))      _  = PCon $ Just $ if mode == NF then nf NF e                else e
    go (Con c n es)         [] = Con c n     $ if mode == NF then map (nf NF) es         else es
    go (Con c n es)         ts = Con c n     $ if mode == NF then map (nf NF) (es ++ ts) else es ++ ts
    go (DataType d es)      [] = DataType d  $ if mode == NF then map (nf NF) es         else es
    go (DataType d es)      ts = DataType d  $ if mode == NF then map (nf NF) (es ++ ts) else es ++ ts
    go (Path es)            [] = Path        $ if mode == NF then map (nf NF) es         else es
    go (Path es)            ts = Path        $ if mode == NF then map (nf NF) (es ++ ts) else es ++ ts
    go (PathImp ma b c)     _  | mode == NF = PathImp (fmap (nf NF) ma) (nf NF b) (nf NF c)
    go e@PathImp{}          _  = e
    go (Lam (Name vars e)) ts =
        let lvars = length vars
            (t1,t2) = splitAt lvars ts
            lt1 = length t1
            nfm = if mode == WHNF then id else nf mode
        in if lt1 < lvars
            then Lam $ Name (drop lt1 vars) $ Scope $ nfm $ unscope e >>= \var -> case var of
                B b -> if b < lt1 then fmap (F . Var) (t1 !! b) else return $ B (b - lt1)
                _   -> return var
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
    go (At a b e1 e2) ts = case (nf WHNF e1, nf WHNF e2) of
        (_, ICon ILeft)      -> go a ts
        (_, ICon IRight)     -> go b ts
        (PCon (Just t1), t2) -> go t1 (t2:ts)
        (t1, t2)             -> apps (At (go a []) (go b []) (go t1 []) (go t2 [])) (nfs mode ts)
    go (Coe es) ts = case es ++ ts of
        e1:e2:e3:e4:es' | nf NF e2 == nf NF e4 || isStationary e1 -> go e3 es'
        es'                                                       -> Coe (nfs mode es')
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

isStationary :: (Eq a, Show a) => Term a -> Bool
isStationary t = case sequenceA (nf NF $ App (fmap F t) $ Var $ B ()) of
    F _ -> True
    B _ -> False

nfs :: (Eq a, Show a) => NF -> [Term a] -> [Term a]
nfs NF terms = map (nf NF) terms
nfs _  terms = terms

instantiatePat :: (Eq a, Show a) => [RTPattern] -> [Term a] -> Maybe [Term a]
instantiatePat [] [] = Just []
instantiatePat (RTPatternVar : pats) (term:terms) = fmap (term:) (instantiatePat pats terms)
instantiatePat (RTPattern con pats1 : pats) (term:terms) = case nf WHNF term of
    Con i n terms1 | i == con -> liftM2 (++) (instantiatePat pats1 terms1) (instantiatePat pats terms)
    _ -> Nothing
instantiatePat (RTPatternI con : pats) (term:terms) = case nf WHNF term of
    ICon i | i == con -> instantiatePat pats terms
    _ -> Nothing
instantiatePat _ _ = Nothing

instantiateCases :: (Eq a, Show a) => [Names RTPattern Term a] -> [Term a] -> Maybe (Term a)
instantiateCases cases terms = msum $ flip map cases $ \(Name pats term) ->
    fmap (\ts -> instantiate (ts !!) term) (instantiatePat pats terms)
