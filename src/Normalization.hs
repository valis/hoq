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
nf mode (Var a ts) = Var a (nfs mode ts)
nf mode (Apply t ts) = nfSemantics mode t ts
nf mode (Lambda t) = Lambda $ if mode == WHNF then t else nf mode t

nfSemantics :: Eq a => NF -> Semantics -> [Term Semantics a] -> Term Semantics a
nfSemantics mode (Semantics (S.Lam (_:vs)) Lam) (Lambda a@Lambda{} : t : ts) =
    nfStep mode $ Apply (Semantics (S.Lam vs) Lam) (instantiate1 t a : ts)
nfSemantics mode (Semantics _ Lam) (Lambda s : t : ts) = nfStep mode $ apps (instantiate1 t s) ts
nfSemantics mode t@(Semantics _ (DCon _ k conds)) ts =
    let (params,args) = splitAt k ts
    in case instantiateClauses (map (\(pats, Closed term) -> (pats, apps term params)) conds) args of
        Just (t', ts')  -> nfStep mode (apps t' ts')
        _               -> Apply t (nfs mode ts)
nfSemantics mode t@(Semantics _ (FunCall _ clauses)) ts =
    case instantiateClauses (map (\(pats, Closed term) -> (pats, term)) clauses) ts of
        Just (t', ts')  -> nfStep mode (apps t' ts')
        _               -> Apply t (nfs mode ts)
nfSemantics mode t@(Semantics _ (Conds k conds)) (term : ts) =
    let (params,args) = splitAt k ts
    in case instantiateClauses (map (\(pats, Closed term) -> (pats, apps term params)) conds) args of
        Just (t', ts')  -> nfStep mode (apps t' ts')
        _               -> Apply t (nfs mode ts)
nfSemantics mode t@(Semantics _ At) (t1:t2:t3:t4:ts) = case (nf WHNF t3, nf WHNF t4) of
    (_, Apply (Semantics _ (ICon ILeft))  _) -> nfStep mode (apps t1 ts)
    (_, Apply (Semantics _ (ICon IRight)) _) -> nfStep mode (apps t2 ts)
    (Apply (Semantics _ PCon) [t3'], t4')    -> nfStep mode $ apps t3' (t4':ts)
    (t3', t4')                               -> Apply t $ nfs mode (t1:t2:t3':t4':ts)
nfSemantics mode t@(Semantics _ Coe) (t1:t2:t3:t4:ts) =
    let t1' = nf WHNF t1
        t2' = nf NF t2
        t4' = nf NF t4
        isICon c (Apply (Semantics _ (ICon c')) _) = c == c'
        isICon _ _ = False
        r = Apply t $ if mode == WHNF then t1':t2':t3:t4':ts else nf mode t1' : t2' : nf mode t3 : t4' : map (nf mode) ts
    in case (t2' == t4' || isStationary t1', isICon ILeft  t2' && isICon IRight t4',
                                             isICon IRight t2' && isICon ILeft  t4', t1') of
        (True, _, _, _) -> nfStep mode (apps t3 ts)
        (_, True, _, (Apply (Semantics _ Iso) [_,_,c,_,_,_])) -> nfStep mode $ apps c (t3:ts)
        (_, _, True, (Apply (Semantics _ Iso) [_,_,_,c,_,_])) -> nfStep mode $ apps c (t3:ts)
        (_, b1, b2, _) | b1 || b2 -> case nf NF $ apps (fmap Free t1') [bvar] of
            Apply (Semantics _ Iso) [c1, c2, c3, c4, c5, c6, Var Bound []] -> case map sequenceA [c1,c2,c3,c4,c5,c6] of
                [Free{}, Free{}, Free c3', Free c4', Free{}, Free{}] -> nfStep mode $ apps (if b1 then c3' else c4') (t3:ts)
                _ -> r
            _ -> r
        _ -> r
nfSemantics mode t@(Semantics _ Iso) ts@[t1,t2,_,_,_,_,t7] = case nf WHNF t7 of
    Apply (Semantics _ (ICon ILeft))  _ -> nfStep mode t1
    Apply (Semantics _ (ICon IRight)) _ -> nfStep mode t2
    _                                   -> Apply t (nfs mode ts)
nfSemantics mode t@(Semantics _ Squeeze) [t1,t2] = case (nf WHNF t1, nf WHNF t2) of
    (Apply t@(Semantics _ (ICon ILeft))  _, _)  -> capply t
    (Apply (Semantics _ (ICon IRight)) _, j)    -> if mode == Step then j else nf mode j
    (_, Apply t@(Semantics _ (ICon ILeft))  _)  -> capply t
    (i, Apply (Semantics _ (ICon IRight)) _)    -> if mode == Step then i else nf mode i
    (t1',t2')                                   -> Apply t $ nfs mode [t1',t2']
nfSemantics mode t@(Semantics _ (Case pats)) (term:terms) =
    let (terms1,terms2) = splitAt (length pats) terms
    in case instantiateCaseClauses (zipWith (\pat te -> ([pat], te)) pats terms1) [term] of
        Just (t', ts')  -> nfStep mode $ apps t' (ts' ++ terms2)
        _               -> Apply t $ nfs mode (term:terms)
nfSemantics mode t@(Semantics _ (FieldAcc i conds)) (term:terms) = case nf WHNF term of
    Apply (Semantics _ (DCon _ k _)) args | arg:_ <- drop (k + i) args -> nfStep mode (apps arg terms)
    term' -> case instantiateClauses (map (\(pats, Closed term) -> (pats, term)) conds) terms of
        Just (t', ts')  -> nfStep mode (apps t' ts')
        _               -> Apply t $ nfs mode (term':terms)
nfSemantics mode a as = Apply a (nfs mode as)

nfStep :: Eq a => NF -> Term Semantics a -> Term Semantics a
nfStep Step t = t
nfStep mode t = nf mode t

nfType :: Eq a => NF -> Type Semantics a -> Type Semantics a
nfType mode (Type t lvl) = Type (nf mode t) lvl

isStationary :: Eq a => Term Semantics a -> Bool
isStationary t = case sequenceA $ nf NF $ apps (fmap Free t) [bvar] of
    Free _  -> True
    Bound   -> False

nfs :: Eq a => NF -> [Term Semantics a] -> [Term Semantics a]
nfs WHNF terms = terms
nfs mode terms = map (nf mode) terms

getCon :: Term Semantics a -> Maybe (Int, [Term Semantics a])
getCon (Apply (Semantics _ (ICon ILeft )) terms) = Just (0, terms)
getCon (Apply (Semantics _ (ICon IRight)) terms) = Just (1, terms)
getCon (Apply (Semantics _ PCon         ) terms) = Just (0, terms)
getCon (Apply (Semantics _ (DCon i k _ )) terms) = Just (i, drop k terms)
getCon _                                         = Nothing

instantiatePat :: Eq a => [Term Int t] -> Term Semantics a -> [Term Semantics a] -> Maybe (Term Semantics a, [Term Semantics a])
instantiatePat [] Lambda{} _ = Nothing
instantiatePat [] term terms = Just (term, terms)
instantiatePat (Var{} : pats) (Lambda s) (term:terms) = instantiatePat pats (instantiate1 term s) terms
instantiatePat (Apply con pats1 : pats) s (term:terms) = case getCon (nf WHNF term) of
    Just (con', terms1) | con == con' && length pats1 == length terms1 -> instantiatePat (pats1 ++ pats) s (terms1 ++ terms)
    _ -> Nothing
instantiatePat _ _ _ = Nothing

instantiateClauses :: Eq a => [([Term Int t], Term Semantics a)]
    -> [Term Semantics a] -> Maybe (Term Semantics a, [Term Semantics a])
instantiateClauses clauses terms = msum $ map (\(pats, s) -> instantiatePat pats s terms) clauses

instantiateCaseClauses :: Eq a => [([Term Int t], Term Semantics a)]
    -> [Term Semantics a] -> Maybe (Term Semantics a, [Term Semantics a])
instantiateCaseClauses clauses terms = msum $ map (\(pats, s) -> instantiatePat pats s terms) clauses
