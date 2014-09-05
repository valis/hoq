{-# LANGUAGE GADTs #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Data.List
import Data.Void

import Syntax as S
import Semantics
import Semantics.Value as V
import Semantics.Pattern as P
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context as C
import TypeChecking.Expressions
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Patterns
-- import TypeChecking.Expressions.Conditions
import TypeChecking.Expressions.Telescopes
import TypeChecking.Definitions.Termination
import Normalization

typeCheckDataType :: Monad m => PName -> [Tele] -> [S.Con] -> [S.Clause] -> TCM m ()
typeCheckDataType p@(_, dt) params cons conds = do
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- typeCheckTelescope C.Nil params $ Type (universe Prop) (Set NoLevel)
    dtID <- addDataTypeCheck p lcons (closed dataType)
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(pos, conName) tele, i) -> do
        (_, conType) <- typeCheckTelescope ctx tele $
            Type (Apply (Semantics (Name Prefix dt) $ DataType dtID lcons) $ ctxToVars ctx) Prop
        case findOccurrence dtID (nf WHNF $ getType conType) of
            Just n | n > 1 -> throwError [Error Other $ emsgLC pos "Data type is not strictly positive" enull]
            _ -> return ()
        return $ Just (con, i, conType)
    let ks = map (\(_, _, Type _ k) -> k) cons'
        mk = dmaximum $ (if lcons > 1 then Set NoLevel else Prop) : ks
    forM_ cons' $ \(con, i, Type ty k) -> addConstructorCheck con dtID i [] [] $
        closed $ Type (abstractTerm ctx $ replaceSort ty mk Nothing) mk
    conds' <- forW conds $ \(S.Clause (pos, con) pats expr) ->
        case find (\((_, c), _, _) -> c == con) cons' of
            Just ((_, conName), i, ty) -> do
                (bf, TermsInCtx ctx' rtpats _ ty') <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [Error Other $ emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx C.+++ ctx') expr $ Just (nfType WHNF ty')
                throwErrors $ checkTermination (Left i) pos (patternsToTerms rtpats) ctx (abstractTerm ctx' term)
                return $ Just (conName, (pos, P.Clause rtpats term))
            _ -> do
                warn [notInScope pos "data constructor" (nameToString con)]
                return Nothing
    lift $ replaceDataType dt lcons $ closed $ Type (replaceSort dtTerm (succ mk) $ Just mk) mk
    let cons'' = map (\((_, con), i, ty) -> (con, i, ty, map snd $ filter (\(c,_) -> c == con) conds')) cons'
        toPClause (_,c) = ParameterizedClause $ clauseAToClause . instantiateClauseA ctx (clauseToClauseA c)
    forM_ cons'' $ \(con, i, Type ty k, conds'') -> lift $ replaceConstructor con dtID i (map toPClause conds'')
        (map (\(_,c) -> (fst $ clauseToEval c, closed $ abstractTerm ctx $ snd $ clauseToEval c)) conds'') $
        closed $ Type (abstractTerm ctx $ replaceSort ty mk Nothing) mk
    {-
    forM_ cons'' $ \(con, i, _, conds'') ->
        let conTerm = Semantics (Name Prefix con) $ Con $ DCon i lcons $ map (\(_,b,c) -> (b,c)) conds''
        in warn $ checkConditions ctx (capply conTerm) $ map (\(pos, p, Closed t) -> (pos, p, t)) conds''
    -}

data PatternA b = PatDConA Int Int [ClauseA b] [PatternA b] | PatPConA (PatternA b) | PatIConA ICon | PatVarA String
data ClauseA b = ClauseA [PatternA b] (Term Semantics b)

instance Functor PatternA where
    fmap f (PatDConA i n cs ps) = PatDConA i n (map (fmap f) cs) $ map (fmap f) ps
    fmap f (PatPConA p) = PatPConA (fmap f p)
    fmap _ (PatIConA c) = PatIConA c
    fmap _ (PatVarA  v) = PatVarA v

instance Functor ClauseA where
    fmap f (ClauseA ps t) = ClauseA (map (fmap f) ps) (fmap f t)

clauseToClauseA :: P.Clause b -> ClauseA b
clauseToClauseA (P.Clause P.Nil term) = ClauseA [] term
clauseToClauseA (P.Clause (Cons (PatDCon i n cs ps) pats) term) =
    let ClauseA pats' term' = clauseToClauseA $ P.Clause (ps P.+++ pats) term
        (pats1,pats2) = splitAt (patternsLength ps) pats'
    in  ClauseA (PatDConA i n (map clauseToClauseA cs) pats1 : pats2) term'
clauseToClauseA (P.Clause (Cons (PatPCon p) pats) term) =
    let ClauseA pats' term' = clauseToClauseA $ P.Clause (Cons p pats) term
    in  ClauseA (PatPConA (head pats') : tail pats') term'
clauseToClauseA (P.Clause (Cons (PatICon con) pats) term) =
    let ClauseA pats' term' = clauseToClauseA (P.Clause pats term)
    in  ClauseA (PatIConA con : pats') term'
clauseToClauseA (P.Clause (Cons (PatVar var) pats) term) =
    let ClauseA pats' term' = clauseToClauseA (P.Clause pats term)
    in  ClauseA (PatVarA var : map abstractPatternA1 pats') (Lambda term')
  where
    abstractPatternA1 :: PatternA (Scoped b) -> PatternA b
    abstractPatternA1 (PatDConA i n cs ps) = PatDConA i n
        (map (\(ClauseA ps' t) -> ClauseA (map abstractPatternA1 ps') $ Lambda t) cs)
        (map abstractPatternA1 ps)
    abstractPatternA1 (PatPConA p) = PatPConA (abstractPatternA1 p)
    abstractPatternA1 (PatIConA con) = PatIConA con
    abstractPatternA1 (PatVarA var) = PatVarA var

clauseAToClause :: ClauseA b -> P.Clause b
clauseAToClause (ClauseA [] term) = P.Clause P.Nil term
clauseAToClause (ClauseA (PatDConA i n cs ps : pats) term) = case clauseAToClause $ ClauseA (ps ++ pats) term of
    P.Clause pats' term' -> case patternsSplitAt pats' (length ps) of
        Split pats1 pats2 -> P.Clause (Cons (PatDCon i n (map clauseAToClause cs) pats1) pats2) term'
clauseAToClause (ClauseA (PatPConA p : pats) term) = case clauseAToClause $ ClauseA (p:pats) term of
    P.Clause (Cons p' pats') term' -> P.Clause (Cons (PatPCon p') pats') term'
    _ -> error "clauseAToClause"
clauseAToClause (ClauseA (PatIConA c : pats) term) = case clauseAToClause (ClauseA pats term) of
    P.Clause pats' term' -> P.Clause (Cons (PatICon c) pats') term'
clauseAToClause (ClauseA (PatVarA  v : pats) term) = case clauseAToClause (ClauseA pats term) of
    P.Clause pats' term' -> P.Clause (Cons (PatVar v) $ liftPatterns pats') $ apps (fmap Free term') [bvar]
  where
    liftPatterns :: Patterns b a -> Patterns (Scoped b) (Scoped a)
    liftPatterns P.Nil = P.Nil
    liftPatterns (Cons p ps) = Cons (liftPattern p) (liftPatterns ps)
    
    liftPattern :: Pattern b a -> Pattern (Scoped b) (Scoped a)
    liftPattern (PatDCon i n cs ps) = PatDCon i n
        (map (\(P.Clause pats' term') -> P.Clause (liftPatterns pats') $ apps (fmap Free term') [bvar]) cs)
        (liftPatterns ps)
    liftPattern (PatPCon p) = PatPCon (liftPattern p)
    liftPattern (PatICon c) = PatICon c
    liftPattern (PatVar  v) = PatVar v

data CtxClause s f a b where
    CtxClause :: Ctx s f a c -> (b -> c) -> CtxClause s f a b

instantiateClauseA :: Ctx s f Void b -> ClauseA b -> [Term Semantics a] -> ClauseA a
instantiateClauseA ctx c ts = case liftClause ctx of
    CtxClause ctx' f -> go ctx' (fmap f c) (reverse ts)
  where
    liftClause :: Ctx s f Void b -> CtxClause s f a b
    liftClause C.Nil = CtxClause C.Nil absurd
    liftClause (Snoc ctx _ _) = case liftClause ctx of
        CtxClause ctx' f -> CtxClause (Snoc ctx' (error "") $ error "") (fmap f)
    
    go :: Ctx s f a c -> ClauseA c -> [Term Semantics a] -> ClauseA a
    go C.Nil c _ = c
    go (Snoc ctx _ _) c (a:as) = go ctx (instantiateClauseA1 (fmap (liftBase ctx) a) c) as
    go _ _ _ = error "instantiateClauseA"
    
    instantiateClauseA1 :: Term Semantics a -> ClauseA (Scoped a) -> ClauseA a
    instantiateClauseA1 a (ClauseA ps term) = ClauseA (map (instantiatePatternA1 a) ps) (instantiate1 a term)
    
    instantiatePatternA1 :: Term Semantics a -> PatternA (Scoped a) -> PatternA a
    instantiatePatternA1 a (PatDConA i n cs ps) = PatDConA i n (map (instantiateClauseA1 a) cs) $ map (instantiatePatternA1 a) ps
    instantiatePatternA1 a (PatPConA p) = PatPConA (instantiatePatternA1 a p)
    instantiatePatternA1 _ (PatIConA c) = PatIConA c
    instantiatePatternA1 _ (PatVarA  v) = PatVarA v
