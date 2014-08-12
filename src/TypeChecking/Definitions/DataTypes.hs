{-# LANGUAGE RecursiveDo, ExistentialQuantification #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Bifunctor
import Data.Bifoldable
import Data.Void

import Syntax as S
import Semantics
import Semantics.Value as V
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Patterns
import TypeChecking.Expressions.Conditions
import TypeChecking.Definitions.Termination
import Normalization

typeCheckDataType :: MonadFix m => PName -> [Tele] -> [S.Con] -> [Clause] -> TCM m ()
typeCheckDataType p@(pos, dt) params cons conds = mdo
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- checkTele Nil params $ universe (Set NoLevel)
    dtid <- addDataTypeCheck p lcons $ Closed (vacuous dataType)
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(PIdent pos conName) tele, i) -> do
        (_, Type conType conSort) <- checkTele ctx tele $ Apply (Semantics (Name Prefix dt) $ DataType dtid lcons) (ctxToVars ctx)
        case findOccurrence dtid (nf WHNF conType) of
            Just n | n > 1 -> throwError [emsgLC pos "Data type is not strictly positive" enull]
            _ -> return ()
        let conds'' = map snd $ filter (\(c,_) -> c == conName) conds'
            conTerm = Semantics (Name Prefix $ Ident conName) $ Con $ DCon i lcons (PatEval conds'')
        return $ Just (con, (i, conds'', conTerm), Type conType conSort)
    let ks = map (\(_, _, Type _ k) -> k) cons'
        mk = if null ks then Prop else dmaximum ks
    forM_ cons' $ \(PIdent pcon con, (i, cs, _), Type ty k) ->
        addConstructorCheck (pcon, Ident con) dtid i lcons (PatEval cs) $ Closed $ Type (vacuous $ abstractTerm ctx ty) mk
    conds' <- forW conds $ \(Clause (pos, con) pats expr) ->
        case find (\((PIdent _ c), _, _) -> Ident c == con) cons' of
            Just (PIdent _ conName, (i, _, _), ty) -> do
                (bf, TermsInCtx ctx' _ ty', rtpats) <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx +++ ctx') expr $ Just (nfType WHNF ty')
                let scope = closed (abstractTerm ctx' term)
                throwErrors $ checkTermination (Left i) pos (map (first snd) rtpats) scope
                return $ Just (conName, (rtpats, scope))
            _ -> do
                warn [notInScope pos "data constructor" (getStr con)]
                return Nothing
    lift $ replaceDataType dt lcons $ Closed $ Type (vacuous $ replaceSort dtTerm mk) mk
    forM_ cons' $ \(PIdent pos _, (_, conds, con), _) -> warn $ checkConditions pos (Closed $ capply con) conds

data SomeEq f = forall a. Eq a => SomeEq (f a)

extendCtx :: (Functor t, Eq a) => [s] -> Ctx s t b a -> t a -> SomeEq (Ctx s t b)
extendCtx [] ctx _ = SomeEq ctx
extendCtx (x:xs) ctx t = extendCtx xs (Snoc ctx x t) (fmap Free t)

checkTele :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> [Tele] -> Term Semantics a
    -> TCM m (SomeEq (Ctx String (Type Semantics) Void), Type Semantics a)
checkTele ctx [] term = return (SomeEq ctx, Type term $ Set NoLevel)
checkTele ctx (VarsTele vars expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    k1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    case extendCtx (map getName vars) Nil (Type r1 k1) of
        SomeEq ctx' -> do
            (rctx, Type r2 k2) <- checkTele (ctx +++ ctx') tele $ fmap (liftBase ctx') term
            let sem = Semantics (S.Pi $ reverse $ ctxVars ctx') (V.Pi k1 k2)
            return (rctx, Type (Apply sem [r1, abstractTerm ctx' r2]) $ dmax k1 k2)
checkTele ctx (TypeTele expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    k1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    (rctx, Type r2 k2) <- checkTele ctx tele term
    return (rctx, Type (Apply (Semantics (S.Pi []) $ V.Pi k1 k2) [r1,r2]) $ dmax k1 k2)

replaceSort :: Term Semantics a -> Sort -> Term Semantics a
replaceSort (Apply p@(Semantics _ V.Pi{}) [a,b]) k = Apply p [a, replaceSort b k]
replaceSort (Lambda t) k = Lambda (replaceSort t k)
replaceSort _ k = universe k

findOccurrence :: Eq a => ID -> Term Semantics a -> Maybe Int
findOccurrence dt (Apply (Semantics _ V.Pi{}) [a,b]) = case (findOccurrence dt $ nf WHNF a, findOccurrence dt $ nf WHNF b) of
        (Nothing, Nothing) -> Nothing
        (Nothing, Just b') -> Just b'
        (Just a', Nothing) -> Just (succ a')
        (Just a', Just b') -> Just $ max (succ a') b'
findOccurrence dt (Lambda t) = findOccurrence dt (nf WHNF t)
findOccurrence dt t = if dt `elem` collectDataTypes t then Just 0 else Nothing

collectDataTypes :: Term Semantics a -> [ID]
collectDataTypes = biconcatMap (\t -> case t of
    Semantics _ (DataType dt _) -> [dt]
    _                           -> []) (const [])
