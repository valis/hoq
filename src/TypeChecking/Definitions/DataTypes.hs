{-# LANGUAGE RecursiveDo, ExistentialQuantification, GADTs #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Bifoldable
import Data.Void

import Syntax as S
import Semantics
import Semantics.Value as V
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Definitions.Patterns
import TypeChecking.Definitions.Conditions
import TypeChecking.Definitions.Termination
import Normalization

typeCheckDataType :: MonadFix m => PIdent -> [Tele] -> [Con] -> [Clause] -> TCM m ()
typeCheckDataType p@(PIdent pos dt) params cons conds = mdo
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- checkTele Nil params (universe NoLevel)
    dtid <- addDataTypeCheck p lcons dataType
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(PIdent pos conName) tele, i) -> do
        (_, Type conType conLevel) <- checkTele ctx tele $ capps (Semantics (Ident dt) $ DataType dtid lcons) (ctxToVars ctx)
        checkPositivity pos dtid (nf WHNF conType)
        let conds'' = map snd $ filter (\(c,_) -> c == conName) conds'
            conTerm = Semantics (Ident conName) $ Con i (PatEval conds'')
        return $ Just (con, (i, conds'', conTerm), Type conType conLevel)
    forM_ cons' $ \(con, (i, cs, _), Type ty lvl) ->
        addConstructorCheck con dtid i lcons (PatEval cs) $ Type (abstractTerm ctx ty) lvl
    conds' <- forW conds $ \(Clause (PIdent pos con) pats expr) ->
        case find (\(PIdent _ c, _, _) -> c == con) cons' of
            Just (_, (i, _, _), ty) -> do
                (bf, TermsInCtx ctx' _ ty', rtpats) <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx +++ ctx') expr (Just ty')
                let scope = closed (abstractTerm ctx' term)
                throwErrors (checkTermination (Left i) pos rtpats scope)
                return $ Just (con, (rtpats, scope))
            _ -> do
                warn [notInScope pos "data constructor" con]
                return Nothing
    let lvls = map (\(_, _, Type _ lvl) -> lvl) cons'
        lvl = if null lvls then NoLevel else maximum lvls
    lift $ replaceDataType dt lcons $ Type (replaceLevel dtTerm lvl) lvl
    forM_ cons' $ \(PIdent pos _, (_, conds, con), _) -> warn $ checkConditions pos (Closed $ cterm con) conds

data SomeEq f = forall a. Eq a => SomeEq (f a)

extendCtx :: (Functor t, Eq a) => [s] -> Ctx s t b a -> t a -> SomeEq (Ctx s t b)
extendCtx [] ctx _ = SomeEq ctx
extendCtx (x:xs) ctx t = extendCtx xs (Snoc ctx x t) (fmap Free t)

checkTele :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> [Tele] -> Term Semantics a
    -> TCM m (SomeEq (Ctx String (Type Semantics) Void), Type Semantics a)
checkTele ctx [] term = return (SomeEq ctx, Type term NoLevel)
checkTele ctx (VarsTele vars expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    lvl1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    case extendCtx (map getName vars) Nil (Type r1 lvl1) of
        SomeEq ctx' -> do
            (rctx, Type r2 lvl2) <- checkTele (ctx +++ ctx') tele $ fmap (liftBase ctx') term
            return (rctx, Type (Apply (Semantics (S.Pi $ reverse $ ctxVars ctx') $ V.Pi lvl1 lvl2) [r1, abstractTerm ctx' r2]) $ max lvl1 lvl2)
checkTele ctx (TypeTele expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    lvl1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    (rctx, Type r2 lvl2) <- checkTele ctx tele term
    return (rctx, Type (Apply (Semantics (S.Pi []) $ V.Pi lvl1 lvl2) [r1,r2]) $ max lvl1 lvl2)

replaceLevel :: Term Semantics a -> Level -> Term Semantics a
replaceLevel (Apply p@(Semantics _ V.Pi{}) [a,b]) lvl = Apply p [a, replaceLevel b lvl]
replaceLevel (Lambda t) lvl = Lambda (replaceLevel t lvl)
replaceLevel _ lvl = universe lvl

checkPositivity :: (Eq a, Monad m) => Posn -> ID -> Term Semantics a -> EDocM m ()
checkPositivity pos dt (Apply (Semantics _ V.Pi{}) [a,b]) = checkNoNegative pos dt (nf WHNF a) >> checkPositivity pos dt (nf WHNF b)
checkPositivity pos dt (Lambda t) = checkPositivity pos dt (nf WHNF t)
checkPositivity _ _ _ = return ()

checkNoNegative :: (Eq a, Monad m) => Posn -> ID -> Term Semantics a -> EDocM m ()
checkNoNegative pos dt (Apply (Semantics _ V.Pi{}) [a,b]) = checkNoDataType pos dt a >> checkNoNegative pos dt (nf WHNF b)
checkNoNegative pos dt (Lambda t) = checkNoNegative pos dt (nf WHNF t)
checkNoNegative _ _ _ = return ()

checkNoDataType :: Monad m => Posn -> ID -> Term Semantics a -> EDocM m ()
checkNoDataType pos dt t = when (dt `elem` collectDataTypes t) $
    throwError [emsgLC pos "Data type is not strictly positive" enull]

collectDataTypes :: Term Semantics a -> [ID]
collectDataTypes = biconcatMap (\t -> case t of
    Semantics _ (DataType dt _) -> [dt]
    _                           -> []) (const [])
