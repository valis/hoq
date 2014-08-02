{-# LANGUAGE RecursiveDo, ExistentialQuantification, GADTs #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Bifunctor
import Data.Bifoldable
import Data.Void

import Syntax
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
    (SomeEq ctx, dataType@(Type dtTerm _)) <- checkTele Nil params $ cterm (Universe NoLevel)
    addDataTypeCheck p dataType lcons
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(PIdent pos conName) tele, i) -> do
        (_, Type conType conLevel) <- checkTele ctx tele $ capps (DataType dt lcons) (ctxToVars ctx)
        checkPositivity p (nf WHNF conType)
        let conTerm = Con i con (map snd $ filter (\(c,_) -> c == conName) conds')
        return $ Just (con, conTerm, Type conType conLevel)
    forM_ cons' $ \(con, te, Type ty lvl) ->
        addConstructorCheck con dt lcons (abstractTermInCtx ctx $ cterm te) (abstractTermInCtx ctx ty) lvl
    conds' <- forW conds $ \(Clause (PIdent pos con) pats expr) ->
        case find (\(PIdent _ c, _, _) -> c == con) cons' of
            Nothing -> do
                warn [notInScope pos "data constructor" con]
                return Nothing
            Just (_, _, ty) -> do
                (bf, TermsInCtx ctx' _ ty', rtpats) <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx +++ ctx') expr (Just ty')
                let scope = closed (abstractTermInCtx ctx' term)
                throwErrors (checkTermination con rtpats scope)
                return $ Just (con, (rtpats, scope))
    lift $ deleteDataType dt
    let lvls = map (\(_, _, Type _ lvl) -> lvl) cons'
        lvl = if null lvls then NoLevel else maximum lvls
    lift $ addDataType dt (Type (replaceLevel dtTerm lvl) lvl) lcons
    forM_ cons' $ \(PIdent pos _, con@(Con _ _ conds), _) -> warn $ checkConditions pos (Closed $ cterm con) conds

data SomeEq f = forall a. Eq a => SomeEq (f a)

extendCtx :: (Functor t, Eq a) => [s] -> Ctx s t b a -> t a -> SomeEq (Ctx s t b)
extendCtx [] ctx _ = SomeEq ctx
extendCtx (x:xs) ctx t = extendCtx xs (Snoc ctx x t) (fmap Free t)

checkTele :: (Monad m, Eq a) => Ctx String (Type Syntax) Void a -> [Tele] -> Term Syntax a
    -> TCM m (SomeEq (Ctx String (Type Syntax) Void), Type Syntax a)
checkTele ctx [] term = return (SomeEq ctx, Type term NoLevel)
checkTele ctx (VarsTele vars expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    lvl1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    case extendCtx (map getName vars) Nil (Type r1 lvl1) of
        SomeEq ctx' -> do
            (rctx, Type r2 lvl2) <- checkTele (ctx +++ ctx') tele $ fmap (liftBase ctx') term
            let (vs,r2') = abstractTerm ctx' r2
            return (rctx, Type (Apply (Pi vs lvl1 lvl2) [r1,r2']) $ max lvl1 lvl2)
checkTele ctx (TypeTele expr : tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    lvl1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    (rctx, Type r2 lvl2) <- checkTele ctx tele term
    return (rctx, Type (Apply (Pi [] lvl1 lvl2) [r1,r2]) $ max lvl1 lvl2)

abstractTerm :: Ctx s g b a -> Term p a -> ([s], Term p b)
abstractTerm Nil term = ([], term)
abstractTerm (Snoc ctx v _) term = first (v:) $ abstractTerm ctx $ Lambda (Scope1 term)

replaceLevel :: Term Syntax a -> Level -> Term Syntax a
replaceLevel (Apply p@Pi{} [a,b]) lvl = Apply p [a, replaceLevel b lvl]
replaceLevel (Lambda (Scope1 t)) lvl = Lambda $ Scope1 (replaceLevel t lvl)
replaceLevel _ lvl = cterm (Universe lvl)

checkPositivity :: (Eq a, Monad m) => PIdent -> Term Syntax a -> EDocM m ()
checkPositivity dt (Apply Pi{} [a,b]) = checkNoNegative dt (nf WHNF a) >> checkPositivity dt (nf WHNF b)
checkPositivity dt (Lambda (Scope1 t)) = checkPositivity dt (nf WHNF t)
checkPositivity _ _ = return ()

checkNoNegative :: (Eq a, Monad m) => PIdent -> Term Syntax a -> EDocM m ()
checkNoNegative dt (Apply Pi{} [a,b]) = checkNoDataType dt a >> checkNoNegative dt (nf WHNF b)
checkNoNegative dt (Lambda (Scope1 t)) = checkNoNegative dt (nf WHNF t)
checkNoNegative _ _ = return ()

checkNoDataType :: Monad m => PIdent -> Term Syntax a -> EDocM m ()
checkNoDataType (PIdent pos dt) t = when (dt `elem` collectDataTypes t) $
    throwError [emsgLC pos "Data type is not strictly positive" enull]

collectDataTypes :: Term Syntax a -> [String]
collectDataTypes = biconcatMap (\t -> case t of
    DataType dt _   -> [dt]
    _               -> []) (const [])
