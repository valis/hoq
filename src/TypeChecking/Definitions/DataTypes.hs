{-# LANGUAGE RecursiveDo #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Definitions.Patterns
import Normalization

type Tele = [([Arg], Expr)]

typeCheckDataType :: MonadFix m => PIdent -> Tele -> [(PIdent,Tele)] -> [(E.Pattern, Expr)] -> TCM m ()
typeCheckDataType p@(PIdent (lc,dt)) params cons conds = mdo
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- checkTele Nil params $ Closed (T.Universe NoLevel)
    addDataTypeCheck p dataType lcons
    cons' <- forW (zip cons [0..]) $ \((con@(PIdent (_,conName)),tele),i) -> do
        (_, Type conType conLevel) <- checkTele ctx tele $ Closed $ DataType dt lcons []
        checkPositivity p (nf WHNF conType)
        let conTerm = T.Con i conName (map snd $ filter (\(c,_) -> c == conName) conds') []
        return $ Just (con, conTerm, Type conType conLevel)
    forM_ cons' $ \(con, te, Type ty lvl) ->
        addConstructorCheck con dt lcons (abstractTermInCtx ctx te) (abstractTermInCtx ctx ty) lvl
    conds' <- forW conds $ \(E.Pattern (E.PIdent (lc,con)) pats,expr) ->
        case find (\(PIdent (_,c),_,_) -> c == con) cons' of
            Nothing -> do
                warn [notInScope lc "data constructor" con]
                return Nothing
            Just (_, _, Type ty lvl) -> do
                (bf, TermsInCtx ctx' _ ty', rtpats, _) <- typeCheckPatterns ctx (Type (nf WHNF ty) lvl) pats
                when bf $ warn [emsgLC lc "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx +++ ctx') expr (Just ty')
                return $ Just (con, (rtpats, closed $ mapScope (const ()) $ abstractTermInCtx ctx' term))
    lift $ deleteDataType dt
    let lvls = map (\(_, _, Type _ lvl) -> lvl) cons'
        lvl = if null lvls then NoLevel else maximum lvls
    lift $ addDataType dt (Type (replaceLevel dtTerm lvl) lvl) lcons

checkTele :: (Monad m, Eq a) => Ctx String Type String a -> Tele -> Closed Term
    -> TCM m (SomeEq (Ctx String Type String), Type a)
checkTele ctx [] (Closed term) = return (SomeEq ctx, Type term NoLevel)
checkTele ctx ((args,expr):tele) term = do
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    lvl1 <- checkIsType ctx expr (nf WHNF t1)
    case extendCtx (map unArg args) Nil (Type r1 lvl1) of
        SomeEq ctx' -> do
            (rctx, Type r2 lvl2) <- checkTele (ctx +++ ctx') tele term
            return (rctx, Type (T.Pi r1 $ abstractTermInCtx ctx' r2) $ max lvl1 lvl2)

replaceLevel :: Term a -> Level -> Term a
replaceLevel (T.Pi r1 r2) lvl = T.Pi r1 (replaceLevelScope r2)
  where
    replaceLevelScope :: Scope String Term a -> Scope String Term a
    replaceLevelScope (ScopeTerm t) = ScopeTerm (replaceLevel t lvl)
    replaceLevelScope (Scope v t) = Scope v (replaceLevelScope t)
replaceLevel _ lvl = T.Universe lvl

checkPositivity :: (Eq a, Monad m) => PIdent -> Term a -> EDocM m ()
checkPositivity dt (T.Pi a b) = checkNoNegative dt (nf WHNF a) >> checkPositivityScope b
  where
    checkPositivityScope :: (Eq a, Monad m) => Scope String Term a -> EDocM m ()
    checkPositivityScope (ScopeTerm t) = checkPositivity dt (nf WHNF t)
    checkPositivityScope (Scope v t) = checkPositivityScope t
checkPositivity _ _ = return ()

checkNoNegative :: (Eq a, Monad m) => PIdent -> Term a -> EDocM m ()
checkNoNegative dt (T.Pi a b) = checkNoDataType dt a >> checkNoNegativeScope b
  where
    checkNoNegativeScope :: (Eq a, Monad m) => Scope String Term a -> EDocM m ()
    checkNoNegativeScope (ScopeTerm t) = checkNoNegative dt (nf WHNF t)
    checkNoNegativeScope (Scope v t) = checkNoNegativeScope t
checkNoNegative _ _ = return ()

checkNoDataType :: Monad m => PIdent -> Term a -> EDocM m ()
checkNoDataType (PIdent (lc,dt)) t = when (dt `elem` collectDataTypes t) $
    throwError [emsgLC lc "Data type is not strictly positive" enull]
