{-# LANGUAGE RecursiveDo, ExistentialQuantification, GADTs #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List

import Syntax.Term
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Definitions.Patterns
import TypeChecking.Definitions.Conditions
import TypeChecking.Definitions.Termination
import Normalization

typeCheckDataType :: MonadFix m => PIdent -> [Tele Posn PIdent] -> [Con] -> [Clause] -> TCM m ()
typeCheckDataType p@(PIdent pos dt) params cons conds = mdo
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- checkTele Nil params (Universe (0,0) NoLevel)
    addDataTypeCheck p dataType lcons
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(PIdent pos conName) tele, i) -> do
        (_, Type conType conLevel) <- checkTele ctx (mapCtxTele ctx tele) $
            DataType pos dt lcons $ ctxToVars (const (0,0)) ctx
        checkPositivity p (nf WHNF conType)
        let conTerm = Con pos i conName (map snd $ filter (\(c,_) -> c == conName) conds') []
        return $ Just (con, conTerm, Type conType conLevel)
    forM_ cons' $ \(con, te, Type ty lvl) ->
        addConstructorCheck con dt lcons (abstractTermInCtx ctx te) (abstractTermInCtx ctx ty) lvl
    conds' <- forW conds $ \(Clause (PIdent pos con) pats expr) ->
        case find (\(PIdent _ c, _, _) -> c == con) cons' of
            Nothing -> do
                warn [notInScope pos "data constructor" con]
                return Nothing
            Just (_, _, ty) -> do
                (bf, TermsInCtx ctx' _ ty', rtpats) <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx +++ ctx') (fmap (liftBase $ ctx +++ ctx') expr) (Just ty')
                let scope = closed (abstractTermInCtx ctx' term)
                throwErrors (checkTermination con rtpats scope)
                return $ Just (con, (rtpats, scope))
    lift $ deleteDataType dt
    let lvls = map (\(_, _, Type _ lvl) -> lvl) cons'
        lvl = if null lvls then NoLevel else maximum lvls
    lift $ addDataType dt (Type (replaceLevel dtTerm lvl) lvl) lcons
    forM_ cons' $ \(_, Con pos' i conName conConds [], _) -> do
        warn $ checkConditions pos (Closed $ Con pos' i conName conConds []) conConds

data SomeEq f = forall a. Eq a => SomeEq (f a)

extendCtx :: (Functor t, Eq a) => [s] -> Ctx s p t b a -> t a -> SomeEq (Ctx s p t b)
extendCtx [] ctx _ = SomeEq ctx
extendCtx (x:xs) ctx t = extendCtx xs (Snoc ctx x t) (fmap Free t)

checkTele :: (Monad m, Eq a) => Ctx String Posn (Type Posn) PIdent a -> [Tele Posn a] -> Term Posn a
    -> TCM m (SomeEq (Ctx String Posn (Type Posn) PIdent), Type Posn a)
checkTele ctx [] term = return (SomeEq ctx, Type term NoLevel)
checkTele ctx (VarsTele vars expr : tele) term = do
    let pos = getAttr (toBase ctx getPos) expr
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    lvl1 <- checkIsType ctx pos (nf WHNF t1)
    case extendCtx (map getName vars) Nil (Type r1 lvl1) of
        SomeEq ctx' -> do
            (rctx, Type r2 lvl2) <- checkTele (ctx +++ ctx') (mapCtxTele ctx' tele) $ fmap (liftBase ctx') term
            return (rctx, Type (Pi pos (Type r1 lvl1) (abstractTermInCtx ctx' r2) lvl2) $ max lvl1 lvl2)
checkTele ctx (TypeTele expr : tele) term = do
    let pos = getAttr (toBase ctx getPos) expr
    (r1, Type t1 _) <- typeCheckCtx ctx expr Nothing
    lvl1 <- checkIsType ctx pos (nf WHNF t1)
    (rctx, Type r2 lvl2) <- checkTele ctx tele term
    return (rctx, Type (Pi pos (Type r1 lvl1) (ScopeTerm r2) lvl2) $ max lvl1 lvl2)

mapCtxTele :: Eq a => Ctx String Posn f b a -> [Tele Posn b] -> [Tele Posn a]
mapCtxTele ctx = map $ \tele -> case tele of
    VarsTele vars expr -> VarsTele vars (fmap (liftBase ctx) expr)
    TypeTele      expr -> TypeTele      (fmap (liftBase ctx) expr)

replaceLevel :: Term Posn a -> Level -> Term Posn a
replaceLevel (Pi p r1 r2 lvl2) lvl = Pi p r1 (replaceLevelScope r2) lvl2
  where
    replaceLevelScope :: Scope String Posn (Term Posn) a -> Scope String Posn (Term Posn) a
    replaceLevelScope (ScopeTerm t) = ScopeTerm (replaceLevel t lvl)
    replaceLevelScope (Scope v t) = Scope v (replaceLevelScope t)
replaceLevel (Universe p _) lvl = Universe p lvl
replaceLevel _ lvl = Universe (0,0) lvl

checkPositivity :: (Eq a, Monad m) => PIdent -> Term Posn a -> EDocM m ()
checkPositivity dt (Pi _ (Type a _) b _) = checkNoNegative dt (nf WHNF a) >> checkPositivityScope b
  where
    checkPositivityScope :: (Eq a, Monad m) => Scope String Posn (Term Posn) a -> EDocM m ()
    checkPositivityScope (ScopeTerm t) = checkPositivity dt (nf WHNF t)
    checkPositivityScope (Scope v t) = checkPositivityScope t
checkPositivity _ _ = return ()

checkNoNegative :: (Eq a, Monad m) => PIdent -> Term Posn a -> EDocM m ()
checkNoNegative dt (Pi _ (Type a _) b _) = checkNoDataType dt a >> checkNoNegativeScope b
  where
    checkNoNegativeScope :: (Eq a, Monad m) => Scope String Posn (Term Posn) a -> EDocM m ()
    checkNoNegativeScope (ScopeTerm t) = checkNoNegative dt (nf WHNF t)
    checkNoNegativeScope (Scope v t) = checkNoNegativeScope t
checkNoNegative _ _ = return ()

checkNoDataType :: Monad m => PIdent -> Term Posn a -> EDocM m ()
checkNoDataType (PIdent pos dt) t = when (dt `elem` collectDataTypes t) $
    throwError [emsgLC pos "Data type is not strictly positive" enull]

collectDataTypes :: Term Posn a        -> [String]
collectDataTypes Var{}                  = []
collectDataTypes (App e1 e2)            = collectDataTypes e1 ++ collectDataTypes e2
collectDataTypes (Lam _ (Scope1 _ e))   = collectDataTypes e
collectDataTypes (Pi _ (Type e _) s _)  = collectDataTypes e ++ go s
  where
    go :: Scope s Posn (Term Posn) a -> [String]
    go (ScopeTerm t) = collectDataTypes t
    go (Scope _   s) = go s
collectDataTypes (Con _ _ _ _ as)       = as >>= collectDataTypes
collectDataTypes FunCall{}              = []
collectDataTypes FunSyn{}               = []
collectDataTypes (DataType _ d _ as)    = d : (as >>= collectDataTypes)
collectDataTypes Universe{}             = []
collectDataTypes Interval{}             = []
collectDataTypes ICon{}                 = []
collectDataTypes (Path _ _ me1 es)      = maybe [] collectDataTypes me1 ++ (es >>= collectDataTypes)
collectDataTypes (PCon _ me)            = maybe [] collectDataTypes me
collectDataTypes (At _ e3 e4)           = collectDataTypes e3 ++ collectDataTypes e4
collectDataTypes (Coe _ es)             = es >>= collectDataTypes
collectDataTypes (Iso _ es)             = es >>= collectDataTypes
collectDataTypes (Squeeze _ es)         = es >>= collectDataTypes
