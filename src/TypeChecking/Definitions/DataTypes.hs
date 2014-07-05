{-# LANGUAGE RecursiveDo, GADTs #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Maybe

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.Context
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Expressions
import TypeChecking.Definitions.Patterns
import Normalization

type Tele = [([Arg], Expr)]

typeCheckDataType :: MonadFix m => Arg -> Tele -> [(Arg,Tele)] -> [(E.Pattern, Expr)] -> TCM m ()
typeCheckDataType arg params cons conds = mdo
    let lcons = length cons
        dt  = unArg arg
    (CtxFrom ctx, dataType, _) <- checkTele Nil params (T.Universe NoLevel)
    addDataTypeCheck arg dataType lcons
    cons' <- forW (zip cons [0..]) $ \((con,tele),i) -> do
        (_, conType, conLevel) <- checkTele ctx tele $ DataType dt lcons []
        checkPositivity arg (nf WHNF conType)
        let conTerm = T.Con i (unArg con) [] $ map snd $ filter (\(c,_) -> c == unArg con) conds'
        return $ Just (con, conTerm, conType, conLevel)
    forM_ cons' $ \(con, te, ty, _) -> addConstructorCheck con dt lcons $ case TermsInCtx ctx [te] ty of
        TermsInCtx Nil  [con'] conType' -> Left  (con', conType')
        TermsInCtx ctx' [con'] conType' -> Right (abstractTermInCtx ctx' con', abstractTermInCtx ctx' conType')
        _                               -> error "typeCheckPDef"
    conds' <- forW conds $ \(E.Pattern (E.PIdent (lc,con)) pats,expr) -> case find (\(c,_,_,_) -> unArg c == con) cons' of
        Nothing -> do
            warn [notInScope lc "data constructor" con]
            return Nothing
        Just (_,_,ty,_) -> do
            (bf, TermsInCtx ctx' _ ty', rtpats, _) <- typeCheckPatterns ctx (nf WHNF ty) pats
            when bf $ warn [emsgLC lc "Absurd patterns are not allowed in conditions" enull]
            (term, _) <- typeCheckCtx (ctx +++ ctx') expr $ Just (nf WHNF ty')
            let term' = toScope $ reverseTerm (length $ contextNames ctx') $ abstractTermInCtx ctx' term
            return $ Just (con, ClosedName rtpats $ fromJust $ closed term')
    lift $ deleteDataType dt
    let lvls = map (\(_,_,_,lvl) -> lvl) cons'
    lift $ addDataType dt (replaceLevel dataType $ if null lvls then NoLevel else maximum lvls) lcons

checkTele :: (Monad m, Eq a, Show a) => Ctx Int [String] Term String a -> Tele -> Term a ->
    TCM m (CtxFrom Int [String] Term String, Term a, Level)
checkTele ctx [] term = return (CtxFrom ctx, term, NoLevel)
checkTele ctx (([],expr):tele) term = do
    (r1,t1) <- typeCheckCtx ctx expr Nothing
    (rctx,r2,t2) <- checkTele ctx tele term
    T.Universe t <- checkUniverses ctx ctx expr expr t1 (T.Universe t2)
    return (rctx, T.Arr r1 r2, t)
checkTele ctx ((args,expr):tele) term = do
    (r1,t1) <- typeCheckCtx ctx expr Nothing
    let vars = map unArg args
        ctx' = Snoc ctx (reverse vars) r1
    (rctx,r2,t2) <- checkTele ctx' tele (fmap F term)
    T.Universe t <- checkUniverses ctx ctx' expr expr t1 (T.Universe t2)
    return (rctx, T.Pi (null tele) r1 $ Name vars $ toScope r2, t)

replaceLevel :: Term a -> Level -> Term a
replaceLevel (T.Pi fl r1 (Name vars (Scope r2))) lvl = T.Pi fl r1 $ Name vars $ Scope (replaceLevel r2 lvl)
replaceLevel _ lvl = T.Universe lvl

checkPositivity :: (Eq a, Show a) => Monad m => Arg -> Term a -> EDocM m ()
checkPositivity dt (T.Arr a b)                   = checkNoNegative dt (nf WHNF a) >> checkPositivity dt (nf WHNF b)
checkPositivity dt (T.Pi _ a (Name _ (Scope b))) = checkNoNegative dt (nf WHNF a) >> checkPositivity dt (nf WHNF b)
checkPositivity _ _                              = return ()

checkNoNegative :: (Eq a, Show a) => Monad m => Arg -> Term a -> EDocM m ()
checkNoNegative dt (T.Arr a b)                   = checkNoDataType dt a >> checkNoNegative dt (nf WHNF b)
checkNoNegative dt (T.Pi _ a (Name _ (Scope b))) = checkNoDataType dt a >> checkNoNegative dt (nf WHNF b)
checkNoNegative _ _                              = return ()

checkNoDataType :: Monad m => Arg -> Term a -> EDocM m ()
checkNoDataType dt t = when (unArg dt `elem` collectDataTypes t) $
    throwError [emsgLC (argGetPos dt) "Data type is not strictly positive" enull]
