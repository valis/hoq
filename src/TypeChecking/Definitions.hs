{-# LANGUAGE RecursiveDo, GADTs #-}

module TypeChecking.Definitions
    ( typeCheckDefs
    ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.Error
import Data.Maybe
import Data.List

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.Context
import Syntax.ErrorDoc
import TypeChecking.Expressions
import TypeChecking.Patterns
import TypeChecking.Coverage
import TypeChecking.Monad
import Normalization

type Tele = [([Arg], Expr)]
data PDef = PDefSyn Arg Expr
          | PDefCases Arg Expr [((Int, Int), [ParPat], Maybe Expr)]
          | PDefData Arg Tele [(Arg,Tele)] [(E.Pattern, Expr)]

theSameAs :: String -> Def -> Bool
theSameAs name (DefFun (FunCase (E.Pattern (PIdent (_,name')) _) _)) = name == name'
theSameAs name (DefFunEmpty (E.Pattern (PIdent (_,name')) _)) = name == name'
theSameAs _ _ = False

splitDefs :: Monad m => [Def] -> EDocM m [PDef]
splitDefs [] = return []
splitDefs (DefType p@(PIdent (lc,name)) ty : defs) =
    case span (theSameAs name) defs of
        ([],_) -> do
            warn [emsgLC lc ("Missing a realization of function " ++ show name) enull]
            splitDefs defs
        (defs1,defs2) -> do
            pdefs <- splitDefs defs2
            let defToPDef (DefFun (FunCase (E.Pattern (PIdent (lc,_)) pats) expr)) = (lc, pats, Just expr)
                defToPDef (DefFunEmpty (E.Pattern (PIdent (lc,_)) pats))           = (lc, pats, Nothing)
                defToPDef _                                                        = error "defToPDef"
            return $ PDefCases (Arg p) ty (map defToPDef defs1) : pdefs
splitDefs (DefFun (FunCase (E.Pattern p []) expr) : defs) = liftM (PDefSyn (Arg p) expr :) (splitDefs defs)
splitDefs (DefFun (FunCase (E.Pattern (PIdent (lc,name)) _) _) : defs) = do
    warn [inferErrorMsg lc "the argument"]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefFunEmpty (E.Pattern (PIdent (lc,name)) []) : defs) = do
    warn [emsgLC lc "Expected right hand side" enull]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefFunEmpty (E.Pattern (PIdent (lc,name)) _) : defs) = do
    warn [inferErrorMsg lc "the argument"]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefDataEmpty p teles : defs) = splitDefs (DefDataWith p teles [] [] : defs)
splitDefs (DefData p teles cons : defs) = splitDefs (DefDataWith p teles cons [] : defs)
splitDefs (DefDataWith p teles cons conds : defs) = do
    dataTeles <- forM teles $ \(DataTele _ e1 e2) -> liftM (\vs -> (vs, e2)) (exprToVars e1)
    conTeles  <- forM cons $ \(E.Con p teles) -> do
        teles' <- forM teles $ \tele ->
            case tele of
                VarTele _ e1 e2 -> liftM (\vs -> (vs, e2)) (exprToVars e1)
                TypeTele e2     -> return ([], e2)
        return (Arg p, teles')
    pdefs <- splitDefs defs
    return (PDefData (Arg p) dataTeles conTeles (map (\(FunCase pat expr) -> (pat, expr)) conds) : pdefs)

typeCheckDefs :: MonadFix m => [Def] -> TCM m ()
typeCheckDefs defs = splitDefs defs >>= mapM_ (\t -> typeCheckPDef t `catchError` warn)

typeCheckPDef :: MonadFix m => PDef -> TCM m ()
typeCheckPDef (PDefSyn arg expr) = do
    (term, ty) <- typeCheck expr Nothing
    addFunctionCheck arg (FunSyn (unArg arg) term) ty
typeCheckPDef (PDefCases arg ety cases) = mdo
    (ty, u) <- typeCheck ety Nothing
    case u of
        T.Universe _ -> return ()
        _            -> throwError [emsgLC (getPos ety) "" $ pretty "Expected a type" $$
                                                             pretty "Actual type:" <+> prettyOpen Nil ty]
    addFunctionCheck arg (FunCall (unArg arg) names) ty
    namesAndPats <- forW cases $ \(lc,pats,mexpr) ->  do
        (bf, TermsInCtx ctx _ ty', rtpats, cpats) <- typeCheckPatterns Nil (nf WHNF ty) pats
        case (bf,mexpr) of
            (True,  Nothing) -> return Nothing
            (False, Nothing) -> do
                let msg = "The right hand side can be omitted only if the absurd pattern is given"
                warn [emsgLC (argGetPos arg) msg enull]
                return Nothing
            (True, Just expr) -> do
                let msg = "If the absurd pattern is given the right hand side must be omitted"
                warn [emsgLC (getPos expr) msg enull]
                return Nothing
            (False, Just expr) -> do
                (term, _) <- typeCheckCtx ctx expr $ Just (nf WHNF ty')
                return $ Just (ClosedName rtpats $ fromJust $ closed $ toScope $
                    reverseTerm (length $ contextNames ctx) (abstractTermInCtx ctx term), (lc, cpats))
    let names = map fst namesAndPats
    case checkCoverage (map snd namesAndPats) of
        Nothing -> warn [emsgLC (argGetPos arg) "Incomplete pattern matching" enull]
        Just uc -> warn $ map (\lc -> emsgLC lc "Unreachable clause" enull) uc
typeCheckPDef (PDefData arg params cons conds) = mdo
    (CtxFrom ctx, dataType, _) <- checkTele Nil params (T.Universe NoLevel)
    addDataTypeCheck arg dataType lcons
    cons' <- forW (zip cons [0..]) $ \((con,tele),i) -> do
        (_, conType, conLevel) <- checkTele ctx tele $ DataType name lcons []
        checkPositivity (nf WHNF conType)
        let conTerm = T.Con i (unArg con) [] $ map snd $ filter (\(c,_) -> c == unArg con) conds'
        return $ Just (con, conTerm, conType, conLevel)
    forM_ cons' $ \(con, te, ty, _) -> addConstructorCheck con name lcons $ case TermsInCtx ctx [te] ty of
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
    lift $ deleteDataType name
    let lvls = map (\(_,_,_,lvl) -> lvl) cons'
    lift $ addDataType name (replaceLevel dataType $ if null lvls then NoLevel else maximum lvls) lcons
  where
    lcons = length cons
    name = unArg arg
    
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
    
    checkPositivity :: (Eq a, Show a) => Monad m => Term a -> EDocM m ()
    checkPositivity (T.Arr a b)                   = checkNoNegative (nf WHNF a) >> checkPositivity (nf WHNF b)
    checkPositivity (T.Pi _ a (Name _ (Scope b))) = checkNoNegative (nf WHNF a) >> checkPositivity (nf WHNF b)
    checkPositivity _                             = return ()
    
    checkNoNegative :: (Eq a, Show a) => Monad m => Term a -> EDocM m ()
    checkNoNegative (T.Arr a b)                   = checkNoDataType a >> checkNoNegative (nf WHNF b)
    checkNoNegative (T.Pi _ a (Name _ (Scope b))) = checkNoDataType a >> checkNoNegative (nf WHNF b)
    checkNoNegative _                             = return ()
    
    checkNoDataType :: Monad m => Term a -> EDocM m ()
    checkNoDataType t = when (name `elem` collectDataTypes t) $ throwError
        [emsgLC (argGetPos arg) "Data type is not strictly positive" enull]
