module TypeChecking.Definitions
    ( PDef(..), Tele
    , splitDefs
    , parPatToPattern
    ) where

import Control.Monad

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import TypeChecking.Expressions
import TypeChecking.Monad

exprPatToPattern :: Monad m => E.Pattern -> TCM m (Maybe RTPattern)
exprPatToPattern (E.Pattern (PIdent (lc,name)) pats) = do
    d <- lift (getConstructor name Nothing)
    case d of
        []       -> throwError [notInScope lc "data constructor" name]
        [(i, _)] -> liftM (fmap (RTPattern i) . sequence) (mapM parPatToPattern pats)
        _        -> throwError [inferErrorMsg lc $ "data constructor " ++ show name]

parPatToPattern :: Monad m => ParPat -> TCM m (Maybe RTPattern)
parPatToPattern (ParEmpty _) = return Nothing
parPatToPattern (ParVar arg) = do
    let var = unArg arg
    d <- lift $ getConstructor var Nothing
    case d of
        []       -> return (Just RTPatternVar)
        [(i, _)] -> return $ Just $ RTPattern i []
        _        -> throwError [inferErrorMsg (argGetPos arg) $ "data constructor " ++ show var]
parPatToPattern (ParPat _ pat) = exprPatToPattern pat

type Tele = [([Arg], Expr)]
data PDef = PDefSyn Arg Expr | PDefCases Arg Expr [([ParPat], Maybe Expr)] | PDefData Arg Tele [(Arg,Tele)]

theSameAs :: String -> Def -> Bool
theSameAs name (DefFun (E.Pattern (PIdent (_,name')) _) _) = name == name'
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
            let defToPDef (DefFun (E.Pattern _ pats) expr) = (pats, Just expr)
                defToPDef (DefFunEmpty (E.Pattern _ pats)) = (pats, Nothing)
                defToPDef _                                = error "defToPDef"
            return $ PDefCases (Arg p) ty (map defToPDef defs1) : pdefs
splitDefs (DefFun (E.Pattern p []) expr : defs) = liftM (PDefSyn (Arg p) expr :) (splitDefs defs)
splitDefs (DefFun (E.Pattern (PIdent (lc,name)) _) _ : defs) = do
    warn [inferErrorMsg lc "the argument"]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefFunEmpty (E.Pattern (PIdent (lc,name)) []) : defs) = do
    warn [emsgLC lc "Expected right hand side" enull]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefFunEmpty (E.Pattern (PIdent (lc,name)) _) : defs) = do
    warn [inferErrorMsg lc "the argument"]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefDataEmpty p teles : defs) = splitDefs (DefData p teles [] : defs)
splitDefs (DefData p teles cons : defs) = do
    dataTeles <- forM teles $ \(DataTele _ e1 e2) -> liftM (\vs -> (vs, e2)) (exprToVars e1)
    conTeles  <- forM cons $ \(E.Con p teles) -> do
        teles' <- forM teles $ \tele ->
            case tele of
                VarTele _ e1 e2 -> liftM (\vs -> (vs, e2)) (exprToVars e1)
                TypeTele e2     -> return ([], e2)
        return (Arg p, teles')
    pdefs <- splitDefs defs
    return (PDefData (Arg p) dataTeles conTeles : pdefs)
