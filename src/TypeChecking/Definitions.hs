module TypeChecking.Definitions
    ( PDef(..), Tele
    , splitDefs
    , parPatToPattern, toListPat
    ) where

import Control.Monad

import Syntax.Expr as E
import Syntax.Term as T
import TypeChecking.Expressions
import TypeChecking.Monad

exprPatToPattern :: Monad m => E.Pattern -> TCM m RTPattern
exprPatToPattern (E.Pattern (PIdent (lc,name)) pats) = do
    d <- lift (getConstructor name Nothing)
    case d of
        []       -> throwError [notInScope lc "data constructor" name]
        [(i, _)] -> liftM (RTPattern i) (mapM parPatToPattern pats)
        _        -> throwError [inferErrorMsg lc $ "data constructor " ++ show name]

parPatToPattern :: Monad m => ParPat -> TCM m RTPattern
parPatToPattern (ParVar arg) = do
    let var = unArg arg
    d <- lift $ getConstructor var Nothing
    case d of
        []       -> return RTPatternVar
        [(i, _)] -> return $ RTPattern i []
        _        -> throwError [inferErrorMsg (argGetPos arg) $ "data constructor " ++ show var]
parPatToPattern (ParPat _ pat) = exprPatToPattern pat

toListPat :: RTPattern -> E.Pattern -> [String]
toListPat RTPatternVar (E.Pattern (PIdent (_,name)) _) = [name]
toListPat (RTPattern _ pats) (E.Pattern _ pats') = concat (zipWith toListPar pats pats')
  where
    toListPar :: RTPattern -> ParPat -> [String]
    toListPar pat (ParPat _ pat') = toListPat pat pat'
    toListPar RTPatternVar (ParVar arg) = [unArg arg]
    toListPar (RTPattern _ _) (ParVar _) = []

type Tele = [([Arg], Expr)]
data PDef = PDefSyn Arg Expr | PDefCases Arg Expr [([ParPat],Expr)] | PDefData Arg Tele [(Arg,Tele)]

theSameAs :: String -> Def -> Bool
theSameAs name (DefFun (E.Pattern (PIdent (_,name')) _) _) = name == name'
theSameAs _ _ = False

splitDefs :: Monad m => [Def] -> EDocM m [PDef]
splitDefs [] = return []
splitDefs (DefType p@(PIdent (_,name)) ty : defs) =
    let (defs1,defs2) = span (theSameAs name) defs
    in liftM (PDefCases (Arg p) ty (map (\(DefFun (E.Pattern _ pats) expr) -> (pats,expr)) defs1) :) (splitDefs defs2)
splitDefs (DefFun (E.Pattern p []) expr : defs) = liftM (PDefSyn (Arg p) expr :) (splitDefs defs)
splitDefs (DefFun (E.Pattern (PIdent (lc,name)) _) _ : defs) = do
    warn [inferErrorMsg lc "the argument"]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefData p teles cons : defs) = do
    dataTeles <- forM teles $ \(DataTele _ e1 e2) -> liftM (\vs -> (vs, e2)) (exprToVars e1)
    conTeles  <- forM (unCons cons) $ \(E.Con p teles) -> do
        teles' <- forM teles $ \tele ->
            case tele of
                VarTele _ e1 e2 -> liftM (\vs -> (vs, e2)) (exprToVars e1)
                TypeTele e2     -> return ([], e2)
        return (Arg p, teles')
    pdefs <- splitDefs defs
    return (PDefData (Arg p) dataTeles conTeles : pdefs)
