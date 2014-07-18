module TypeChecking.Definitions
    ( typeCheckDefs
    ) where

import Control.Monad

import Syntax.Term
import Syntax.ErrorDoc
import TypeChecking.Expressions
import TypeChecking.Definitions.DataTypes
import TypeChecking.Definitions.Functions
import TypeChecking.Monad

type Tele = [([Arg], Expr)]

typeCheckDefs :: MonadFix m => [Def] -> TCM m ()
typeCheckDefs [] = return ()
typeCheckDefs (DefType p@(PIdent (lc,name)) ty : defs) =
    case span (theSameAs name) defs of
        ([],_) -> do
            warn [emsgLC lc ("Missing a realization of function " ++ show name) enull]
            typeCheckDefs defs
        (defs1,defs2) -> do
            typeCheckFunction p ty (map defToPDef defs1)
            typeCheckDefs defs2
  where
    defToPDef :: Def -> ((Int, Int), [E.Pattern], Maybe Expr)
    defToPDef (DefFun (FunCase (PatName (PIdent (lc,_)) pats) expr)) = (lc, pats, Just expr)
    defToPDef (DefFunEmpty (PatName (PIdent (lc,_)) pats))           = (lc, pats, Nothing)
    defToPDef _                                                      = error "defToPDef"
typeCheckDefs (DefFun (FunCase (PatName p@(PIdent (_,name)) []) expr) : defs) = do
    (term, ty) <- typeCheck expr Nothing
    addFunctionCheck p (FunSyn name term) ty
    typeCheckDefs defs
typeCheckDefs (DefFun (FunCase (PatName (PIdent (lc,name)) _) _) : defs) = do
    warn [inferErrorMsg lc "the argument"]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefFunEmpty (PatName (PIdent (lc,name)) []) : defs) = do
    warn [emsgLC lc "Expected right hand side" enull]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefFunEmpty (PatName (PIdent (lc,name)) _) : defs) = do
    warn [inferErrorMsg lc "the argument"]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefDataEmpty p teles : defs) = typeCheckDefs (DefDataWith p teles [] [] : defs)
typeCheckDefs (DefData p teles cons : defs) = typeCheckDefs (DefDataWith p teles cons [] : defs)
typeCheckDefs (DefDataWith p teles cons conds : defs) = do
    dataTeles <- forM teles $ \(DataTele _ e1 e2) -> liftM (\vs -> (vs, e2)) (exprToVars e1)
    conTeles  <- forM cons $ \(E.Con p teles) -> do
        teles' <- forM teles $ \tele ->
            case tele of
                VarTele _ e1 e2 -> liftM (\vs -> (vs, e2)) (exprToVars e1)
                TypeTele e2     -> return ([], e2)
        return (p, teles')
    typeCheckDataType p dataTeles conTeles $ map (\(FunCase pat expr) -> (pat, expr)) conds
    typeCheckDefs defs

theSameAs :: String -> Def -> Bool
theSameAs name (DefFun (FunCase (PatName (PIdent (_,name')) _) _)) = name == name'
theSameAs name (DefFunEmpty (PatName (PIdent (_,name')) _)) = name == name'
theSameAs _ _ = False
