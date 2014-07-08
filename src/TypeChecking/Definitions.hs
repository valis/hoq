module TypeChecking.Definitions
    ( typeCheckDefs
    ) where

import Control.Monad
import Control.Monad.Error

import Syntax.Expr as E
import Syntax.Term as T
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
    defToPDef :: Def -> ((Int, Int), [ParPat], Maybe Expr)
    defToPDef (DefFun (FunCase (E.Pattern (PIdent (lc,_)) pats) expr)) = (lc, pats, Just expr)
    defToPDef (DefFunEmpty (E.Pattern (PIdent (lc,_)) pats))           = (lc, pats, Nothing)
    defToPDef _                                                        = error "defToPDef"
typeCheckDefs (DefFun (FunCase (E.Pattern p@(PIdent (_,name)) []) expr) : defs) = do
    (term, ty) <- typeCheck expr Nothing
    addFunctionCheck p (FunSyn name term) ty
    typeCheckDefs defs
typeCheckDefs (DefFun (FunCase (E.Pattern (PIdent (lc,name)) _) _) : defs) = do
    warn [inferErrorMsg lc "the argument"]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefFunEmpty (E.Pattern (PIdent (lc,name)) []) : defs) = do
    warn [emsgLC lc "Expected right hand side" enull]
    typeCheckDefs $ dropWhile (theSameAs name) defs
typeCheckDefs (DefFunEmpty (E.Pattern (PIdent (lc,name)) _) : defs) = do
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
theSameAs name (DefFun (FunCase (E.Pattern (PIdent (_,name')) _) _)) = name == name'
theSameAs name (DefFunEmpty (E.Pattern (PIdent (_,name')) _)) = name == name'
theSameAs _ _ = False
