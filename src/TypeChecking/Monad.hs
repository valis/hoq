module TypeChecking.Monad
    ( EDocM, ScopeM, TCM, runTCM
    , addFunctionCheck, addDataTypeCheck, addConstructorCheck
    , module TypeChecking.Monad.Warn
    , module TypeChecking.Monad.Scope
    , lift
    ) where

import Control.Monad
import Control.Monad.Trans(lift)

import TypeChecking.Monad.Warn
import TypeChecking.Monad.Scope
import Syntax.Term
import Syntax.Expr
import Syntax.ErrorDoc

type EDocM = WarnT [EMsg Term]
type ScopeM = ScopeT (Term String) (Type String) (Scope String Term String) (Scope String Term String, Level)
type TCM m = EDocM (ScopeM m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runScopeT . runWarnT

multipleDeclaration :: (Int,Int) -> String -> EMsg f
multipleDeclaration lc var = emsgLC lc ("Multiple declarations of " ++ show var) enull

addFunctionCheck :: Monad m => PIdent -> Term String -> Type String -> TCM m ()
addFunctionCheck (PIdent (lc,var)) te ty = do
    mr <- lift (getEntry var Nothing)
    case mr of
        [] -> lift (addFunction var te ty)
        _  -> warn [multipleDeclaration lc var]

addDataTypeCheck :: Monad m => PIdent -> Type String -> Int -> TCM m ()
addDataTypeCheck (PIdent (lc,var)) ty b = do
    mr <- lift (getEntry var Nothing)
    case mr of
        FunctionE _ _ : _ -> warn [multipleDeclaration lc var]
        DataTypeE _ _ : _ -> warn [multipleDeclaration lc var]
        _                 -> lift (addDataType var ty b)

addConstructorCheck :: Monad m => PIdent -> String -> Int
    -> Scope String Term String -> Scope String Term String -> Level -> TCM m ()
addConstructorCheck (PIdent (lc,var)) dt n te ty lvl = do
    mr <- lift $ getEntry var (Just dt)
    case mr of
        FunctionE    _ _   : _ -> warn [multipleDeclaration lc var]
        ConstructorE _ _ _ : _ -> warn [multipleDeclaration lc var]
        _                      -> lift $ addConstructor var dt n te (ty,lvl)
