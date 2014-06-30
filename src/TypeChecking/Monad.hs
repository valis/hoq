module TypeChecking.Monad
    ( EDocM, TCM, runTCM
    , addFunctionCheck, addDataTypeCheck, addConstructorCheck
    , module TypeChecking.Monad.Warn
    , module TypeChecking.Monad.Scope
    , lift
    ) where

import Bound.Var
import Control.Monad
import Control.Monad.Trans(lift)

import TypeChecking.Monad.Warn
import TypeChecking.Monad.Scope
import Syntax.Term
import Syntax.Expr
import Syntax.ErrorDoc

type EDocM = WarnT [EMsg Term]
type TCM m = EDocM (ScopeT Term m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runScopeT . runWarnT

multipleDeclaration :: Arg -> String -> EMsg f
multipleDeclaration arg var = emsgLC (argGetPos arg) ("Multiple declarations of " ++ show var) enull

addFunctionCheck :: Monad m => Arg -> Term String -> Term String -> TCM m ()
addFunctionCheck arg te ty = do
    let var = unArg arg
    mr <- lift (getEntry var Nothing)
    case mr of
        [] -> lift (addFunction var te ty)
        _  -> throwError [multipleDeclaration arg var]

addDataTypeCheck :: Monad m => Arg -> Term String -> TCM m ()
addDataTypeCheck arg ty = do
    let var = unArg arg
    mr <- lift (getEntry var Nothing)
    case mr of
        FunctionE _ _ : _ -> throwError [multipleDeclaration arg var]
        DataTypeE _   : _ -> throwError [multipleDeclaration arg var]
        _                 -> lift (addDataType var ty)

addConstructorCheck :: Monad m => Arg -> String
    -> Either (Term String, Term String) (Term (Var Int String), Term (Var Int String)) -> TCM m ()
addConstructorCheck arg dt ty = do
    let var = unArg arg
    mr <- lift $ getEntry var (Just dt)
    case mr of
        FunctionE _ _  : _ -> throwError [multipleDeclaration arg var]
        ConstructorE _ : _ -> throwError [multipleDeclaration arg var]
        _                  -> lift (addConstructor var dt ty)
