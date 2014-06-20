{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecking.Monad.Scope
    ( ScopeT, runScopeT
    , addFunction, addConstructor, addDataType
    , deleteDataType
    , getConstructor
    , Entry(..), getEntry
    ) where

import Bound.Var
import Control.Monad
import Control.Monad.Fix
import Control.Monad.State
import Control.Applicative
import Data.List
import Data.Maybe

data Entry f = FunctionE (f String) (f String)
             | DataTypeE (f String)
             | ConstructorE Int (Either (f String) (f (Var Int String)))

data ScopeState f = ScopeState
    { functions    :: [(String, (f String, f String))]
    , dataTypes    :: [(String, f String)]
    , constructors :: [((String, String), (Int, Either (f String) (f (Var Int String))))]
    }

newtype ScopeT f m a = ScopeT { unScopeT :: StateT (ScopeState f) m a }
    deriving (Functor,Monad,MonadTrans,MonadIO,MonadFix,Applicative)

addFunction :: (Monad f, Monad m) => String -> f String -> f String -> ScopeT f m ()
addFunction v te ty = ScopeT $ modify $ \scope -> scope { functions = (v, (te, ty)) : functions scope }

addDataType :: (Monad f, Monad m) => String -> f String -> ScopeT f m ()
addDataType v ty = ScopeT $ modify $ \scope -> scope { dataTypes = (v, ty) : dataTypes scope }

addConstructor :: (Monad f, Monad m) => String -> String -> Int -> Either (f String) (f (Var Int String)) -> ScopeT f m ()
addConstructor con dt i ty = ScopeT $ modify $ \scope -> scope { constructors = ((con, dt), (i, ty)) : constructors scope }

deleteDataType :: (Monad f, Monad m) => String -> ScopeT f m ()
deleteDataType dt = ScopeT $ modify $ \scope ->
    scope { dataTypes = deleteBy (\(v1,_) (v2,_) -> v1 == v2) (dt, error "") (dataTypes scope) }

getConstructor :: Monad m => String -> Maybe String -> ScopeT f m [(Int, Either (f String) (f (Var Int String)))]
getConstructor con (Just dt) = ScopeT $ liftM (maybeToList . lookup (con, dt) . constructors) get
getConstructor con Nothing   = ScopeT $ liftM (map snd . filter (\((c,_),_) -> con == c) . constructors) get

getEntry :: Monad m => String -> Maybe String -> ScopeT f m [Entry f]
getEntry v dt = ScopeT $ do
    cons  <- unScopeT (getConstructor v dt)
    scope <- get
    return $ map (uncurry FunctionE)    (maybeToList $ lookup v $ functions scope)
          ++ map DataTypeE              (maybeToList $ lookup v $ dataTypes scope)
          ++ map (uncurry ConstructorE) cons

runScopeT :: Monad m => ScopeT f m a -> m a
runScopeT (ScopeT f) = evalStateT f $ ScopeState [] [] []
