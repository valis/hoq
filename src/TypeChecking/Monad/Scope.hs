{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecking.Monad.Scope
    ( ScopeT, runScopeT
    , addFunction, addConstructor, addDataType
    , deleteDataType
    , getConstructor, getConstructorDataTypes
    , Entry(..), getEntry
    ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.State
import Control.Applicative
import Data.List
import Data.Maybe

data Entry a b c d = FunctionE a b | DataTypeE b Int | ConstructorE Int c d

data ScopeState a b c d = ScopeState
    { functions    :: [(String, (a, b))]
    , dataTypes    :: [(String, (b, Int))]
    , constructors :: [((String, String), (Int, c, d))]
    }

newtype ScopeT a b c d m a' = ScopeT { unScopeT :: StateT (ScopeState a b c d) m a' }
    deriving (Functor,Monad,MonadTrans,MonadIO,MonadFix,Applicative)

addFunction :: Monad m => String -> a -> b -> ScopeT a b c d m ()
addFunction v te ty = ScopeT $ modify $ \scope -> scope { functions = (v, (te, ty)) : functions scope }

addDataType :: Monad m => String -> b -> Int -> ScopeT a b c d m ()
addDataType v ty b = ScopeT $ modify $ \scope -> scope { dataTypes = (v, (ty, b)) : dataTypes scope }

addConstructor :: Monad m => String -> String -> Int -> c -> d -> ScopeT a b c d m ()
addConstructor con dt n te ty = ScopeT $ modify $ \scope ->
    scope { constructors = ((con, dt), (n, te, ty)) : constructors scope }

deleteDataType :: Monad m => String -> ScopeT a b c d m ()
deleteDataType dt = ScopeT $ modify $ \scope ->
    scope { dataTypes = deleteBy (\(v1,_) (v2,_) -> v1 == v2) (dt, error "") (dataTypes scope) }

getConstructor :: Monad m => String -> Maybe String -> ScopeT a b c d m [(Int, c, d)]
getConstructor con (Just dt) = ScopeT $ liftM (maybeToList . lookup (con, dt) . constructors) get
getConstructor con Nothing   = ScopeT $ liftM (map snd . filter (\((c,_),_) -> con == c) . constructors) get

getConstructorDataTypes :: Monad m => String -> ScopeT a b c d m [String]
getConstructorDataTypes con = ScopeT $ liftM (map (snd . fst) . filter (\((c,_),_) -> con == c) . constructors) get

getEntry :: Monad m => String -> Maybe String -> ScopeT a b c d m [Entry a b c d]
getEntry v dt = ScopeT $ do
    cons  <- unScopeT (getConstructor v dt)
    scope <- get
    return $ map (uncurry FunctionE) (maybeToList $ lookup v $ functions scope)
          ++ map (uncurry DataTypeE) (maybeToList $ lookup v $ dataTypes scope)
          ++ map (\(i,c,d) -> ConstructorE i c d) cons

runScopeT :: Monad m => ScopeT a b c d m a' -> m a'
runScopeT (ScopeT f) = evalStateT f $ ScopeState [] [] []
