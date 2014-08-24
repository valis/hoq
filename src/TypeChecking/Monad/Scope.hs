{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecking.Monad.Scope
    ( ScopeT, runScopeT
    , addFunction, addConstructor, addDataType
    , replaceDataType, replaceFunction
    , getDataType, getFunction
    , getConstructor, getEntry
    ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.State
import Control.Applicative
import Data.Maybe

import Syntax
import Semantics
import Semantics.Value

data ScopeState = ScopeState
    { functions    :: [(Name, (Semantics, Closed (Type Semantics)))]
    , dataTypes    :: [(Name, (Semantics, Closed (Type Semantics)))]
    , constructors :: [((Name, ID), (Semantics, [[SEval]], Closed (Type Semantics)))]
    , counter      :: ID
    }

newtype ScopeT m a = ScopeT { unScopeT :: StateT ScopeState m a }
    deriving (Functor,Monad,MonadTrans,MonadIO,MonadFix,Applicative)

addFunction :: Monad m => Name -> SEval -> Closed (Type Semantics) -> ScopeT m ID
addFunction v e ty = ScopeT $ do
    scope <- get
    let (fc,scope') = updScopeFunction v e ty scope
    put scope'
    return fc

replaceFunction :: Monad m => Name -> SEval -> Closed (Type Semantics) -> ScopeT m ()
replaceFunction v e ty = ScopeT $ modify $ \scope -> case lookupDelete v (functions scope) of
    Just ((Semantics s (FunCall i _),_), functions') -> scope { functions = (v, (Semantics s (FunCall i e), ty)) : functions' }
    _ -> snd (updScopeFunction v e ty scope)

updScopeFunction :: Name -> SEval -> Closed (Type Semantics) -> ScopeState -> (ID, ScopeState)
updScopeFunction v e ty scope = (counter scope, scope
    { functions = (v, (Semantics (Name Prefix v) (FunCall (counter scope) e), ty)) : functions scope
    , counter = counter scope + 1
    })

getFunction :: Monad m => Name -> ScopeT m [(Semantics, Closed (Type Semantics))]
getFunction v = ScopeT $ liftM (map snd . filter (\(v',_) -> v == v') . functions) get

addDataType :: Monad m => Name -> Int -> Closed (Type Semantics) -> ScopeT m ID
addDataType v n ty = ScopeT $ do
    scope <- get
    let (dt,scope') = updScopeDataType v n ty scope
    put scope'
    return dt

replaceDataType :: Monad m => Name -> Int -> Closed (Type Semantics) -> ScopeT m ()
replaceDataType v n ty = ScopeT $ modify $ \scope -> case lookupDelete v (dataTypes scope) of
    Just ((Semantics s (DataType i _), _), dataTypes') -> scope { dataTypes = (v, (Semantics s (DataType i n), ty)) : dataTypes' }
    _ -> snd (updScopeDataType v n ty scope)

updScopeDataType :: Name -> Int -> Closed (Type Semantics) -> ScopeState -> (ID, ScopeState)
updScopeDataType v n ty scope = (counter scope, scope
    { dataTypes = (v, (Semantics (Name Prefix v) (DataType (counter scope) n), ty)) : dataTypes scope
    , counter = counter scope + 1
    })

getDataType :: Monad m => Name -> ScopeT m [(Semantics, Closed (Type Semantics))]
getDataType v = ScopeT $ liftM (map snd . filter (\(v',_) -> v == v') . dataTypes) get

lookupDelete :: Eq a => a -> [(a,b)] -> Maybe (b, [(a,b)])
lookupDelete _ [] = Nothing
lookupDelete a' ((a,b):xs) | a == a' = Just (b, xs)
                           | otherwise = fmap (\(b',xs') -> (b', (a,b):xs')) (lookupDelete a' xs)

addConstructor :: Monad m => Name -> ID -> Int -> Int -> SEval -> Closed (Type Semantics) -> ScopeT m ()
addConstructor con dt i n e ty = ScopeT $ modify $ \scope -> scope
    { constructors = ((con, dt), (Semantics (Name Prefix con) (Con $ DCon i n e), [], ty)) : constructors scope
    }

getConstructor :: Monad m => Name -> Maybe ID -> ScopeT m [(Semantics, [[SEval]], Closed (Type Semantics))]
getConstructor con (Just dt) = ScopeT $ liftM (maybeToList . lookup (con, dt) . constructors) get
getConstructor con Nothing   = ScopeT $ liftM (map snd . filter (\((c,_),_) -> con == c) . constructors) get

getEntry :: Monad m => Name -> Maybe (ID, [Term Semantics a]) -> ScopeT m [(Semantics, Type Semantics a)]
getEntry v dt = ScopeT $ do
    cons  <- unScopeT $ getConstructor v (fmap fst dt)
    scope <- get
    let dts = if isNothing dt then maybeToList $ lookup v $ dataTypes scope else []
    return $ map (\(s,t) -> (s, open t)) (maybeToList (lookup v $ functions scope) ++ dts)
            ++ if null dts then (map (\(s, _, Closed (Type t l)) -> (s, Type (apps t (maybe [] snd dt)) l)) cons) else []

runScopeT :: Monad m => ScopeT m a -> m a
runScopeT (ScopeT f) = evalStateT f $ ScopeState [] [] [] 0
