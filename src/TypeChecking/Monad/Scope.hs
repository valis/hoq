{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecking.Monad.Scope
    ( ScopeT, runScopeT
    , addFunction, addConstructor, addDataType
    , replaceDataType, replaceFunction, replaceConstructor
    , getDataType, getFunction
    , getConstructor, getEntry
    ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.State
import Control.Applicative
import Data.Maybe
import Data.Bifunctor

import Syntax
import Semantics
import Semantics.Value

type PEval = [([Term (Name, Pattern) String], Closed (Term Semantics))]
data ScopeState = ScopeState
    { functions    :: [(Name, (Semantics, Closed (Type Semantics)))]
    , dataTypes    :: [(Name, (Semantics, Closed (Type Semantics)))]
    , constructors :: [((Name, ID), (Semantics, [[Term Pattern String]], [[SEval]], Closed (Type Semantics)))]
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

addConstructor :: Monad m => Name -> ID -> Int -> PEval -> Closed (Type Semantics) -> ScopeT m ()
addConstructor con dt i e ty = ScopeT $ modify (updScopeConstructor con dt i e ty)

updScopeConstructor :: Name -> ID -> Int -> PEval -> Closed (Type Semantics) -> ScopeState -> ScopeState
updScopeConstructor con dt i e ty scope =
    let dcon = DCon i 0 $ map (first $ map $ first $ patternToInt . snd) e
        ent = (Semantics (Name Prefix con) dcon, map (map (first snd) . fst) e, [], ty)
    in scope { constructors = ((con, dt), ent) : constructors scope }

replaceConstructor :: Monad m => Name -> ID -> Int -> PEval -> Closed (Type Semantics) -> ScopeT m ()
replaceConstructor con dt i e ty = ScopeT $ modify $ \scope -> case lookupDelete (con,dt) (constructors scope) of
    Just (_, constructors') -> updScopeConstructor con dt i e ty $ scope { constructors = constructors' }
    _ -> updScopeConstructor con dt i e ty scope

getConstructor :: Monad m => Name -> Maybe (ID, [Term Semantics a])
    -> ScopeT m [(Term Semantics a, [[Term Pattern String]], [[SEval]], Type Semantics a)]
getConstructor con (Just (dt, params)) = ScopeT $ do
    scope <- get
    return $ map (\(Semantics syn (DCon i _ e), cs, es, Closed (Type ty k)) ->
        ( if null e
            then capply $ Semantics syn (DCon i 0 [])
            else Apply (Semantics syn $ DCon i (length params) e) params
        , cs, es, Type (apps ty params) k
        )) $ maybeToList $ lookup (con, dt) (constructors scope)
getConstructor con Nothing = ScopeT $ do
    scope <- get
    return $ map (\(_, (s, cs, es, Closed ty)) -> (capply s, cs, es, ty)) $ filter (\((c,_),_) -> con == c) (constructors scope)

getEntry :: Monad m => Name -> Maybe (ID, [Term Semantics a]) -> ScopeT m [(Term Semantics a, [[SEval]], Type Semantics a)]
getEntry v dt = ScopeT $ do
    cons  <- unScopeT $ getConstructor v dt
    scope <- get
    let dts = if isNothing dt then maybeToList $ lookup v $ dataTypes scope else []
    return $ map (\(s, Closed t) -> (capply s, [],t)) (maybeToList (lookup v $ functions scope) ++ dts)
            ++ if null dts then map (\(a,_,c,d) -> (a,c,d)) cons else []

runScopeT :: Monad m => ScopeT m a -> m a
runScopeT (ScopeT f) = evalStateT f $ ScopeState [] [] [] 0
