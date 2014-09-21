{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module TypeChecking.Monad.Scope
    ( ScopeT, runScopeT
    , addFunction, addConstructor, addDataType, addField
    , replaceDataType, replaceFunction, replaceConstructor
    , getDataType, getFunction, getField
    , getConstructor, getEntry
    , getDataTypeByID, getFields
    ) where

import Control.Monad
import Control.Monad.Fix
import Control.Monad.State
import Control.Applicative
import Data.Maybe
import Data.List

import Syntax hiding (Clause)
import Semantics
import Semantics.Value
import Semantics.Pattern

data ScopeState = ScopeState
    { functions    :: [(Name, (Semantics, Closed (Type Semantics)))]
    , dataTypes    :: [(Name, (Semantics, Closed (Type Semantics)))]
    , constructors :: [((Name, ID), (Name, Semantics, [Closed Clause], [[Closed Clause]], Closed (Type Semantics)))]
    , fields       :: [((String, ID), (Int, SEval, Closed (Type Semantics)))]
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

getDataTypeByID :: Monad m => ID -> ScopeT m Name
getDataTypeByID dt = ScopeT $ liftM (fst . head . filter (\(_,(Semantics _ (DataType dt' _), _)) -> dt == dt') . dataTypes) get

addField :: Monad m => String -> ID -> Int -> SEval -> Closed (Type Semantics) -> ScopeT m ()
addField fn dtID ind e ty = ScopeT $ modify $ \scope -> scope { fields = ((fn, dtID), (ind, e, ty)) : fields scope }

getField :: Monad m => String -> ID -> ScopeT m (Maybe (Int, SEval, Closed (Type Semantics)))
getField fn dtID = ScopeT $ liftM (lookup (fn,dtID) . fields) get

getFields :: Monad m => ID -> ScopeT m [(String, SEval, Closed (Type Semantics))]
getFields dtID = ScopeT $ liftM (map (\((fn,_),(_,e,ty)) -> (fn,e,ty))
                                . sortBy (\(_,(i,_,_)) (_,(i',_,_)) -> compare i i')
                                . filter (\((_,dtID'),_) -> dtID == dtID') . fields) get

lookupDelete :: Eq a => a -> [(a,b)] -> Maybe (b, [(a,b)])
lookupDelete _ [] = Nothing
lookupDelete a' ((a,b):xs) | a == a' = Just (b, xs)
                           | otherwise = fmap (\(b',xs') -> (b', (a,b):xs')) (lookupDelete a' xs)

addConstructor :: Monad m => Name -> (ID,Name) -> Int -> [Closed Clause] -> [[Closed Clause]] -> Closed (Type Semantics) -> ScopeT m ()
addConstructor con dt i e es ty = ScopeT $ modify (updScopeConstructor con dt i e es ty)

updScopeConstructor :: Name -> (ID, Name) -> Int -> [Closed Clause] -> [[Closed Clause]] -> Closed (Type Semantics) -> ScopeState -> ScopeState
updScopeConstructor con (dtID, dtName) i e es ty scope =
    let cs = map (\(Closed c) -> (fst $ clauseToEval c, Closed $ snd $ clauseToEval c)) e
    in scope { constructors = ((con, dtID), (dtName, Semantics (Name Prefix con) $ DCon i 0 cs, e, es, ty)) : constructors scope }

replaceConstructor :: Monad m => Name -> (ID, Name) -> Int -> [Closed Clause] -> [[Closed Clause]] -> Closed (Type Semantics) -> ScopeT m ()
replaceConstructor con dt@(dtID, dtName) i e es ty = ScopeT $ modify $ \scope ->
    case lookupDelete (con,dtID) (constructors scope) of
        Just (_, constructors') -> updScopeConstructor con dt i e es ty $ scope { constructors = constructors' }
        _ -> updScopeConstructor con dt i e es ty scope

getConstructor :: Monad m => Name -> Maybe (ID, [Term Semantics a])
    -> ScopeT m [(Name, Term Semantics a, [Closed Clause], [[Closed Clause]], Type Semantics a)]
getConstructor con (Just (dt, params)) = ScopeT $ do
    scope <- get
    return $ map (\(n, Semantics syn (DCon i _ e), cs, es, Closed (Type ty k)) ->
        (n, if null e
            then capply $ Semantics syn (DCon i 0 [])
            else Apply (Semantics syn $ DCon i (length params) e) params
        , cs, es, Type (apps ty params) k
        )) $ maybeToList $ lookup (con, dt) (constructors scope)
getConstructor con Nothing = ScopeT $ do
    scope <- get
    return $ map (\(_, (n, s, cs, es, Closed ty)) -> (n, capply s, cs, es, ty)) $ filter (\((c,_),_) -> con == c) (constructors scope)

getEntry :: Monad m => Name -> Maybe (ID, [Term Semantics a]) -> ScopeT m [(Term Semantics a, [[Closed Clause]], Type Semantics a)]
getEntry v dt = ScopeT $ do
    cons  <- unScopeT $ getConstructor v dt
    scope <- get
    let dts = if isNothing dt then maybeToList $ lookup v $ dataTypes scope else []
    return $ map (\(s, Closed t) -> (capply s, [], t)) (maybeToList (lookup v $ functions scope) ++ dts)
            ++ if null dts then map (\(_,a,_,c,d) -> (a,c,d)) cons else []

runScopeT :: Monad m => ScopeT m a -> m a
runScopeT (ScopeT f) = evalStateT f $ ScopeState [] [] [] [] 0
