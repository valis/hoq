{-# LANGUAGE GADTs #-}

module TypeChecking.Patterns
    ( typeCheckPatterns
    , TermsInCtx(..)
    , checkCoverage
    ) where

import Control.Monad.Error

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import Syntax.Context
import TypeChecking.Monad
import TypeChecking.Expressions
import Normalization

{-
checkCoverage1 :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Term a -> [ParPat] -> TCM m ()
checkCoverage1 ctx term pats = undefined

checkCoverageD :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Term a -> [[ParPat]] -> TCM m ()
checkCoverageD ctx term ([]:_) = return ()
checkCoverageD ctx term patss | any null patss = return ()
                              | otherwise      = checkCoverage1 ctx term (map head patss)
-}

checkCoverage :: Monad m => Term String -> [([ParPat], Maybe Expr)] -> TCM m ()
checkCoverage _ _ = return () -- TODO

data TermsInCtx a where
    TermsInCtx :: Eq b => Ctx Int [String] Term a b -> [Term b] -> Term b -> TermsInCtx a

instance Error () where
    noMsg = ()

typeCheckPattern :: (Monad m, Eq a) => Ctx Int [String] Term String a
    -> Term a -> ParPat -> ErrorT () (TCM m) (TermInCtx Int [String] Term a, RTPattern)
typeCheckPattern ctx ty (ParEmpty _) = throwError ()
typeCheckPattern ctx ty (ParVar arg) = do
    let var = unArg arg
    cons <- lift $ lift $ getConstructor var $ case ty of
        DataType dt _ -> Just dt
        _             -> Nothing
    case cons of
        []       -> return (TermInCtx (Snoc Nil [var] ty) $ T.Var (B 0), RTPatternVar)
        [(i,_)]  -> return (TermInCtx Nil $ T.Con i var [], RTPattern i [])
        _        -> lift $ throwError [inferErrorMsg (argGetPos arg) $ "data constructor " ++ show var]
typeCheckPattern ctx (DataType dt params) (ParPat _ (E.Pattern (PIdent (lc,conName)) pats)) = do
    cons <- lift $ lift $ getConstructor conName (Just dt)
    (i, conType) <- case cons of
        []                     -> lift $ throwError [notInScope lc "data constructor" conName]
        (i, Left  conType) : _ -> return (i, fmap (liftBase ctx) conType)
        (i, Right conType) : _ -> return (i, conType >>= \v -> case v of
                                                                B i -> reverse params !! i
                                                                F a -> T.Var $ liftBase ctx a)
    (TermsInCtx ctx' terms _, rtpats) <- typeCheckPatterns ctx conType pats
    return (TermInCtx ctx' $ T.Con i conName terms, RTPattern i rtpats)
typeCheckPattern ctx ty (ParPat (PPar (lc,_)) _) = lift $
    throwError [emsgLC lc "" $ pretty "Unexpected pattern" $$
                               pretty "Expected type:" <+> prettyOpen ctx ty]

typeCheckPatterns :: (Monad m, Eq a) => Ctx Int [String] Term String a -> Term a -> [ParPat]
    -> ErrorT () (TCM m) (TermsInCtx a, [RTPattern])
typeCheckPatterns _ ty [] = return (TermsInCtx Nil [] ty, [])
typeCheckPatterns ctx (T.Arr a b) (pat:pats) = do
    (TermInCtx ctx' te, rtpat) <- typeCheckPattern ctx (nf WHNF a) pat
    (TermsInCtx ctx'' tes ty, rtpats) <- typeCheckPatterns (ctx +++ ctx') (nf WHNF $ fmap (liftBase ctx') b) pats
    return (TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats)
typeCheckPatterns ctx (T.Pi fl a b) (pat:pats) = do
    (TermInCtx ctx' te, rtpat) <- typeCheckPattern ctx (nf WHNF a) pat
    let b' = either (T.Pi fl $ fmap (liftBase ctx') a) id $ instantiateNames1 te $ fmap (liftBase ctx') b
    (TermsInCtx ctx'' tes ty, rtpats) <- typeCheckPatterns (ctx +++ ctx') (nf WHNF b') pats
    return (TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats)
typeCheckPatterns _ _ (pat:_) = lift $ throwError [emsgLC (parPatGetPos pat) "Too many arguments" enull]
