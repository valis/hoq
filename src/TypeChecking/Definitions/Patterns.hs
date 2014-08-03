{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Definitions.Patterns
    ( typeCheckPatterns
    , TermsInCtx(..)
    ) where

import Data.Void

import Semantics
import Semantics.Value as V
import Syntax as S
import Syntax.ErrorDoc
import TypeChecking.Context
import TypeChecking.Monad
import TypeChecking.Expressions
import Normalization

data TermInCtx b  = forall a. Eq a => TermInCtx  (Ctx String (Type Semantics) b a) (Term Semantics a)
data TermsInCtx b = forall a. Eq a => TermsInCtx (Ctx String (Type Semantics) b a) [Term Semantics a] (Type Semantics a)

typeCheckPattern :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> Type Semantics a
    -> PatternP PIdent -> TCM m (Bool, Maybe (TermInCtx a), PatternC String)
typeCheckPattern _ _ PatternI{} = error "typeCheckPattern: PatternI"
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (PatternVar (PIdent _ "left")) =
    return (False, Just $ TermInCtx Nil $ iCon ILeft, PatternI () ILeft)
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (PatternVar (PIdent _ "right")) =
    return (False, Just $ TermInCtx Nil $ iCon IRight, PatternI () IRight)
typeCheckPattern ctx (Type ty _) (PatternEmpty _) | (Just (Semantics _ (DataType _ 0)), _) <- collect ty =
    return (True, Nothing, PatternVar "_")
typeCheckPattern ctx (Type ty _) (PatternEmpty pos) =
    throwError [emsgLC pos "" $ pretty "Expected non-empty type:" <+> prettyOpen ctx ty]
typeCheckPattern ctx _ (PatternVar (PIdent _ "_")) = return (False, Nothing, PatternVar "_")
typeCheckPattern ctx (Type ty lvl) (PatternVar (PIdent pos var)) = case collect ty of
    (Just (Semantics (Ident dtn) (DataType dt _)), params) -> do
        cons <- lift $ getConstructor var (Just dtn)
        case cons of
            [] -> return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ Var Bound, PatternVar var)
            (n,con,(conType,_)):_ -> if isDataType conType
                then let con'@(Apply (Semantics (Ident conName) (Con i conds)) _) = instantiate params $ fmap (liftBase ctx) con
                     in return (False, Just $ TermInCtx Nil con', Pattern (PatternCon i n conName conds) [])
                else throwError [emsgLC pos ("Not enough arguments to " ++ show var) enull]
    _ -> return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ Var Bound, PatternVar var)
  where
    isDataType :: Scope a (Term Semantics) b -> Bool
    isDataType (ScopeTerm ty) = case collect ty of
        (Just (Semantics _ DataType{}), _)  -> True
        _                                   -> False
    isDataType (Scope _ t) = isDataType t
typeCheckPattern ctx (Type ty _) (Pattern (PatternCon _ _ (PIdent pos conName) _) pats)
  | (Just (Semantics (Ident dtn) (DataType dt _)), params) <- collect ty = do
    cons <- lift $ getConstructor conName (Just dtn)
    case cons of
        []        -> throwError [notInScope pos "data constructor" conName]
        (n,con,(conType,lvl)):_ -> do
            let Apply (Semantics _ (Con i conds)) _ = instantiate params $ fmap (liftBase ctx) con
                conType' = Type (nf WHNF $ instantiate params $ fmap (liftBase ctx) conType) lvl
            (bf, TermsInCtx ctx' terms (Type ty _), rtpats) <- typeCheckPatterns ctx conType' pats
            let res = TermInCtx ctx' $ capps (Semantics (Ident conName) $ Con i conds) terms
            case collect (nf WHNF ty) of
                (Just (Semantics _ DataType{}), _) -> return (bf, Just res, Pattern (PatternCon i n conName conds) rtpats)
                _ -> throwError [emsgLC pos "Not enough arguments" enull]
typeCheckPattern ctx (Type ty _) pat =
    throwError [emsgLC (patternGetAttr getPos pat) "" $ pretty "Unexpected pattern"
                                                     $$ pretty "Expected type:" <+> prettyOpen ctx ty]

typeCheckPatterns :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> Type Semantics a
    -> [PatternP PIdent] -> TCM m (Bool, TermsInCtx a, [PatternC String])
typeCheckPatterns _ ty [] = return (False, TermsInCtx Nil [] ty, [])
typeCheckPatterns ctx (Type (Apply p@(Semantics (S.Pi vs) (V.Pi l1 l2)) [a, b]) _) (pat:pats) = do
    let a' = Type (nf WHNF a) l1
    (bf1, mte, rtpat) <- typeCheckPattern ctx a' pat
    TermInCtx ctx' te <- case mte of
                            Nothing ->  let var = if null vs then "_" else head vs
                                        in return $ TermInCtx (Snoc Nil var a') (Var Bound)
                            Just te -> return te
    let b' = case b of
                Lambda{} -> instantiate1 te $ fmap (fmap $ liftBase ctx') $ snd (dropOnePi p a b)
                _        -> fmap (liftBase ctx') b
    (bf2, TermsInCtx ctx'' tes ty, rtpats) <- typeCheckPatterns (ctx +++ ctx') (Type (nf WHNF b') l2) pats
    return (bf1 || bf2, TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats)
typeCheckPatterns _ _ (pat:_) = throwError [emsgLC (patternGetAttr getPos pat) "Too many arguments" enull]
