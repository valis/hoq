{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Expressions.Patterns
    ( typeCheckPatterns, typeCheckPattern
    , TermsInCtx(..), TermInCtx(..)
    , Pattern, patternToInt
    ) where

import Data.Void
import Control.Monad

import Semantics
import Semantics.Value as V
import Syntax as S
import Syntax.ErrorDoc
import TypeChecking.Context
import TypeChecking.Monad
import TypeChecking.Expressions.Utils
import Normalization

data TermInCtx b  = forall a. Eq a => TermInCtx  (Ctx String (Type Semantics) b a) (Term Semantics a)
data TermsInCtx b = forall a. Eq a => TermsInCtx (Ctx String (Type Semantics) b a) [Term Semantics a] (Type Semantics a)

data Pattern = PatDCon Int Int SEval | PatPCon | PatICon ICon

patternToInt :: Pattern -> Int
patternToInt (PatDCon i _ _) = i
patternToInt PatPCon = 0
patternToInt (PatICon ILeft) = 0
patternToInt (PatICon IRight) = 1

unexpectedPatternErrorMsg :: Posn -> Ctx String (Type Semantics) Void a -> Term Semantics a -> Error
unexpectedPatternErrorMsg pos ctx ty = Error TypeMismatch $
    emsgLC pos "" $ pretty "Unexpected pattern"
                 $$ pretty "Expected type:" <+> prettyOpen ctx ty

typeCheckPattern :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> Type Semantics a
    -> Term PName b -> TCM m (Bool, Maybe (TermInCtx a), Term (Name,Pattern) String)
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (Apply (pos, Ident "left") pats) = do
    unless (null pats) $ warn [tooManyArgs pos]
    return (False, Just $ TermInCtx Nil $ iCon ILeft, Apply (Ident "left", PatICon ILeft) [])
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (Apply (pos, Ident "right") pats) = do
    unless (null pats) $ warn [tooManyArgs pos]
    return (False, Just $ TermInCtx Nil $ iCon IRight, Apply (Ident "right", PatICon IRight) [])
typeCheckPattern ctx (Type (Apply (Semantics _ (DataType _ 0)) _) _) (Apply (_, Operator "") _) =
    return (True, Nothing, Var "_" [])
typeCheckPattern ctx (Type ty _) (Apply (pos, Operator "") _) =
    throwError [Error Other $ emsgLC pos "" $ pretty "Expected non-empty type:" <+> prettyOpen ctx ty]
typeCheckPattern ctx _ (Apply (_, Ident "_") []) = return (False, Nothing, Var "_" [])
typeCheckPattern ctx (Type ty@(Apply (Semantics _ (DataType dt n)) params) k) (Apply (pos, var) []) = do
    cons <- lift $ getConstructor var $ Just (dt, params)
    case (cons, var) of
        ((con@(Apply (Semantics _ (DCon i _ conds)) _), _, Type conType _):_, _) -> if isDataType conType
            then return (False, Just $ TermInCtx Nil con, capply (var, PatDCon i n conds))
            else throwError [notEnoughArgs pos $ nameToPrefix var]
        (_, Ident var') -> return (False, Just $ TermInCtx (Snoc Nil var' $ Type ty k) bvar, cvar var')
        _               -> throwError [unexpectedPatternErrorMsg pos ctx ty]
  where
    isDataType :: Term Semantics a -> Bool
    isDataType (Lambda t) = isDataType t
    isDataType (Apply (Semantics _ DataType{}) _) = True
    isDataType _ = False
typeCheckPattern ctx (Type ty k) (Apply (pos, Ident var) []) =
    return (False, Just $ TermInCtx (Snoc Nil var $ Type ty k) bvar, cvar var)
typeCheckPattern ctx (Type (Apply (Semantics _ (DataType dt n)) params) _) (Apply (pos, conName) pats) = do
    cons <- lift $ getConstructor conName $ Just (dt, params)
    case cons of
        (con@(Apply (Semantics _ (DCon i _ conds)) _), _, conType):_ -> do
            (bf, TermsInCtx ctx' terms (Type ty' _), rtpats) <- typeCheckPatterns ctx (nfType WHNF conType) pats
            case nf WHNF ty' of
                Apply (Semantics _ DataType{}) _ ->
                    let term = TermInCtx ctx' $ apps (fmap (liftBase ctx') con) terms
                    in return (bf, Just term, Apply (conName, PatDCon i n conds) rtpats)
                _ -> throwError [notEnoughArgs pos $ nameToPrefix conName]
        _ -> throwError [notInScope pos "data constructor" $ nameToPrefix conName]
typeCheckPattern ctx (Type ty _) (Apply (pos, _) _) = throwError [unexpectedPatternErrorMsg pos ctx ty]
typeCheckPattern _ _ _ = error "typeCheckPattern"

typeCheckPatterns :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> Type Semantics a
    -> [Term PName b] -> TCM m (Bool, TermsInCtx a, [Term (Name,Pattern) String])
typeCheckPatterns _ ty [] = return (False, TermsInCtx Nil [] ty, [])
typeCheckPatterns ctx (Type (Apply p@(Semantics _ (V.Pi k1 k2)) [a, b]) _) (pat:pats) = do
    let a' = Type (nf WHNF a) k1
    (bf1, mte, rtpat) <- typeCheckPattern ctx a' pat
    TermInCtx ctx' te <- case mte of
                            Nothing -> return $ TermInCtx (Snoc Nil "_" a') bvar
                            Just te -> return te
    let b' = case b of
                Lambda{} -> instantiate1 te $ fmap (fmap $ liftBase ctx') $ snd (dropOnePi p a b)
                _        -> fmap (liftBase ctx') b
    (bf2, TermsInCtx ctx'' tes ty, rtpats) <- typeCheckPatterns (ctx +++ ctx') (Type (nf WHNF b') k2) pats
    return (bf1 || bf2, TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats)
typeCheckPatterns _ _ (Apply (pos, _) _ : _) = throwError [tooManyArgs pos]
typeCheckPatterns _ _ _ = error "typeCheckPatterns"
