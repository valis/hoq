{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Expressions.Patterns
    ( typeCheckPatterns, typeCheckPattern
    , TermsInCtx(..), TermInCtx(..)
    ) where

import Data.Void
import Control.Monad

import Semantics
import Semantics.Value as V
import Semantics.Pattern as P
import Syntax as S
import Syntax.ErrorDoc
import TypeChecking.Context as C
import TypeChecking.Monad
import TypeChecking.Expressions.Utils
import Normalization

data TermInCtx b  = forall a. Eq a => TermInCtx  (Ctx String (Type Semantics) b a) (Pattern  b a) (Term Semantics a)
data TermsInCtx b = forall a. Eq a => TermsInCtx (Ctx String (Type Semantics) b a) (Patterns b a) [Term Semantics a] (Type Semantics a)

unexpectedPatternErrorMsg :: Posn -> Ctx String (Type Semantics) Void a -> Term Semantics a -> Error
unexpectedPatternErrorMsg pos ctx ty = Error TypeMismatch $
    emsgLC pos "" $ pretty "Unexpected pattern"
                 $$ pretty "Expected type:" <+> prettyOpen ctx ty

typeCheckPattern :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a
    -> Type Semantics a -> Term PName b -> TCM m (Bool, TermInCtx a)
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (Apply (pos, Ident "left") pats) = do
    unless (null pats) $ warn [tooManyArgs pos]
    return (False, TermInCtx C.Nil (PatICon ILeft) $ iCon ILeft)
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (Apply (pos, Ident "right") pats) = do
    unless (null pats) $ warn [tooManyArgs pos]
    return (False, TermInCtx C.Nil (PatICon IRight) $ iCon IRight)
typeCheckPattern ctx ty@(Type (Apply (Semantics _ (DataType _ 0)) _) _) (Apply (_, Operator "") _) =
    return (True, TermInCtx (Snoc C.Nil "_" ty) (PatVar "_") bvar)
typeCheckPattern ctx (Type ty _) (Apply (pos, Operator "") _) =
    throwError [Error Other $ emsgLC pos "" $ pretty "Expected non-empty type:" <+> prettyOpen ctx ty]
typeCheckPattern ctx ty (Apply (_, Ident "_") []) = return (False, TermInCtx (Snoc C.Nil "_" ty) (PatVar "_") bvar)
typeCheckPattern ctx ty@(Type (Apply (Semantics _ (DataType dt n)) params) _) (Apply (pos, var) []) = do
    cons <- lift $ getConstructor var $ Just (dt, params)
    case (cons, var) of
        ((_, con@(Apply (Semantics syn (DCon i _ _)) _), conds, _, Type conType _):_, _) -> if isDataType conType
            then return (False, TermInCtx C.Nil (PatDCon syn i n conds params P.Nil) con)
            else throwError [notEnoughArgs pos $ nameToPrefix var]
        (_, Ident var') -> return (False, TermInCtx (Snoc C.Nil var' ty) (PatVar var') bvar)
        _               -> throwError [unexpectedPatternErrorMsg pos ctx $ getType ty]
  where
    isDataType :: Term Semantics a -> Bool
    isDataType (Lambda t) = isDataType t
    isDataType (Apply (Semantics _ DataType{}) _) = True
    isDataType _ = False
typeCheckPattern ctx ty (Apply (pos, Ident var) []) = return (False, TermInCtx (Snoc C.Nil var ty) (PatVar var) bvar)
typeCheckPattern ctx (Type (Apply (Semantics _ (DataType dt n)) params) _) (Apply (pos, conName) pats) = do
    cons <- lift $ getConstructor conName $ Just (dt, params)
    case cons of
        (_, con@(Apply (Semantics syn (DCon i _ _)) _), conds, _, conType):_ -> do
            (bf, TermsInCtx ctx' rtpats terms (Type ty' _)) <- typeCheckPatterns ctx (nfType WHNF conType) pats
            case nf WHNF ty' of
                Apply (Semantics _ DataType{}) _ ->
                    return (bf, TermInCtx ctx' (PatDCon syn i n conds params rtpats) $ apps (fmap (liftBase ctx') con) terms)
                _ -> throwError [notEnoughArgs pos $ nameToPrefix conName]
        _ -> throwError [notInScope pos "data constructor" $ nameToPrefix conName]
typeCheckPattern ctx (Type ty _) (Apply (pos, _) _) = throwError [unexpectedPatternErrorMsg pos ctx ty]
typeCheckPattern _ _ _ = error "typeCheckPattern"

typeCheckPatterns :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a
    -> Type Semantics a -> [Term PName b] -> TCM m (Bool, TermsInCtx a)
typeCheckPatterns _ ty [] = return (False, TermsInCtx C.Nil P.Nil [] ty)
typeCheckPatterns ctx (Type (Apply p@(Semantics _ (V.Pi k1 k2)) [a, b]) _) (pat:pats) = do
    let a' = Type (nf WHNF a) k1
    (bf1, TermInCtx ctx' rtpat te) <- typeCheckPattern ctx a' pat
    let b' = case b of
                Lambda{} -> instantiate1 te $ fmap (fmap $ liftBase ctx') $ snd (dropOnePi p a b)
                _        -> fmap (liftBase ctx') b
    (bf2, TermsInCtx ctx'' rtpats tes ty) <- typeCheckPatterns (ctx C.+++ ctx') (Type (nf WHNF b') k2) pats
    return (bf1 || bf2, TermsInCtx (ctx' C.+++ ctx'') (Cons rtpat rtpats) (fmap (liftBase ctx'') te : tes) ty)
typeCheckPatterns _ _ (Apply (pos, _) _ : _) = throwError [tooManyArgs pos]
typeCheckPatterns _ _ _ = error "typeCheckPatterns"
