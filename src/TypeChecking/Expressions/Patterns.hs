{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Expressions.Patterns
    ( typeCheckPatterns, typeCheckPattern
    , TermsInCtx(..), TermInCtx(..)
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

notEnoughArgs :: Show a => Posn -> a -> EMsg f
notEnoughArgs pos a = emsgLC pos ("Not enough arguments to " ++ show a) enull

tooManyArgs :: Posn -> EMsg f
tooManyArgs pos = emsgLC pos "Too many arguments" enull

typeCheckPattern :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> Type Semantics a
    -> Term PName b -> TCM m (Bool, Maybe (TermInCtx a), Term (String,SCon) String)
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (Apply (pos, Ident "left") pats) = do
    unless (null pats) $ warn [tooManyArgs pos]
    return (False, Just $ TermInCtx Nil $ iCon ILeft, Apply ("left", ICon ILeft) [])
typeCheckPattern ctx (Type (Apply (Semantics _ Interval) _) _) (Apply (pos, Ident "right") pats) = do
    unless (null pats) $ warn [tooManyArgs pos]
    return (False, Just $ TermInCtx Nil $ iCon IRight, Apply ("right", ICon IRight) [])
typeCheckPattern ctx (Type (Apply (Semantics _ (DataType _ 0)) _) _) (Apply (_, Operator "") _) =
    return (True, Nothing, Var "_" [])
typeCheckPattern ctx (Type ty _) (Apply (pos, Operator "") _) =
    throwError [emsgLC pos "" $ pretty "Expected non-empty type:" <+> prettyOpen ctx ty]
typeCheckPattern ctx _ (Apply (_, Ident "_") []) = return (False, Nothing, Var "_" [])
typeCheckPattern ctx (Type ty@(Apply (Semantics _ (DataType dt _)) _) lvl) (Apply (pos, Ident var) []) = do
    cons <- lift $ getConstructor (Ident var) (Just dt)
    case cons of
        (con@(Semantics _ (Con (DCon i n conds))), Type conType _):_ -> if isDataType conType
            then return (False, Just $ TermInCtx Nil $ capply con, Apply (var, DCon i n conds) [])
            else throwError [notEnoughArgs pos var]
        _ -> return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ cvar Bound, Var var [])
  where
    isDataType :: Term Semantics a -> Bool
    isDataType (Lambda t) = isDataType t
    isDataType (Apply (Semantics _ DataType{}) _) = True
    isDataType _ = False
typeCheckPattern ctx (Type ty lvl) (Apply (pos, Ident var) []) =
    return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ cvar Bound, Var var [])
typeCheckPattern ctx (Type (Apply (Semantics _ (DataType dt _)) params) _) (Apply (pos, Ident conName) pats) = do
    cons <- lift $ getConstructor (Ident conName) (Just dt)
    case cons of
        (con@(Semantics _ (Con (DCon i n conds))), Type conType lvl):_ -> do
            let conType' = Type (nf WHNF $ apps (vacuous conType) params) lvl
            (bf, TermsInCtx ctx' terms (Type ty' _), rtpats) <- typeCheckPatterns ctx conType' pats
            case nf WHNF ty' of
                Apply (Semantics _ DataType{}) _ ->
                    return (bf, Just $ TermInCtx ctx' (Apply con terms), Apply (conName, DCon i n conds) rtpats)
                _ -> throwError [notEnoughArgs pos conName]
        _ -> throwError [notInScope pos "data constructor" conName]
typeCheckPattern ctx (Type ty _) (Apply (pos, _) _) =
    throwError [emsgLC pos "" $ pretty "Unexpected pattern"
                             $$ pretty "Expected type:" <+> prettyOpen ctx ty]
typeCheckPattern _ _ _ = error "typeCheckPattern"

typeCheckPatterns :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a -> Type Semantics a
    -> [Term PName b] -> TCM m (Bool, TermsInCtx a, [Term (String,SCon) String])
typeCheckPatterns _ ty [] = return (False, TermsInCtx Nil [] ty, [])
typeCheckPatterns ctx (Type (Apply p@(Semantics (S.Pi vs) (V.Pi l1 l2)) [a, b]) _) (pat:pats) = do
    let a' = Type (nf WHNF a) l1
    (bf1, mte, rtpat) <- typeCheckPattern ctx a' pat
    TermInCtx ctx' te <- case mte of
                            Nothing ->  let var = if null vs then "_" else head vs
                                        in return $ TermInCtx (Snoc Nil var a') (cvar Bound)
                            Just te -> return te
    let b' = case b of
                Lambda{} -> instantiate1 te $ fmap (fmap $ liftBase ctx') $ snd (dropOnePi p a b)
                _        -> fmap (liftBase ctx') b
    (bf2, TermsInCtx ctx'' tes ty, rtpats) <- typeCheckPatterns (ctx +++ ctx') (Type (nf WHNF b') l2) pats
    return (bf1 || bf2, TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats)
typeCheckPatterns _ _ (Apply (pos, _) _ : _) = throwError [tooManyArgs pos]
typeCheckPatterns _ _ _ = error "typeCheckPatterns"