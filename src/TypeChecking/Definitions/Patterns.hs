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

notEnoughArgs :: Show a => Posn -> a -> EMsg f
notEnoughArgs pos a = emsgLC pos ("Not enough arguments to " ++ show a) enull

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
    (Just (Semantics _ (DataType dt _)), params) -> do
        cons <- lift $ getConstructor var (Just dt)
        case cons of
            (n, con@(Semantics (Ident conName) (Con i (PatEval conds))), Type conType _):_ -> if isDataType conType
                then return (False, Just $ TermInCtx Nil $ cterm con, Pattern (PatternCon i n conName conds) [])
                else throwError [notEnoughArgs pos var]
            _ -> return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ Var Bound, PatternVar var)
    _ -> return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ Var Bound, PatternVar var)
  where
    isDataType :: Term Semantics a -> Bool
    isDataType (Lambda t) = isDataType t
    isDataType ty = case collect ty of
        (Just (Semantics _ DataType{}), _)  -> True
        _                                   -> False
typeCheckPattern ctx (Type ty _) (Pattern (PatternCon _ _ (PIdent pos conName) _) pats)
  | (Just (Semantics _ (DataType dt _)), params) <- collect ty = do
    cons <- lift $ getConstructor conName (Just dt)
    case cons of
        (n, con@(Semantics _ (Con i (PatEval conds))), Type conType lvl):_ -> do
            let conType' = Type (nf WHNF $ bapps (vacuous conType) params) lvl
            (bf, TermsInCtx ctx' terms (Type ty' _), rtpats) <- typeCheckPatterns ctx conType' pats
            case collect (nf WHNF ty') of
                (Just (Semantics _ DataType{}), _) -> return (bf, Just $ TermInCtx ctx' (capps con terms), Pattern (PatternCon i n conName conds) rtpats)
                _ -> throwError [notEnoughArgs pos conName]
        _ -> throwError [notInScope pos "data constructor" conName]
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
