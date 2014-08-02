{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Definitions.Patterns
    ( typeCheckPatterns
    , TermsInCtx(..)
    ) where

import Data.Void

import Syntax
import Syntax.ErrorDoc
import TypeChecking.Context
import TypeChecking.Monad
import TypeChecking.Expressions
import Normalization

data TermInCtx b  = forall a. Eq a => TermInCtx  (Ctx String (Type Syntax) b a) (Term Syntax a)
data TermsInCtx b = forall a. Eq a => TermsInCtx (Ctx String (Type Syntax) b a) [Term Syntax a] (Type Syntax a)

typeCheckPattern :: (Monad m, Eq a) => Ctx String (Type Syntax) Void a -> Type Syntax a
    -> PatternP PIdent -> TCM m (Bool, Maybe (TermInCtx a), PatternC String)
typeCheckPattern _ _ PatternI{} = error "typeCheckPattern: PatternI"
typeCheckPattern ctx (Type (Apply Interval _) _) (PatternVar (PIdent _ "left")) =
    return (False, Just $ TermInCtx Nil $ cterm $ ICon ILeft, PatternI () ILeft)
typeCheckPattern ctx (Type (Apply Interval _) _) (PatternVar (PIdent _ "right")) =
    return (False, Just $ TermInCtx Nil $ cterm $ ICon IRight, PatternI () IRight)
typeCheckPattern ctx (Type ty _) (PatternEmpty _) | (Just (DataType _ 0), _) <- collect ty = return (True, Nothing, PatternVar "_")
typeCheckPattern ctx (Type ty _) (PatternEmpty pos) =
    throwError [emsgLC pos "" $ pretty "Expected non-empty type:" <+> prettyOpen ctx ty]
typeCheckPattern ctx _ (PatternVar (PIdent _ "_")) = return (False, Nothing, PatternVar "_")
typeCheckPattern ctx (Type ty lvl) (PatternVar (PIdent pos var)) = case collect ty of
    (Just (DataType dt _), params) -> do
        cons <- lift $ getConstructor var (Just dt)
        case cons of
            [] -> return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ Var Bound, PatternVar var)
            (n,con,(conType,_)):_ -> if isDataType conType
                then let con'@(Apply (Con i conName conds) _) = instantiate params $ fmap (liftBase ctx) con
                     in return (False, Just $ TermInCtx Nil con', Pattern (PatternCon i n (getName conName) conds) [])
                else throwError [emsgLC pos ("Not enough arguments to " ++ show var) enull]
    _ -> return (False, Just $ TermInCtx (Snoc Nil var $ Type ty lvl) $ Var Bound, PatternVar var)
  where
    isDataType :: Scope a (Term Syntax) b -> Bool
    isDataType (ScopeTerm ty) = case collect ty of
        (Just DataType{}, _) -> True
        _                    -> False
    isDataType (Scope _ t) = isDataType t
typeCheckPattern ctx (Type ty _) (Pattern (PatternCon _ _ (PIdent pos conName) _) pats)
  | (Just (DataType dt _), params) <- collect ty = do
    cons <- lift $ getConstructor conName (Just dt)
    case cons of
        []        -> throwError [notInScope pos "data constructor" conName]
        (n,con,(conType,lvl)):_ -> do
            let Apply (Con i _ conds) _ = instantiate params $ fmap (liftBase ctx) con
                conType' = Type (nf WHNF $ instantiate params $ fmap (liftBase ctx) conType) lvl
            (bf, TermsInCtx ctx' terms (Type ty _), rtpats) <- typeCheckPatterns ctx conType' pats
            let res = TermInCtx ctx' $ capps (Con i (PIdent pos conName) conds) terms
            case collect (nf WHNF ty) of
                (Just DataType{}, _) -> return (bf, Just res, Pattern (PatternCon i n conName conds) rtpats)
                _                    -> throwError [emsgLC pos "Not enough arguments" enull]
typeCheckPattern ctx (Type ty _) pat =
    throwError [emsgLC (patternGetAttr getPos pat) "" $ pretty "Unexpected pattern"
                                                     $$ pretty "Expected type:" <+> prettyOpen ctx ty]

typeCheckPatterns :: (Monad m, Eq a) => Ctx String (Type Syntax) Void a -> Type Syntax a
    -> [PatternP PIdent] -> TCM m (Bool, TermsInCtx a, [PatternC String])
typeCheckPatterns _ ty [] = return (False, TermsInCtx Nil [] ty, [])
typeCheckPatterns ctx (Type (Apply p@(Pi vs l1 l2) [a, b]) _) (pat:pats) = do
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
