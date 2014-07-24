{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Definitions.Patterns
    ( typeCheckPatterns
    , TermsInCtx(..)
    ) where

import Syntax.Term
import Syntax.ErrorDoc
import TypeChecking.Context
import TypeChecking.Monad
import TypeChecking.Expressions
import Normalization

data TermInCtx b  = forall a. Eq a => TermInCtx  (Ctx String () (Type ()) b a) (Term () a)
data TermsInCtx b = forall a. Eq a => TermsInCtx (Ctx String () (Type ()) b a) [Term () a] (Type () a)

typeCheckPattern :: (Monad m, Eq a) => Ctx String () (Type ()) PIdent a -> Type () a
    -> PatternC Posn PIdent -> TCM m (Bool, Maybe (TermInCtx a), PatternC () String)
typeCheckPattern _ _ PatternI{} = error "typeCheckPattern: PatternI"
typeCheckPattern ctx (Type Interval{} _) (PatternVar (PIdent _ "left")) =
    return (False, Just $ TermInCtx Nil $ ICon () ILeft, PatternI () ILeft)
typeCheckPattern ctx (Type Interval{} _) (PatternVar (PIdent _ "right")) =
    return (False, Just $ TermInCtx Nil $ ICon () IRight, PatternI () IRight)
typeCheckPattern ctx (Type (DataType _ _ 0 _) _) (PatternEmpty _) = return (True, Nothing, PatternVar "_")
typeCheckPattern ctx (Type ty _) (PatternEmpty pos) =
    throwError [emsgLC pos "" $ pretty "Expected non-empty type:" <+> prettyOpen ctx ty]
typeCheckPattern ctx _ (PatternVar (PIdent _ "_")) = return (False, Nothing, PatternVar "_")
typeCheckPattern ctx ty@(Type (DataType _ dt _ params) _) (PatternVar (PIdent pos var)) = do
    cons <- lift $ getConstructor var (Just dt)
    case cons of
        [] -> return (False, Just $ TermInCtx (Snoc Nil var ty) $ Var $ Bound (), PatternVar var)
        (n,con,(conType,_)):_ -> if isDataType conType
            then let con'@(Con _ i conName conds _) = instantiate params $ fmap (liftBase ctx) $ mapScope' (const ()) con
                 in return (False, Just $ TermInCtx Nil con', Pattern (PatternCon i n conName conds) [])
            else throwError [emsgLC pos ("Not enough arguments to " ++ show var) enull]
  where
    isDataType :: Scope a p (Term p) b -> Bool
    isDataType (ScopeTerm DataType{}) = True
    isDataType (ScopeTerm _)          = False
    isDataType (Scope _ t)            = isDataType t
typeCheckPattern ctx ty (PatternVar (PIdent _ var)) =
    return (False, Just $ TermInCtx (Snoc Nil var ty) $ Var $ Bound (), PatternVar var)
typeCheckPattern ctx (Type (DataType _ dt _ params) _) (Pattern (PatternCon _ _ (PIdent pos conName) _) pats) = do
    cons <- lift $ getConstructor conName (Just dt)
    case cons of
        []        -> throwError [notInScope pos "data constructor" conName]
        (n,con,(conType,lvl)):_ -> do
            let Con _ i _ conds _ = instantiate params $ fmap (liftBase ctx) $ mapScope' (const ()) con
                conType' = Type (nf WHNF $ instantiate params $ fmap (liftBase ctx) $ mapScope' (const ()) conType) lvl
            (bf, TermsInCtx ctx' terms (Type ty _), rtpats) <- typeCheckPatterns ctx conType' pats
            let res = TermInCtx ctx' (Con () i conName conds terms)
            case nf WHNF ty of
                DataType{} -> return (bf, Just res, Pattern (PatternCon i n conName conds) rtpats)
                _          -> throwError [emsgLC pos "Not enough arguments" enull]
typeCheckPattern ctx (Type ty _) pat =
    throwError [emsgLC (patternGetAttr getPos pat) "" $ pretty "Unexpected pattern"
                                                     $$ pretty "Expected type:" <+> prettyOpen ctx ty]

typeCheckPatterns :: (Monad m, Eq a) => Ctx String () (Type ()) PIdent a -> Type () a
    -> [PatternC Posn PIdent] -> TCM m (Bool, TermsInCtx a, [PatternC () String])
typeCheckPatterns _ ty [] = return (False, TermsInCtx Nil [] ty, [])
typeCheckPatterns ctx (Type (Pi p a b lvl) _) (pat:pats) = do
    let a' = nfType WHNF a
    (bf1, mte, rtpat) <- typeCheckPattern ctx a' pat
    TermInCtx ctx' te <- case mte of
                            Nothing ->
                                let var = case b of
                                            Scope v _ -> v
                                            _         -> "_"
                                in return $ TermInCtx (Snoc Nil var a') $ Var $ Bound ()
                            Just te -> return te
    let b' = instantiate1 te $ fmap (fmap $ liftBase ctx') $ unScope1 (dropOnePi p a b lvl)
    (bf2, TermsInCtx ctx'' tes ty, rtpats) <- typeCheckPatterns (ctx +++ ctx') (Type (nf WHNF b') lvl) pats
    return (bf1 || bf2, TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats)
typeCheckPatterns _ _ (pat:_) = throwError [emsgLC (patternGetAttr getPos pat) "Too many arguments" enull]
