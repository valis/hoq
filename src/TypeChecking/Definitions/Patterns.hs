{-# LANGUAGE ExistentialQuantification #-}

module TypeChecking.Definitions.Patterns
    ( typeCheckPatterns
    , TermsInCtx(..)
    ) where

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import TypeChecking.Context
import TypeChecking.Monad
import TypeChecking.Expressions
import Normalization

data TermInCtx b  = forall a. Eq a => TermInCtx  (Ctx String Type b a) (Term a)
data TermsInCtx b = forall a. Eq a => TermsInCtx (Ctx String Type b a) [Term a] (Type a)

typeCheckPattern :: (Monad m, Eq a) => Ctx String Type String a
    -> Type a -> ParPat -> TCM m (Bool, Maybe (TermInCtx a), T.Pattern (Closed (Scope String Term)))
typeCheckPattern ctx (Type T.Interval _) (ParLeft _)  = return (False, Just $ TermInCtx Nil $ ICon ILeft , PatternI ILeft)
typeCheckPattern ctx (Type T.Interval _) (ParRight _) = return (False, Just $ TermInCtx Nil $ ICon IRight, PatternI IRight)
typeCheckPattern ctx (Type (DataType _ 0 _) _) (ParEmpty _) = return (True, Nothing, PatternVar "_")
typeCheckPattern ctx (Type ty _) (ParEmpty (PPar (lc,_))) =
    throwError [emsgLC lc "" $ pretty "Expected non-empty type:" <+> prettyOpen ctx ty]
typeCheckPattern ctx _ (ParVar (NoArg _)) = return (False, Nothing, PatternVar "_")
typeCheckPattern ctx ty@(Type (DataType dt _ params) _) (ParVar (Arg (PIdent (lc,var)))) = do
    cons <- lift $ getConstructor var (Just dt)
    case cons of
        [] -> return (False, Just $ TermInCtx (Snoc Nil var ty) $ T.Var Bound, PatternVar var)
        (n,con,(conType,_)):_ -> if isDataType conType
            then let con'@(T.Con i _ conName conds _) = instantiate params $ fmap (liftBase ctx) con
                 in return (False, Just $ TermInCtx Nil con', T.Pattern (PatternCon i n conName conds) [])
            else throwError [emsgLC lc ("Not enough arguments to " ++ show var) enull]
  where
    isDataType :: Scope a Term b     -> Bool
    isDataType (ScopeTerm DataType{}) = True
    isDataType (ScopeTerm _)          = False
    isDataType (Scope _ t)            = isDataType t
typeCheckPattern ctx ty (ParVar (Arg (PIdent (lc,var)))) =
    return (False, Just $ TermInCtx (Snoc Nil var ty) $ T.Var Bound, PatternVar var)
typeCheckPattern ctx (Type (DataType dt _ params) _) (ParPat _ (E.Pattern (PIdent (lc,conName)) pats)) = do
    cons <- lift $ getConstructor conName (Just dt)
    case cons of
        []        -> throwError [notInScope lc "data constructor" conName]
        (n,con,(conType,lvl)):_ -> do
            let T.Con i _ _ conds _ = instantiate params $ fmap (liftBase ctx) con
                conType' = Type (nf WHNF $ instantiate params $ fmap (liftBase ctx) conType) lvl
            (bf, TermsInCtx ctx' terms (Type ty _), rtpats) <- typeCheckPatterns ctx conType' pats
            let res = TermInCtx ctx' (T.Con i lc conName conds terms)
            case nf WHNF ty of
                DataType{} -> return (bf, Just res, T.Pattern (PatternCon i n conName conds) rtpats)
                _          -> throwError [emsgLC lc "Not enough arguments" enull]
typeCheckPattern ctx (Type ty _) pat =
    throwError [emsgLC (parPatGetPos pat) "" $ pretty "Unexpected pattern" $$
                                               pretty "Expected type:" <+> prettyOpen ctx ty]

typeCheckPatterns :: (Monad m, Eq a) => Ctx String Type String a -> Type a -> [ParPat]
    -> TCM m (Bool, TermsInCtx a, [T.Pattern (Closed (Scope String Term))])
typeCheckPatterns _ ty [] = return (False, TermsInCtx Nil [] ty, [])
typeCheckPatterns ctx (Type (T.Pi a b lvl) _) (pat:pats) = do
    let a' = nfType WHNF a
    (bf1, mte, rtpat) <- typeCheckPattern ctx a' pat
    TermInCtx ctx' te <- case mte of
                            Nothing ->
                                let var = case b of
                                            Scope v _ -> v
                                            _         -> "_"
                                in return $ TermInCtx (Snoc Nil var a') (T.Var Bound)
                            Just te -> return te
    let b' = instantiate1 te $ fmap (fmap $ liftBase ctx') $ unScope1 (dropOnePi a b lvl)
    (bf2, TermsInCtx ctx'' tes ty, rtpats) <- typeCheckPatterns (ctx +++ ctx') (Type (nf WHNF b') lvl) pats
    return (bf1 || bf2, TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats)
typeCheckPatterns _ _ (pat:_) = throwError [emsgLC (parPatGetPos pat) "Too many arguments" enull]

getVariables :: ParPat                    -> [PIdent]
getVariables (ParPat _ (E.Pattern _ pats)) = pats >>= getVariables
getVariables (ParVar (Arg var))            = [var]
getVariables _                             = []
