module TypeChecking.Definitions.Patterns
    ( typeCheckPatterns
    ) where

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import Syntax.Context
import TypeChecking.Monad
import TypeChecking.Definitions.Coverage as C
import TypeChecking.Expressions
import Normalization

getCon :: Monad m => (Int,Int) -> Ctx Int [String] Term String a
    -> Either (Term String) (Term (Var Int String)) -> Term a -> EDocM m (Term a)
getCon _  ctx (Left con) _                                      = return $ fmap (liftBase ctx) con
getCon _  ctx (Right (T.Con i con [] [])) ty                    = return $ T.Con i con [] []
getCon _  ctx (Right con@(T.Con i _ _ _)) (DataType _ _ params) = return $ liftTermWithParams ctx params con
getCon lc ctx (Right (T.Con _ con _ _)) _                       = throwError [inferParamsErrorMsg lc con]
getCon _ _ _ _                                                  = error "getCon"

liftTermWithParams :: Ctx Int [String] Term String a -> [Term a] -> Term (Var Int String) -> Term a
liftTermWithParams ctx params term = term >>= \v -> case v of
    B i -> reverse params !! i
    F t -> return (liftBase ctx t)

typeCheckPattern :: (Monad m, Eq a, Show a) => Ctx Int [String] Term String a
    -> Term a -> ParPat -> TCM m (Bool, TermInCtx Int [String] Term a, T.Pattern, C.Pattern)
typeCheckPattern ctx T.Interval (ParLeft _)  = return (False, TermInCtx Nil $ ICon ILeft , T.PatternI ILeft , PatLeft)
typeCheckPattern ctx T.Interval (ParRight _) = return (False, TermInCtx Nil $ ICon IRight, T.PatternI IRight, PatRight)
typeCheckPattern ctx ty@(DataType _ 0 _) (ParEmpty _) =
    return (True, TermInCtx (Snoc Nil ["_"] ty) $ T.Var (B 0), T.PatternVar, PatVar)
typeCheckPattern ctx ty (ParEmpty (PPar (lc,_))) =
    throwError [emsgLC lc "" $ pretty "Expected non-empty type: " <+> prettyOpen ctx ty]
typeCheckPattern ctx ty (ParVar arg) = do
    let var = unArg arg
    cons <- lift $ getConstructor var $ case ty of
        DataType dt _ _ -> Just dt
        _               -> Nothing
    case cons of
        []        -> return (False, TermInCtx (Snoc Nil [var] ty) $ T.Var (B 0), T.PatternVar, PatVar)
        [(n,con)] -> do
            con'@(T.Con i _ _ _) <- getCon (argGetPos arg) ctx (either (Left . fst) (Right . fst) con) ty
            let ok = case con of
                        Left  (_,conType) -> case nf WHNF conType of
                            DataType{} -> True
                            _          -> False
                        Right (_,conType) -> case nf WHNF conType of
                            DataType{} -> True
                            _          -> False
            if ok then return (False, TermInCtx Nil con', T.Pattern i [], C.Pattern i n [])
                  else throwError [emsgLC (argGetPos arg) ("Not enough arguments to " ++ show var) enull]
        _ -> throwError [inferErrorMsg (argGetPos arg) $ "data constructor " ++ show var]
typeCheckPattern ctx dty@(DataType dt _ params) (ParPat _ (E.Pattern (PIdent (lc,conName)) pats)) = do
    cons <- lift $ getConstructor conName (Just dt)
    case cons of
        []        -> throwError [notInScope lc "data constructor" conName]
        (n,con):_ -> do
            T.Con i _ _ conds <- getCon lc ctx (either (Left . fst) (Right . fst) con) dty
            let conType = either (fmap (liftBase ctx) . snd) (liftTermWithParams ctx params . snd) con
            (bf, TermsInCtx ctx' terms ty, rtpats, cpats) <- typeCheckPatterns ctx conType pats
            case nf WHNF ty of
                DataType{} -> return (bf, TermInCtx ctx' $ T.Con i conName terms conds, T.Pattern i rtpats, C.Pattern i n cpats)
                _          -> throwError [emsgLC lc "Not enough arguments" enull]
typeCheckPattern ctx ty pat =
    throwError [emsgLC (parPatGetPos pat) "" $ pretty "Unexpected pattern" $$
                                               pretty "Expected type:" <+> prettyOpen ctx ty]

typeCheckPatterns :: (Monad m, Eq a, Show a) => Ctx Int [String] Term String a -> Term a -> [ParPat]
    -> TCM m (Bool, TermsInCtx Int [String] Term a, [T.Pattern], [C.Pattern])
typeCheckPatterns _ ty [] = return (False, TermsInCtx Nil [] ty, [], [])
typeCheckPatterns ctx (T.Arr a b) (pat:pats) = do
    (bf1, TermInCtx  ctx'  te,     rtpat , cpat)  <- typeCheckPattern ctx (nf WHNF a) pat
    (bf2, TermsInCtx ctx'' tes ty, rtpats, cpats) <- typeCheckPatterns (ctx +++ ctx') (nf WHNF $ fmap (liftBase ctx') b) pats
    return (bf1 || bf2, TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats, cpat:cpats)
typeCheckPatterns ctx (T.Pi fl a b) (pat:pats) = do
    (bf1, TermInCtx ctx' te, rtpat, cpat) <- typeCheckPattern ctx (nf WHNF a) pat
    let b' = either (T.Pi fl $ fmap (liftBase ctx') a) id $ instantiateNames1 te $ fmap (liftBase ctx') b
    (bf2, TermsInCtx ctx'' tes ty, rtpats, cpats) <- typeCheckPatterns (ctx +++ ctx') (nf WHNF b') pats
    return (bf1 || bf2, TermsInCtx (ctx' +++ ctx'') (fmap (liftBase ctx'') te : tes) ty, rtpat:rtpats, cpat:cpats)
typeCheckPatterns _ _ (pat:_) = throwError [emsgLC (parPatGetPos pat) "Too many arguments" enull]
