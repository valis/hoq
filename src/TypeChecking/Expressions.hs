module TypeChecking.Expressions
    ( typeCheck, typeCheckCtx
    ) where

import Control.Monad
import Data.Either
import Data.Maybe
import Data.Void
import Data.Bifunctor
import Data.Bitraversable
import Data.Traversable(sequenceA)

import Syntax as S
import Semantics
import Semantics.Value as V
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Patterns
import TypeChecking.Expressions.Conditions
import TypeChecking.Expressions.Coverage
import Normalization

type Context = Ctx String (Type Semantics) Void

intType :: Type Semantics a
intType = Type interval (TypeK NoLevel)

pathExp :: Sort -> Semantics
pathExp k = Semantics (Name Prefix $ Ident "Path") (Path k)

pathImp :: Sort -> Semantics
pathImp k = Semantics PathImp (Path k)

sortPred :: Sort -> Sort
sortPred Prop = Contr
sortPred Set{} = Prop
sortPred k = k

prettyOpen' :: Ctx String (Type Semantics) Void a -> Term Semantics (Either k a) -> EDoc (Term Syntax)
prettyOpen' ctx term = epretty $ fmap (pretty . either id absurd) $ close ctx $
    first syntax term >>= fmap Right . either (const $ capply $ Name Prefix $ Ident "_") return

typeCheck :: Monad m => Term (Posn, Syntax) Void -> Maybe (Type Semantics Void) -> TCM m (Term Semantics Void, Type Semantics Void)
typeCheck = typeCheckCtx Nil

typeCheckCtx :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void
    -> Maybe (Type Semantics a) -> TCM m (Term Semantics a, Type Semantics a)
typeCheckCtx ctx term mty = do
    (te, ty, _) <- typeCheckCtx' ctx term $ fmap (\(Type t k) -> Type (fmap Right t) k) mty
    return (te, ty)

typeCheckCtx' :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void -> Maybe (Type Semantics (Either Argument a))
    -> TCM m (Term Semantics a, Type Semantics a, [(Argument, Term Semantics a)])
typeCheckCtx' ctx (Apply (pos, Name ft var) ts) mty = typeCheckName ctx pos ft var ts mty
typeCheckCtx' ctx (Apply (_, S.Lam []) [te]) mty = typeCheckCtx' ctx te mty
typeCheckCtx' ctx (Apply (pos, S.Lam (v:vs)) [te]) (Just (Type (Apply p@(Semantics (S.Pi e _) (V.Pi k1 k2)) [a,b]) k3)) =
    case bitraverse Right id a of
        Left{} -> throwError [inferErrorMsg pos "the argument"]
        Right a' -> do
            (te', Type b' k2', tab) <- typeCheckCtx' (Snoc ctx v $ Type a' k1) (Apply (pos, S.Lam vs) [te]) $
                Just $ Type (nf WHNF $ fmap sequenceA $ snd $ dropOnePi p a b) k2
            let te'' = case te' of
                    Apply (Semantics (S.Lam vs') _) [t] -> Apply (Semantics (S.Lam $ v:vs') V.Lam) [Lambda t]
                    _                                   -> Apply (Semantics (S.Lam [v]) V.Lam) [Lambda te']
                tab' = tab >>= \(kp, term) -> case sequenceA term of
                                                    Bound -> []
                                                    Free t -> [(kp, t)]
            return (te'', Type (Apply (Semantics (S.Pi e [v]) $ V.Pi k1 k2') [a', Lambda b']) k3, tab')
typeCheckCtx' ctx (Apply (pos, S.Lam{}) [_]) (Just (Type (Var Left{} _) _)) =
    throwError [inferErrorMsg pos "lambda expressions"]
typeCheckCtx' ctx (Apply (pos, S.Lam{}) [_]) (Just (Type ty _)) =
    throwError [Error TypeMismatch $ emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen' ctx ty
                                                  $$ pretty "But lambda expression has pi type"]
typeCheckCtx' ctx (Apply (pos, S.Lam{}) _) _ = throwError [inferErrorMsg pos "the argument"]
typeCheckCtx' ctx (Apply (pos, S.Pi e vs) (a:b:ts)) Nothing = do
    (a', Type ty1 _) <- typeCheckCtx ctx a Nothing
    k1 <- checkIsType ctx (termPos a) ty1
    (b', k2) <- extend ctx vs (Type a' k1)
    unless (null ts) $ warn [argsErrorMsg pos "A type"]
    let k = case (k1, k2) of
                (_, Contr) -> Contr
                (_, Prop) -> Prop
                (Set l1, Set l2) -> Set (max l1 l2)
                (TypeK l1, Set l2) -> Set (max l1 l2)
                (_, Set l) -> Set l
                (Set l1, TypeK l2) -> TypeK (max l1 l2)
                (TypeK l1, TypeK l2) -> TypeK (max l1 l2)
                (_, TypeK l) -> TypeK l
    return (Apply (Semantics (S.Pi e vs) (V.Pi k1 k2)) [a', b'], Type (universe k) $ succ k, [])
  where
    extend :: (Monad m, Eq a) => Context a -> [String] -> Type Semantics a -> TCM m (Term Semantics a, Sort)
    extend ctx [] _ = do
        (te, Type ty _) <- typeCheckCtx ctx b Nothing
        k <- checkIsType ctx (termPos b) ty
        return (te, k)
    extend ctx (v:vs) a = do
        (te, k) <- extend (Snoc ctx v a) vs (fmap Free a)
        return (Lambda te, k)
typeCheckCtx' ctx (Apply (pos, PathImp) (a1:a2:ts)) Nothing = do
    unless (null ts) $ warn [argsErrorMsg pos "A type"]
    (r1, Type t1 k) <- typeCheckCtx ctx a1 Nothing
    (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF t1) k
    return (Apply (Semantics PathImp (Path k)) [Apply (Semantics (S.Lam ["_"]) V.Lam)
            [Lambda $ fmap Free t1], r1, r2], Type (universe $ sortPred k) $ succ $ sortPred k, [])
typeCheckCtx' ctx (Apply (pos, S.At) (b:c:ts)) mty = do
    (r1, Type t1 k) <- typeCheckCtx ctx b Nothing
    (r2, _) <- typeCheckCtx ctx c (Just intType)
    case nf WHNF t1 of
        Apply (Semantics _ Path{}) [a,b',c'] -> do
            (tes, ty, tab) <- typeCheckApps pos (Just $ Operator "@") ctx (map Left ts) (Type (apps a [r2]) k) mty
            return (Apply (Semantics S.At V.At) (b':c':r1:r2:tes), ty, tab)
        t1' -> throwError [Error TypeMismatch $ emsgLC pos "" $ pretty "Expected type: Path"
                                                             $$ pretty "Actual type:" <+> prettyOpen ctx t1']
typeCheckCtx' ctx (Apply (pos, (S.Case (pat:pats))) (expr:terms)) mty = do
    (exprTerm, exprType) <- typeCheckCtx ctx expr Nothing
    let (term1:terms1,terms2) = splitAt (length pats + 1) terms
        typeCheckClause mtype (pat,term) = do
            (bf, mt, pat') <- typeCheckPattern ctx exprType pat
            when bf $ warn [Error Other $ emsgLC (termPos pat) "Absurd patterns are not allowed in case constructions" enull]
            case fromMaybe (TermInCtx (Snoc Nil "_" exprType) $ error "") mt of
                TermInCtx ctx' _ -> do
                    (te, Type ty k, tab) <- typeCheckCtx' (ctx +++ ctx') term $ fmap (fmap $ fmap $ liftBase ctx') mtype
                    let tab' = tab >>= \(kp, t) -> case sequenceA $ fmap (toBase ctx') t of
                                                    Nothing -> []
                                                    Just t' -> [(kp, t')]
                    return (pat', abstractTerm ctx' te, Type (abstractTerm ctx' ty) k, tab')
    (pat', term1', Type type1 k, tab1) <- typeCheckClause (if null terms2 then mty else Nothing) (pat,term1)
    type1' <- case isStationary type1 of
                Nothing -> throwError [Error Other $
                    emsgLC pos "Type of expressions in case constructions cannot be dependent" enull]
                Just r  -> return (Type r k)
    patsAndTerms <- mapM (liftM (\(p,t,_,_) -> (p,t)) . typeCheckClause (Just $ nfType WHNF $ fmap Right type1')) (zip pats terms1)
    (terms2', ty, tab2) <- if null terms2
        then return ([], type1', [])
        else typeCheckApps pos Nothing ctx (map Left terms2) type1' mty
    let (pats',terms1') = unzip patsAndTerms
        sem = Semantics (S.Case $ map (first $ \(s,_) -> ((0,0), Ident s)) $ pat':pats') $ V.Case (pat':pats')
        terms' = term1' : terms1' ++ terms2'
    warn $ coverageErrorMsg pos $ checkCoverage $ zipWith (\p1 p2 -> (termPos p1, [first snd p2])) (pat:pats) (pat':pats')
    warn $ checkConditions pos ctx (Lambda $ Apply sem $ bvar : map (fmap Free) terms') $
        map (\(p,t) -> ([p],t)) $ (pat',term1'):patsAndTerms
    return (Apply sem $ exprTerm:terms', ty, tab1 ++ tab2)
  where
    isStationary :: Term a b -> Maybe (Term a b)
    isStationary (Lambda t) = case sequenceA t of
        Bound -> Nothing
        Free t' -> isStationary t'
    isStationary t = Just t
typeCheckCtx' ctx te (Just (Type ty _)) = do
    (te', Type ty' k') <- typeCheckCtx ctx te Nothing
    tab <- cmpTypes ActExp ctx ty' ty (termPos te)
    return (te', Type ty' k', tab)
typeCheckCtx' _ _ _ = error "typeCheckCtx"

typeCheckName :: (Monad m, Eq a) => Context a -> Posn -> Fixity -> Name -> [Term (Posn, Syntax) Void]
    -> Maybe (Type Semantics (Either Argument a)) -> TCM m (Term Semantics a, Type Semantics a, [(Argument, Term Semantics a)])
typeCheckName ctx pos ft var ts mty = do
    when (nameToString var == "_") $ throwError [inferExprErrorMsg pos]
    eres <- case lookupCtx (nameToString var) ctx of
        Just r -> return (Left r)
        Nothing -> do
            let mdt = case mty of
                        Just (Type (Apply (Semantics _ (DataType dti _)) params) _) -> Just (dti,params)
                        _ -> Nothing
            mt <- lift $ getEntry var mdt
            case mt of
                [] -> liftM Right (typeCheckKeyword ctx pos (nameToString var) ts mty)
                [(s, ty)] ->
                    let s' = case syntax s of
                                Name ft' _ | ft == ft'  -> s
                                _                       -> s { syntax = Name ft var }
                    in case sequenceA ty of
                        Left kp -> throwError (inferArgErrorMsg kp)
                        Right ty' -> return $ Left (capply s', ty')
                _ -> throwError [Error Other $ emsgLC pos ("Ambiguous identifier: " ++ show (nameToString var)) enull]
    case eres of
        Left (te, ty) -> do
            (tes, ty', tab) <- typeCheckApps pos (Just var) ctx (map Left ts) ty mty
            return (apps te tes, ty', tab)
        Right res -> return res

typeCheckKeyword :: (Monad m, Eq a) => Context a -> Posn -> String -> [Term (Posn, Syntax) Void]
    -> Maybe (Type Semantics (Either Argument a)) -> TCM m (Term Semantics a, Type Semantics a, [(Argument, Term Semantics a)])
typeCheckKeyword _ pos u as Nothing | (k,""):_ <- reads u = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (universe k, Type (universe $ succ k) $ succ $ succ k, [])
typeCheckKeyword ctx pos "contr" [] (Just (Type ty k)) = do
    case k of
        Contr   -> return ()
        _       -> warn [Error TypeMismatch $ emsgLC pos "" $ pretty "Expected a contractible type"
                                                           $$ pretty "Actual type:" <+> prettyOpen' ctx ty]
    case sequenceA ty of
        Left kp -> throwError (inferArgErrorMsg kp)
        Right ty' -> return (capply $ Semantics (Name Prefix $ Ident "contr") CCon, Type ty' k, [])
typeCheckKeyword _ pos "contr" _ _ = throwError [inferErrorMsg pos "contr"]
typeCheckKeyword _ pos "I" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos "A type"]
    return (interval, Type (universe $ TypeK NoLevel) $ TypeK $ Level 1, [])
typeCheckKeyword _ pos "left" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "left"]
    return (iCon ILeft, intType, [])
typeCheckKeyword _ pos "right" as Nothing = do
    unless (null as) $ warn [argsErrorMsg pos $ show "right"]
    return (iCon IRight, intType, [])
typeCheckKeyword _ pos "Path" [] _ = throwError [expectedArgErrorMsg pos "Path"]
typeCheckKeyword ctx pos "Path" (a:as) Nothing = do
    (r1, _, (v, t1)) <- typeCheckLambda ctx a intType
    k <- checkIsType (Snoc ctx v $ error "") (termPos a) t1
    let r1' c = apps r1 [iCon c]
        k' = sortPred k
        mkType t = Type t (succ k')
    case as of
        [] -> return (Apply (pathExp k) [r1], mkType $ Apply (Semantics (S.Pi Explicit []) $ V.Pi k $ succ k)
            [r1' ILeft, Apply (Semantics (S.Pi Explicit []) $ V.Pi k $ succ k) [r1' IRight, universe k']], [])
        [a2] -> do
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF $ r1' ILeft) k
            return (Apply (pathExp k) [r1,r2], mkType $ Apply (Semantics (S.Pi Explicit []) $ V.Pi k $ succ k) [r1' IRight, universe k'], [])
        a2:a3:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r2, _) <- typeCheckCtx ctx a2 $ Just $ Type (nf WHNF $ r1' ILeft) k
            (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ r1' IRight) k
            return (Apply (pathExp k) [r1,r2,r3], mkType $ universe k', [])
typeCheckKeyword _ pos "path" [] _ = throwError [expectedArgErrorMsg pos "path"]
typeCheckKeyword ctx pos "path" (a:as) mty = do
    unless (null as) $ warn [argsErrorMsg pos "A path"]
    case mty of
        Nothing -> do
            (te, Type ty k, _) <- typeCheckLambda ctx a intType
            return (te, Type (Apply (pathImp k) [ty, apps te [iCon ILeft], apps te [iCon IRight]]) k, [])
        Just (Type (Var (Left kp) _) _) -> do
            (te, Type ty k, _) <- typeCheckLambda ctx a intType
            let ty = Apply (pathImp k) [ty, apps te [iCon ILeft], apps te [iCon IRight]]
            return (te, Type ty k, [(kp,ty)])
        Just (Type ety@(Apply (Semantics _ (Path k1)) [t1,_,_]) k) -> do
            let sem = Semantics (S.Pi Explicit ["i"]) $ V.Pi (TypeK NoLevel) k1
                aty = Apply sem [interval, Lambda $ apps (fmap Free t1) [bvar]]
            (r, Type ty' _, tab1) <- typeCheckCtx' ctx a $ Just (Type aty k1)
            case nf WHNF ty' of
                Apply (Semantics (S.Pi e vs) p) [ta, tb] -> do
                    let tb' = case tb of
                                Lambda t@Lambda{} -> Apply (Semantics (S.Lam ["i"]) V.Lam)
                                    [Lambda $ Apply (Semantics (S.Pi e $ tail vs) p) [fmap Free ta, t]]
                                Lambda{} -> Apply (Semantics (S.Lam ["i"]) V.Lam) [tb]
                                _ -> Apply (Semantics (S.Lam ["_"]) V.Lam) [Lambda $ fmap Free tb]
                        aty = Apply (pathImp k1) [tb', apps r [iCon ILeft], apps r [iCon IRight]]
                    tab2 <- cmpTypes ActExp ctx aty ety pos
                    return (path [r], Type aty k, tab1 ++ tab2)
                _ -> error "typeCheckKeyword: path"
        Just (Type ty _) -> throwError [Error TypeMismatch $ emsgLC pos "" $ pretty "Expected type:" <+> prettyOpen' ctx ty
                                                                          $$ pretty "Actual type: Path"]
typeCheckKeyword _ pos "coe" [] _ = throwError [expectedArgErrorMsg pos "coe"]
typeCheckKeyword ctx pos "coe" (a1:as) Nothing = do
    (r1, _, (v, t1)) <- typeCheckLambda ctx a1 intType
    k <- checkIsType (Snoc ctx v $ error "") (termPos a1) t1
    let res = Apply (Semantics (S.Pi Explicit ["r"]) $ V.Pi (TypeK NoLevel) k) [interval, Lambda $ apps (fmap Free r1) [bvar]]
        coe = Semantics (Name Prefix $ Ident "coe") Coe
    case as of
        [] -> return (Apply coe [r1], Type (Apply (Semantics (S.Pi Explicit ["l"]) $ V.Pi (TypeK NoLevel) k) [interval, Lambda $
            Apply (Semantics (S.Pi Explicit []) $ V.Pi k k) [apps (fmap Free r1) [bvar], fmap Free res]]) k, [])
        a2:as1 -> do
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            case as1 of
                [] -> return (Apply coe [r1,r2], Type (Apply (Semantics (S.Pi Explicit []) $ V.Pi k k) [apps r1 [r2], res]) k, [])
                a3:as2 -> do
                    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (nf WHNF $ apps r1 [r2]) k
                    case as2 of
                        [] -> return (Apply coe [r1,r2,r3], Type res k, [])
                        a4:as3 -> do
                            (r4, _) <- typeCheckCtx ctx a4 (Just intType)
                            (tes, ty, _) <- typeCheckApps pos Nothing ctx (map Left as3) (Type (apps r1 [r4]) k) Nothing
                            return (Apply coe $ [r1,r2,r3,r4] ++ tes, ty, [])
typeCheckKeyword ctx pos "iso" (a1:a2:a3:a4:a5:a6:as) Nothing = do
    (r1, Type t1 _) <- typeCheckCtx ctx a1 Nothing
    (r2, Type t2 _) <- typeCheckCtx ctx a2 Nothing
    let t1' = nf WHNF t1
        t2' = nf WHNF t2
    k1 <- checkIsType ctx (termPos a1) t1'
    k2 <- checkIsType ctx (termPos a2) t2'
    let k = dmax k1 k2
    (r3, _) <- typeCheckCtx ctx a3 $ Just $ Type (Apply (Semantics (S.Pi Explicit []) $ V.Pi k1 k2) [r1,r2]) k
    (r4, _) <- typeCheckCtx ctx a4 $ Just $ Type (Apply (Semantics (S.Pi Explicit []) $ V.Pi k2 k1) [r2,r1]) k
    let h e s1 s3 s4 tk = typeCheckCtx ctx e $ Just $ Type (Apply (Semantics (S.Pi Explicit ["x"]) $ V.Pi tk tk) [s1, Lambda $
            Apply (pathImp tk) [Apply (Semantics (S.Lam ["_"]) V.Lam) [Lambda $ fmap (Free . Free) s1],
                apps (fmap Free s4) [apps (fmap Free s3) [bvar]], bvar]]) tk
        iso = Semantics (Name Prefix $ Ident "iso") Iso
    (r5, _) <- h a5 r1 r3 r4 k1
    (r6, _) <- h a6 r2 r4 r3 k2
    case as of
        [] -> return (Apply iso [r1,r2,r3,r4,r5,r6],
            Type (Apply (Semantics (S.Pi Explicit []) $ V.Pi (TypeK NoLevel) $ succ k) [interval, universe k]) $ succ k, [])
        a7:as' -> do
            unless (null as') $ warn [argsErrorMsg pos "A type"]
            (r7, _) <- typeCheckCtx ctx a7 (Just intType)
            return (Apply iso [r1,r2,r3,r4,r5,r6,r7], Type (universe k) $ succ k, [])
typeCheckKeyword _ pos "iso" _ Nothing =
    throwError [Error NotEnoughArgs $ emsgLC pos "Expected at least 6 arguments to \"iso\"" enull]
typeCheckKeyword ctx pos "squeeze" as Nothing =
    let mkType t = Apply (Semantics (S.Pi Explicit []) $ V.Pi (TypeK NoLevel) $ TypeK NoLevel) [interval, t]
        squeeze = Semantics (Name Prefix $ Ident "squeeze") Squeeze
    in case as of
        [] -> return (capply squeeze, Type (mkType $ mkType interval) $ TypeK NoLevel, [])
        [a1] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            return (Apply squeeze [r1], Type (mkType interval) $ TypeK NoLevel, [])
        [a1,a2] -> do
            (r1, _) <- typeCheckCtx ctx a1 (Just intType)
            (r2, _) <- typeCheckCtx ctx a2 (Just intType)
            return (Apply squeeze [r1,r2], intType, [])
        _ -> throwError [argsErrorMsg pos "squeeze _ _"]
typeCheckKeyword ctx pos var ts (Just (Type ty _)) = do
    (te', Type ty' k', _) <- typeCheckKeyword ctx pos var ts Nothing
    tab <- cmpTypes ActExp ctx ty' ty pos
    return (te', Type ty' k', tab)
typeCheckKeyword _ pos var _ _ = throwError [notInScope pos "" var]

data CmpTypes = ActExp | ExpAct deriving Eq

cmpTypes :: (Monad m, Eq a) => CmpTypes -> Context a -> Term Semantics a -> Term Semantics (Either Argument a) -> Posn
    -> EDocM m [(Argument, Term Semantics a)]
cmpTypes d ctx t1 t2 pos = do
    let t1' = nf NF t1
        t2' = nf NF t2
        (act,exp) = if d == ActExp
            then (prettyOpen  ctx t1', prettyOpen' ctx t2')
            else (prettyOpen' ctx t2', prettyOpen  ctx t1')
        (mo,l) = pcmpTerms t1' t2'
        l' = rights $ map (\(k,mt) -> maybe (Left k) (\t -> Right (k,t)) mt) l
    unless (useful l' || mo == Just EQ || mo == Just (if d == ActExp then LT else GT)) $
        warn [Error TypeMismatch $ emsgLC pos "" $ pretty "Expected type:" <+> exp
                                                $$ pretty "Actual type:"   <+> act]
    return l'

typeCheckApps :: (Monad m, Eq a) => Posn -> Maybe Name -> Context a -> [Either (Term (Posn, Syntax) Void) (Term Semantics a)]
    -> Type Semantics a -> Maybe (Type Semantics (Either Argument a))
    -> TCM m ([Term Semantics a], Type Semantics a, [(Argument, Term Semantics a)])
typeCheckApps pos mname ctx allTerms ty mety = go 0 [] [] (map (\t -> (Explicit, t)) allTerms) nty
  where
    nty = nfType WHNF (fmap Right ty)
    mety' = fmap (\(Type t _) -> either (const $ Left t) Right $ sequenceA t) mety
    
    go n acc rest ((e1, term@(Left (Apply (pos', Name _ (Ident "_")) []))) : terms) (Type (Apply p@(Semantics (S.Pi e2 _) (V.Pi _ k2)) [a,b]) _) | e1 == e2 =
        go (n + 1) (Left (inferArgErrorMsg $ Argument n pos' mname) : acc) ((e1,term):rest) terms $
        Type (nf WHNF $ instantiate1 (cvar $ Left (Argument n pos' mname)) $ snd $ dropOnePi p a b) k2
    go n acc rest ((e1,term):terms) (Type (Apply p@(Semantics (S.Pi e2 _) (V.Pi k1 k2)) [a,b]) _) | e1 == e2 = do
        mres <- case term of
                    Left t -> let catchErrs = catchErrorType [Inference,TypeMismatch]
                              in liftM (\(a,_,c) -> Right (a,c)) (typeCheckCtx' ctx t $ Just $ Type (nf WHNF a) k1)
                                    `catchErrs` (return . Left)
                    Right t -> return $ Right (t, [])
        case mres of
            Left errs -> go (n + 1) (Left errs : acc) ((e1,term):rest) terms $
                Type (nf WHNF $ instantiate1 (cvar $ Left $ NoArgument errs) $ snd $ dropOnePi p a b) k2
            Right (term', tab) ->
                if useful tab
                then go 0 [] [] (replaceTerms (reverse rest ++ [(e1, Right term')] ++ terms) tab) nty
                else go (n + 1) (Right term' : acc) ((e1, Right term') : rest) terms $ Type (nf WHNF $ case b of
                    Lambda{} -> instantiate1 (fmap Right term') $ snd (dropOnePi p a b)
                    _        -> b) k2
    go n acc rest terms (Type (Apply p@(Semantics (S.Pi Implicit _) (V.Pi _ k2)) [a,b]) _) =
        go (n + 1) (Left (inferArgErrorMsg $ Argument n pos mname) : acc)
            ((Implicit, Left (capply (pos, Name Prefix $ Ident "_"))) : rest) terms $
            Type (nf WHNF $ instantiate1 (cvar $ Left (Argument n pos mname)) $ snd $ dropOnePi p a b) k2
    go _ acc rest [] (Type aty k) =
        let checkAty = case sequenceA aty of
                        Left kp -> throwError (inferArgErrorMsg kp)
                        Right aty' -> do
                            acc' <- checkAcc
                            return (acc', Type aty' k, [])
            checkAcc = case partitionEithers (reverse acc) of
                        ([],rights) -> return rights
                        (left:_,_)  -> throwError left
        in case mety' of
            Just (Right ety) -> do
                tab <- cmpTypes ExpAct ctx ety aty pos
                if useful tab
                    then go 0 [] [] (replaceTerms (reverse rest) tab) nty
                    else checkAty
            Just (Left ety) -> do
                (_, Type aty' k', _) <- checkAty
                tab <- cmpTypes ActExp ctx aty' ety pos
                acc' <- checkAcc
                return (acc', Type aty' k', tab)
            Nothing -> checkAty
    go _ _ _ _ (Type (Var (Left kp) _) _) = throwError (inferArgErrorMsg kp)
    go _ _ _ _ (Type ty _) = throwError [Error TypeMismatch $ emsgLC pos "" $ pretty "Expected pi type"
                                                                           $$ pretty "Actual type:" <+> prettyOpen' ctx ty]
    
    replaceTerms :: [(e, Either t s)] -> [(Argument, s)] -> [(e, Either t s)]
    replaceTerms ts [] = ts
    replaceTerms ts ((Argument k _ _, t):tab) =
        let (ts1,ts2) = splitAt k (replaceTerms ts tab)
        in if null ts2 then ts1 else ts1 ++ [(fst $ head ts2, Right t)] ++ tail ts2
    replaceTerms ts ((NoArgument{},_):tab) = replaceTerms ts tab

useful :: [(Argument,a)] -> Bool
useful = not . null . filter (\(arg,_) -> case arg of
    Argument{}   -> True
    NoArgument{} -> False)

typeCheckLambda :: (Monad m, Eq a) => Context a -> Term (Posn, Syntax) Void -> Type Semantics a
    -> TCM m (Term Semantics a, Type Semantics a, (String, Term Semantics (Scoped a)))
typeCheckLambda ctx (Apply (pos, S.Lam (v:vs)) [te]) (Type ty k) = do
    (te', Type ty' k') <- typeCheckCtx (Snoc ctx v $ Type ty k) (if null vs then te else Apply (pos, S.Lam vs) [te]) Nothing
    let te'' = case te' of
                Apply (Semantics (S.Lam vs') _) [te''] -> Apply (Semantics (S.Lam $ v:vs') V.Lam) [Lambda te'']
                _ -> Apply (Semantics (S.Lam [v]) V.Lam) [Lambda te']
    return (te'', Type (Apply (Semantics (S.Pi Explicit [v]) (V.Pi k k')) [ty, Lambda ty']) $ dmax k k', (v, ty'))
typeCheckLambda ctx te ty = do
    (te', Type ty' k') <- typeCheckCtx ctx te Nothing
    case nf WHNF ty' of
        ty''@(Apply p@(Semantics sp (V.Pi ka kb)) [a,b]) ->
            let na = nf NF a
                Type nty kty = nfType NF ty
            in if (nty `lessOrEqual` na)
                then return (te', Type ty'' k', dropOnePi p a b)
                else throwError [Error TypeMismatch $ emsgLC (termPos te) "" $
                        pretty "Expected type:" <+> prettyOpen ctx (Apply (Semantics sp $ V.Pi kty kb) [nty,b]) $$
                        pretty "Actual type:"   <+> prettyOpen ctx (Apply p [na,b])]
        _ -> throwError [Error TypeMismatch $ emsgLC (termPos te) "" $ pretty "Expected pi type"
                                                                    $$ pretty "Actual type:" <+> prettyOpen ctx ty']
