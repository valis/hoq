{-# LANGUAGE ExistentialQuantification, GADTs #-}

module TypeChecking.Definitions.Records
    ( typeCheckRecord
    ) where

import Data.Void
import Control.Monad

import Syntax as S
import Semantics
import Semantics.Value as V
import Semantics.Pattern as P
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context as C
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Patterns
import TypeChecking.Expressions.Telescopes
import TypeChecking.Expressions.Conditions
import TypeChecking.Expressions
import TypeChecking.Definitions.Termination
import Normalization

typeCheckRecord :: Monad m => PName -> [Tele] -> Maybe PName -> [Field] -> [S.Clause] -> TCM m ()
typeCheckRecord recPName@(recPos, recName) params mcon fields conds = do
    (SomeEq ctx, recType@(Type recTerm _)) <- typeCheckTelescope C.Nil params $ Type (universe Prop) (Set NoLevel)
    recID <- addDataTypeCheck recPName 1 $ Closed (vacuous recType)
    (Fields ctx1 fields', Type conType conSort) <- typeCheckFields ctx fields $
        Type (Apply (Semantics (Name Prefix recName) $ DataType recID 1) $ map return $ ctxToVars ctx) Prop
    let ctx' = ctx C.+++ ctx1
    forM_ fields' $ \(_, Type fieldType _) -> case findOccurrence recID (nf WHNF fieldType) of
        Just n | n > 0 -> throwError [Error Other $ emsgLC recPos "Record types cannot be recursive" enull]
        _ -> return ()
    conds' <- forW conds $ \(S.Clause (pos, fn) pats expr) ->
        case lookup fn $ zipWith (\((_,fn),fty) fv -> (fn,(fv,fty))) fields' (ctxToVars ctx1) of
            Just (fieldVar, fieldType) -> do
                (bf, TermsInCtx ctx2 rtpats _ exprType) <- typeCheckPatterns ctx' fieldType pats
                when bf $ warn [Error Other $ emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                let ctx'' = ctx' C.+++ ctx2
                (term, _) <- typeCheckCtx ctx'' expr $ Just (nfType WHNF exprType)
                return $ Just (fn, (pos, P.Clause rtpats term), PatInCtx (Variable $ liftBase ctx2 fieldVar) (patternsToTermsVar rtpats) term)
            Nothing -> do
                warn [notInScope pos "record field" (nameToString fn)]
                return Nothing
    termErrs <- liftM concat $ forM fields' $ \((_, fn), _) ->
        let tc = filter (\(fn',_,_) -> fn == fn') conds'
            (_,(pos,_),_) = head tc
            termErrs = checkTermination pos $ map (\(_,_,t) -> t) tc
        in warn termErrs >> return (if null termErrs then [] else [fn])
    let clauseToSEval (_,(_,c),_) = (fst $ clauseToEval c, closed $ abstractTerm ctx' $ snd $ clauseToEval c)
        getSConds ((_,fn),_) = if elem fn termErrs
            then []
            else map clauseToSEval $ filter (\(fn',_,_) -> fn == fn') conds'
        getConds ((_,fn),_) = if elem fn termErrs
            then []
            else map (\(_,(_,c),_) -> closed $ abstractClause ctx' c) $ filter (\(fn',_,_) -> fn == fn') conds'
    case mcon of
        Just con -> addConstructorCheck con (recID, recName) 0 [] (if null conds' then [] else map getConds fields') $
            Closed $ Type (vacuous $ abstractTerm ctx $ replaceSort conType conSort Nothing) conSort
        _ -> return ()
    let varl = lengthCtx ctx'
        sconds = map getSConds fields'
        vars = map (return . liftBase ctx1) (ctxToVars ctx) ++ map snd fields''
        fields'' = zipWith (\(field@((_,fn),_), c) v -> (fn, Apply (Semantics (S.Conds varl) $ V.Conds varl c) $ return v : vars)) (zip fields' sconds) (ctxToVars ctx1)
    forM_ fields'' $ \(fn, field) -> warn $ checkConditions ctx' field $ map (\(_,b,_) -> b) $ filter (\(fn',_,_) -> fn == fn') conds'
    forM_ (zip (zip fields' [0..]) sconds) $ \((((fp, fn), Type fty k), ind), cond) ->
        addFieldCheck (PIdent fp $ nameToPrefix fn) recID ind cond $ closed $ Type (abstractTerm ctx' fty) k

data Fields b = forall a. Eq a => Fields (Ctx String (Type Semantics) b a) [(PName, Type Semantics a)]

typeCheckFields :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a
    -> [Field] -> Type Semantics a -> TCM m (Fields a, Type Semantics a)
typeCheckFields _ [] ty = return (Fields C.Nil [], ty)
typeCheckFields ctx (Field (PIdent p v) expr : exprs) ty = do
    (term, Type t1 _) <- typeCheckCtx ctx expr Nothing
    k1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    (Fields ctx' terms, Type ty' k2) <- typeCheckFields (Snoc ctx v $ Type term k1) exprs (fmap Free ty)
    let ctx'' = Snoc C.Nil v (Type term k1) C.+++ ctx'
    return (Fields ctx'' $ ((p, Ident v), fmap (liftBase ctx'') $ Type term k1) : terms,
        Type (Apply (Semantics (S.Pi Explicit [v]) $ V.Pi k1 k2) [term, Lambda ty']) $ dmax k1 k2)

abstractClause :: Ctx s f b a -> P.Clause a -> P.Clause b
abstractClause C.Nil c = c
abstractClause (Snoc ctx _ _) c = abstractClause ctx (abstractClause1 c)
