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
        case lookup fn $ zipWith (\(fn,fty) fv -> (fn,(fv,fty))) fields' (ctxToVars ctx1) of
            Just (fieldVar, fieldType) -> do
                (bf, TermsInCtx ctx2 rtpats _ exprType) <- typeCheckPatterns ctx' fieldType pats
                when bf $ warn [Error Other $ emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                let ctx'' = ctx' C.+++ ctx2
                (term, _) <- typeCheckCtx ctx'' expr $ Just (nfType WHNF exprType)
                throwErrors $ checkTermination (Variable $ liftBase ctx2 fieldVar) pos (patternsToTerms rtpats) ctx'' term
                return $ Just (fn, (pos, P.Clause rtpats term))
            Nothing -> do
                warn [notInScope pos "record field" (nameToString fn)]
                return Nothing
    let clauseToSEval (_,(_,c)) = (fst $ clauseToEval c, closed $ abstractTerm ctx' $ snd $ clauseToEval c)
        getSConds (fn,_) = map clauseToSEval $ filter (\(fn',_) -> fn == fn') conds'
        getConds (fn,_) = map (\(_,(_,c)) -> closed $ abstractClause ctx' c) $ filter (\(fn',_) -> fn == fn') conds'
    case mcon of
        Just con -> addConstructorCheck con (recID, recName) 0 [] (if null conds' then [] else map getConds fields') $
            Closed $ Type (vacuous $ abstractTerm ctx $ replaceSort conType conSort Nothing) conSort
        _ -> return ()
    let varl = lengthCtx ctx'
        sem field = Semantics (S.Conds varl) $ V.Conds varl (getSConds field)
        vars = map (return . liftBase ctx1) (ctxToVars ctx) ++ map snd fields''
        fields'' = zipWith (\field@(fn,_) v -> (fn, Apply (sem field) $ return v : vars)) fields' (ctxToVars ctx1)
    forM_ fields'' $ \(fn, field) -> warn $ checkConditions ctx' field $ map snd $ filter (\(fn',_) -> fn == fn') conds'

data Fields b = forall a. Eq a => Fields (Ctx String (Type Semantics) b a) [(Name, Type Semantics a)]

typeCheckFields :: (Monad m, Eq a) => Ctx String (Type Semantics) Void a
    -> [Field] -> Type Semantics a -> TCM m (Fields a, Type Semantics a)
typeCheckFields _ [] ty = return (Fields C.Nil [], ty)
typeCheckFields ctx (Field (PIdent _ v) expr : exprs) ty = do
    (term, Type t1 _) <- typeCheckCtx ctx expr Nothing
    k1 <- checkIsType ctx (termPos expr) (nf WHNF t1)
    (Fields ctx' terms, Type ty' k2) <- typeCheckFields (Snoc ctx v $ Type term k1) exprs (fmap Free ty)
    let ctx'' = Snoc C.Nil v (Type term k1) C.+++ ctx'
    return (Fields ctx'' $ (Ident v, fmap (liftBase ctx'') $ Type term k1) : terms,
        Type (Apply (Semantics (S.Pi Explicit [v]) $ V.Pi k1 k2) [term, Lambda ty']) $ dmax k1 k2)

abstractClause :: Ctx s f b a -> P.Clause a -> P.Clause b
abstractClause C.Nil c = c
abstractClause (Snoc ctx _ _) c = abstractClause ctx (abstractClause1 c)
