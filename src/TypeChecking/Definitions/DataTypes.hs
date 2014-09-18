{-# LANGUAGE GADTs #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Data.List

import Syntax as S
import Semantics
import Semantics.Value as V
import Semantics.Pattern as P
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context as C
import TypeChecking.Expressions
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Patterns
import TypeChecking.Expressions.Conditions
import TypeChecking.Expressions.Telescopes
import TypeChecking.Definitions.Termination
import Normalization

typeCheckDataType :: Monad m => PName -> [Tele] -> [S.Con] -> [S.Clause] -> TCM m ()
typeCheckDataType p@(_, dt) params cons conds = do
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- typeCheckTelescope C.Nil params $ Type (universe Prop) (Set NoLevel)
    dtID <- addDataTypeCheck p lcons (closed dataType)
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(pos, conName) tele, i) -> do
        (_, conType) <- typeCheckTelescope ctx tele $
            Type (Apply (Semantics (Name Prefix dt) $ DataType dtID lcons) $ map return $ ctxToVars ctx) Prop
        case findOccurrence dtID (nf WHNF $ getType conType) of
            Just n | n > 1 -> throwError [Error Other $ emsgLC pos "Data type is not strictly positive" enull]
            _ -> return ()
        return $ Just (con, i, conType)
    let ks = map (\(_, _, Type _ k) -> k) cons'
        mk = dmaximum $ (if lcons > 1 then Set NoLevel else Prop) : ks
    forM_ cons' $ \(con, i, Type ty k) -> addConstructorCheck con (dtID, dt) i [] [] $
        closed $ Type (abstractTerm ctx $ replaceSort ty mk Nothing) mk
    conds' <- forW conds $ \(S.Clause (pos, con) pats expr) ->
        case find (\((_, c), _, _) -> c == con) cons' of
            Just ((_, conName), i, ty) -> do
                (bf, TermsInCtx ctx1 rtpats _ ty') <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [Error Other $ emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                let ctx' = ctx C.+++ ctx1
                (term, _) <- typeCheckCtx ctx' expr $ Just (nfType WHNF ty')
                throwErrors $ checkTermination (Constructor i) pos (patternsToTerms rtpats) ctx' term
                return $ Just (conName, (pos, P.Clause rtpats term))
            _ -> do
                warn [notInScope pos "data constructor" (nameToString con)]
                return Nothing
    lift $ replaceDataType dt lcons $ closed $ Type (replaceSort dtTerm (succ mk) $ Just mk) mk
    let cons'' = map (\((_, con), i, ty) ->
            let conds2 = map snd $ filter (\(c,_) -> c == con) conds'
                conds3 = map (\(_,c) -> closed $ abstractClause ctx c) conds2
            in (con, i, ty, conds2, conds3)) cons'
    forM_ cons'' $ \(con, i, Type ty k, _, conds3) ->
        lift $ replaceConstructor con (dtID, dt) i conds3 [] $ closed $ Type (abstractTerm ctx $ replaceSort ty mk Nothing) mk
    forM_ cons'' $ \(con, i, _, conds2, conds3) ->
        let toEval (Closed c) = (fst $ clauseToEval c, Closed $ snd $ clauseToEval c)
            vars = map return (ctxToVars ctx)
            conTerm = Apply (Semantics (Name Prefix con) $ DCon i (length vars) $ map toEval conds3) vars
        in warn $ checkConditions ctx conTerm conds2

abstractClause :: Ctx s f b a -> P.Clause a -> P.Clause b
abstractClause C.Nil c = c
abstractClause (Snoc ctx _ _) c = abstractClause ctx (abstractClause1 c)
