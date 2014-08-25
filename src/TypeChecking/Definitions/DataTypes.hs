{-# LANGUAGE RecursiveDo #-}

module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.List
import Data.Bifunctor
import Data.Void

import Syntax as S
import Semantics
import Semantics.Value as V
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Patterns
import TypeChecking.Expressions.Conditions
import TypeChecking.Expressions.Telescopes
import TypeChecking.Definitions.Termination
import Normalization

typeCheckDataType :: MonadFix m => PName -> [Tele] -> [S.Con] -> [Clause] -> TCM m ()
typeCheckDataType p@(pos, dt) params cons conds = mdo
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- typeCheckTelescope Nil params $ Type (universe Prop) (Set NoLevel)
    dtid <- addDataTypeCheck p lcons $ Closed (vacuous dataType)
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(pos, conName) tele, i) -> do
        (_, Type conType conSort) <- typeCheckTelescope ctx tele $
            Type (Apply (Semantics (Name Prefix dt) $ DataType dtid lcons) $ ctxToVars ctx) Prop
        case findOccurrence dtid (nf WHNF conType) of
            Just n | n > 1 -> throwError [Error Other $ emsgLC pos "Data type is not strictly positive" enull]
            _ -> return ()
        let conds'' = map snd $ filter (\(c,_) -> c == conName) conds'
            conTerm = Semantics (Name Prefix conName) $ Con $ DCon i lcons (PatEval conds'')
        return $ Just (con, (i, conds'', conTerm), Type conType conSort)
    let ks = map (\(_, _, Type _ k) -> k) cons'
        mk = if null ks then Prop else dmaximum $ (if lcons > 1 then Set NoLevel else Prop) : ks
    forM_ cons' $ \(con, (i, cs, _), Type ty k) -> addConstructorCheck con dtid i lcons (PatEval cs) [] $
        Closed $ Type (vacuous $ abstractTerm ctx $ replaceSort ty mk Nothing) mk
    conds' <- forW conds $ \(Clause (pos, con) pats expr) ->
        case find (\((_, c), _, _) -> c == con) cons' of
            Just ((_, conName), (i, _, _), ty) -> do
                (bf, TermsInCtx ctx' _ ty', rtpats) <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [Error Other $ emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx +++ ctx') expr $ Just (nfType WHNF ty')
                let scope = closed (abstractTerm ctx' term)
                throwErrors $ checkTermination (Left i) pos (map (first snd) rtpats) scope
                return $ Just (conName, (rtpats, scope))
            _ -> do
                warn [notInScope pos "data constructor" (nameToString con)]
                return Nothing
    lift $ replaceDataType dt lcons $ Closed $ Type (vacuous $ replaceSort dtTerm (succ mk) $ Just mk) mk
    forM_ cons' $ \((pos, _), (_, conds, con), _) -> warn $
        checkConditions pos Nil (capply con) $ map (\(p, Closed t) -> (p, t)) conds
