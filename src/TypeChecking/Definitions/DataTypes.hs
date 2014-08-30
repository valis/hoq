module TypeChecking.Definitions.DataTypes
    ( typeCheckDataType
    ) where

import Control.Monad
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

typeCheckDataType :: Monad m => PName -> [Tele] -> [S.Con] -> [Clause] -> TCM m ()
typeCheckDataType p@(_, dt) params cons conds = do
    let lcons = length cons
    (SomeEq ctx, dataType@(Type dtTerm _)) <- typeCheckTelescope Nil params $ Type (universe Prop) (Set NoLevel)
    dtID <- addDataTypeCheck p lcons $ Closed (vacuous dataType)
    cons' <- forW (zip cons [0..]) $ \(ConDef con@(pos, conName) tele, i) -> do
        (_, conType) <- typeCheckTelescope ctx tele $
            Type (Apply (Semantics (Name Prefix dt) $ DataType dtID lcons) $ ctxToVars ctx) Prop
        case findOccurrence dtID (nf WHNF $ getType conType) of
            Just n | n > 1 -> throwError [Error Other $ emsgLC pos "Data type is not strictly positive" enull]
            _ -> return ()
        return $ Just (con, i, conType)
    let ks = map (\(_, _, Type _ k) -> k) cons'
        mk = dmaximum $ (if lcons > 1 then Set NoLevel else Prop) : ks
    forM_ cons' $ \(con, i, Type ty k) -> addConstructorCheck con dtID i lcons (PatEval []) $
        Closed $ Type (vacuous $ abstractTerm ctx $ replaceSort ty mk Nothing) mk
    conds' <- forW conds $ \(Clause (pos, con) pats expr) ->
        case find (\((_, c), _, _) -> c == con) cons' of
            Just ((_, conName), i, ty) -> do
                (bf, TermsInCtx ctx' _ ty', rtpats) <- typeCheckPatterns ctx (nfType WHNF ty) pats
                when bf $ warn [Error Other $ emsgLC pos "Absurd patterns are not allowed in conditions" enull]
                (term, _) <- typeCheckCtx (ctx +++ ctx') expr $ Just (nfType WHNF ty')
                let scope = closed (abstractTerm ctx' term)
                throwErrors $ checkTermination (Left i) pos (map (first snd) rtpats) scope
                return $ Just (conName, (pos, rtpats, scope))
            _ -> do
                warn [notInScope pos "data constructor" (nameToString con)]
                return Nothing
    lift $ replaceDataType dt lcons $ Closed $ Type (vacuous $ replaceSort dtTerm (succ mk) $ Just mk) mk
    let cons'' = map (\((_, con), i, ty) -> (con, i, ty, map snd $ filter (\(c,_) -> c == con) conds')) cons'
    forM_ cons'' $ \(con, i, Type ty k, conds'') ->
        lift $ replaceConstructor con dtID i lcons (PatEval $ map (\(_,b,c) -> (b,c)) conds'') $
            Closed $ Type (vacuous $ abstractTerm ctx $ replaceSort ty mk Nothing) mk
    forM_ cons'' $ \(con, i, _, conds'') ->
        let conTerm = Semantics (Name Prefix con) $ Con $ DCon i lcons $ PatEval $ map (\(_,b,c) -> (b,c)) conds''
        in warn $ checkConditions ctx (capply conTerm) $ map (\(pos, p, Closed t) -> (pos, p, t)) conds''
