{-# LANGUAGE RecursiveDo #-}

module TypeChecking.Definitions.Functions
    ( typeCheckFunction
    ) where

import Control.Monad.Fix
import Data.Maybe

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.Context
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Expressions
import TypeChecking.Definitions.Patterns
import TypeChecking.Definitions.Coverage
import Normalization

typeCheckFunction :: MonadFix m => Arg -> Expr -> [((Int, Int), [ParPat], Maybe Expr)] -> TCM m ()
typeCheckFunction arg ety cases = mdo
    (ty, u) <- typeCheck ety Nothing
    case u of
        T.Universe _ -> return ()
        _            -> throwError [emsgLC (getPos ety) "" $ pretty "Expected a type" $$
                                                             pretty "Actual type:" <+> prettyOpen Nil ty]
    addFunctionCheck arg (FunCall (unArg arg) names) ty
    namesAndPats <- forW cases $ \(lc,pats,mexpr) ->  do
        (bf, TermsInCtx ctx _ ty', rtpats, cpats) <- typeCheckPatterns Nil (nf WHNF ty) pats
        case (bf,mexpr) of
            (True,  Nothing) -> return Nothing
            (False, Nothing) -> do
                let msg = "The right hand side can be omitted only if the absurd pattern is given"
                warn [emsgLC (argGetPos arg) msg enull]
                return Nothing
            (True, Just expr) -> do
                let msg = "If the absurd pattern is given the right hand side must be omitted"
                warn [emsgLC (getPos expr) msg enull]
                return Nothing
            (False, Just expr) -> do
                (term, _) <- typeCheckCtx ctx expr $ Just (nf WHNF ty')
                return $ Just (ClosedName rtpats $ fromJust $ closed $ toScope $
                    reverseTerm (length $ contextNames ctx) (abstractTermInCtx ctx term), (lc, cpats))
    let names = map fst namesAndPats
    case checkCoverage (map snd namesAndPats) of
        Nothing -> warn [emsgLC (argGetPos arg) "Incomplete pattern matching" enull]
        Just uc -> warn $ map (\lc -> emsgLC lc "Unreachable clause" enull) uc
