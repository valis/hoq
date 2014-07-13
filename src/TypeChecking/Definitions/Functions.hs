{-# LANGUAGE RecursiveDo #-}

module TypeChecking.Definitions.Functions
    ( typeCheckFunction
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.Maybe

import Syntax.Expr as E
import Syntax.Term as T
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Definitions.Patterns
import TypeChecking.Definitions.Coverage
import TypeChecking.Definitions.Conditions
import TypeChecking.Definitions.Termination
import Normalization

typeCheckFunction :: MonadFix m => PIdent -> Expr -> [((Int, Int), [E.Pattern], Maybe Expr)] -> TCM m ()
typeCheckFunction p@(PIdent (lc,name)) ety clauses = mdo
    (ty, Type u _) <- typeCheck ety Nothing
    lvl <- case u of
            T.Universe lvl -> return lvl
            _              -> throwError [emsgLC (getPos ety) "" $ pretty "Expected a type" $$
                                                                   pretty "Actual type:" <+> prettyOpen Nil ty]
    addFunctionCheck p (FunCall lc name clauses') (Type ty lvl)
    clausesAndPats <- forW clauses $ \(lc,pats,mexpr) ->  do
        (bf, TermsInCtx ctx _ ty', rtpats) <- typeCheckPatterns Nil (Type (nf WHNF ty) lvl) pats
        case (bf,mexpr) of
            (True,  Nothing) -> return Nothing
            (False, Nothing) -> do
                let msg = "The right hand side can be omitted only if the absurd pattern is given"
                warn [emsgLC lc msg enull]
                return Nothing
            (True, Just expr) -> do
                let msg = "If the absurd pattern is given the right hand side must be omitted"
                warn [emsgLC (getPos expr) msg enull]
                return Nothing
            (False, Just expr) -> do
                (term, _) <- typeCheckCtx ctx expr (Just ty')
                let scope = closed (abstractTermInCtx ctx term)
                throwErrors (checkTermination name rtpats scope)
                return $ Just ((rtpats, scope), (lc, rtpats))
    let clauses' = map fst clausesAndPats
    case checkCoverage (map snd clausesAndPats) of
        Nothing -> when (length clausesAndPats == length (filter (\(_,_,me) -> isJust me) clauses)) $
                warn [emsgLC lc "Incomplete pattern matching" enull]
        Just uc -> warn $ map (\lc -> emsgLC lc "Unreachable clause" enull) uc
    warn $ checkConditions lc (Closed $ FunCall lc name clauses') (map fst clausesAndPats)
