module TypeChecking.Definitions.Functions
    ( typeCheckFunction
    ) where

import Data.Maybe
import Data.Void

import Syntax
import Semantics
import Semantics.Value
import Semantics.Pattern as P
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context as C
import TypeChecking.Expressions
import TypeChecking.Expressions.Utils
import TypeChecking.Expressions.Patterns
import TypeChecking.Expressions.Coverage
-- import TypeChecking.Expressions.Conditions
import TypeChecking.Definitions.Termination
import Normalization

typeCheckFunction :: Monad m => PName -> Term (Posn, Syntax) Void
    -> [(Posn, [Term PName Void], Maybe (Term (Posn, Syntax) Void))] -> TCM m ()
typeCheckFunction p@(pos, name) ety clauses = do
    (ty, Type u _) <- typeCheck ety Nothing
    k <- case nf WHNF u of
            Apply (Semantics _ (Universe k)) _ -> return k
            u' -> throwError [Error TypeMismatch $ emsgLC (termPos ety) "" $ pretty "Expected a type"
                                                                          $$ pretty "Actual type:" <+> prettyOpen C.Nil u']
    let cty = closed (Type ty k)
    fcid <- addFunctionCheck p [] cty
    clausesAndPats <- forW clauses $ \(pos',pats,mexpr) ->  do
        (bf, TermsInCtx ctx rtpats _ ty') <- typeCheckPatterns C.Nil (Type (nf WHNF ty) k) pats
        case (bf,mexpr) of
            (True,  Nothing) -> return Nothing
            (False, Nothing) -> do
                let msg = "The right hand side can be omitted only if the absurd pattern is given"
                warn [Error Other $ emsgLC pos' msg enull]
                return Nothing
            (True, Just expr) -> do
                let msg = "If the absurd pattern is given the right hand side must be omitted"
                warn [Error Other $ emsgLC (termPos expr) msg enull]
                return Nothing
            (False, Just expr) -> do
                (term, _) <- typeCheckCtx ctx expr $ Just (nfType WHNF ty')
                let scope = abstractTerm ctx term
                    rtterms = patternsToTerms rtpats
                throwErrors $ checkTermination (Right fcid) pos' rtterms C.Nil scope
                return $ Just ((rtterms, closed scope), (pos', P.Clause rtpats term))
    let clauses' = map fst clausesAndPats
        eval = map (fmap $ \(Closed scope) -> Closed $ replaceFunCalls fcid fc scope) clauses'
        fc = Closed $ capply $ Semantics (Name Prefix name) (FunCall fcid eval)
    lift $ replaceFunction name eval cty
    case checkCoverage (map snd clausesAndPats) of
        Nothing | length clausesAndPats /= length (filter (\(_,_,me) -> isJust me) clauses) -> return ()
        r -> warn (coverageErrorMsg pos r)
    -- warn $ checkConditions C.Nil (open fc) $ map (\((p,Closed t),(pos',_)) -> (pos',p,t)) clausesAndPats

replaceFunCalls :: ID -> Closed (Term Semantics) -> Term Semantics a -> Term Semantics a
replaceFunCalls name fc (Var a ts) = Var a $ map (replaceFunCalls name fc) ts
replaceFunCalls name fc (Apply (Semantics _ (FunCall name' _)) ts) | name == name' = apps (open fc) ts
replaceFunCalls name fc (Apply s ts) = Apply s $ map (replaceFunCalls name fc) ts
replaceFunCalls name fc (Lambda t) = Lambda (replaceFunCalls name fc t)
