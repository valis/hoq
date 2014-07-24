module TypeChecking.Definitions.Functions
    ( typeCheckFunction
    ) where

import Control.Monad
import Control.Monad.Fix
import Data.Maybe

import Syntax.Parser.Term
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Context
import TypeChecking.Expressions
import TypeChecking.Definitions.Patterns
import TypeChecking.Definitions.Coverage
import TypeChecking.Definitions.Conditions
import TypeChecking.Definitions.Termination
import Normalization

typeCheckFunction :: MonadFix m => PIdent -> Term Posn PIdent
    -> [(Posn, [PatternC Posn PIdent], Maybe (Term Posn PIdent))] -> TCM m ()
typeCheckFunction p@(PIdent pos name) ety clauses = do
    (ty, Type u _) <- typeCheck ety Nothing
    lvl <- case u of
            Universe _ lvl -> return lvl
            _              -> throwError [emsgLC (getAttr getPos ety) "" $ pretty "Expected a type"
                                                                        $$ pretty "Actual type:" <+> prettyOpen Nil ty]
    addFunctionCheck p (FunCall () name []) (Type ty lvl)
    clausesAndPats <- forW clauses $ \(pos,pats,mexpr) ->  do
        (bf, TermsInCtx ctx _ ty', rtpats) <- typeCheckPatterns Nil (Type (nf WHNF ty) lvl) pats
        case (bf,mexpr) of
            (True,  Nothing) -> return Nothing
            (False, Nothing) -> do
                let msg = "The right hand side can be omitted only if the absurd pattern is given"
                warn [emsgLC pos msg enull]
                return Nothing
            (True, Just expr) -> do
                let msg = "If the absurd pattern is given the right hand side must be omitted"
                warn [emsgLC (getAttr getPos expr) msg enull]
                return Nothing
            (False, Just expr) -> do
                (term, _) <- typeCheckCtx ctx (fmap (liftBase ctx) expr) (Just ty')
                let scope = closed (abstractTermInCtx ctx term)
                -- throwErrors (checkTermination name rtpats scope)
                return $ Just ((rtpats, scope), (pos, rtpats))
    lift (deleteFunction name)
    let clauses' = map fst clausesAndPats
        fc = Closed $ FunCall () name $ map (fmap $ \(Closed scope) -> Closed $ replaceFunCallsScope name fc scope) clauses'
    lift $ addFunction name (open fc) (Type ty lvl)
    case checkCoverage (map snd clausesAndPats) of
        Nothing -> when (length clausesAndPats == length (filter (\(_,_,me) -> isJust me) clauses)) $
                warn [emsgLC pos "Incomplete pattern matching" enull]
        Just uc -> warn $ map (\pos -> emsgLC pos "Unreachable clause" enull) uc
    warn $ checkConditions pos (Closed $ FunCall () name clauses') (map fst clausesAndPats)

replaceFunCallsScope :: String -> Closed (Term p) -> Scope s (Term p) a -> Scope s (Term p) a
replaceFunCallsScope name fc (ScopeTerm term) = ScopeTerm (replaceFunCalls name fc term)
replaceFunCallsScope name fc (Scope v scope)  = Scope v   (replaceFunCallsScope name fc scope)

replaceFunCalls :: String -> Closed (Term p) -> Term p a -> Term p a
replaceFunCalls name fc = go
  where
    go e@Var{} = e
    go (App e1 e2) = App (go e1) (go e2)
    go (Lam p (Scope1 s e)) = Lam p $ Scope1 s (replaceFunCalls name fc e)
    go (Pi p (Type e1 lvl1) e2 lvl2) = Pi p (Type (go e1) lvl1) (replaceFunCallsScope name fc e2) lvl2
    go (Con p i c cs as) = Con p i c cs (map go as)
    go fc'@(FunCall _ name' _) = if name == name' then open fc else fc'
    go e@FunSyn{} = e
    go e@Universe{} = e
    go (DataType p dt n as) = DataType p dt n (map go as)
    go e@Interval{} = e
    go e@ICon{} = e
    go (Path p h ma bs) = Path p h (fmap (\(a,l) -> (go a, l)) ma) (map go bs)
    go (PCon p me) = PCon p (fmap go me)
    go (At mab c d) = At (fmap (\(a,b) -> (go a, go b)) mab) (go c) (go d)
    go (Coe p as) = Coe p (map go as)
    go (Iso p as) = Iso p (map go as)
    go (Squeeze p as) = Squeeze p (map go as)
