module Syntax.Parser
    ( pDefs, pExpr
    , fixFixity, fixFixityDef
    ) where

import Data.Maybe
import Control.Monad.State
import qualified Data.ByteString as B

import Syntax
import Syntax.ErrorDoc
import Syntax.Parser.Lexer
import qualified Syntax.Parser.Parser as P
import TypeChecking.Monad.Warn
import TypeChecking.Expressions.Utils

pDefs :: Monad m => B.ByteString -> WarnT [Error] m [Def]
pDefs = liftM reverse . runParser P.pDefs

pExpr :: Monad m => [(Name,Fixity)] -> B.ByteString -> WarnT [Error] m RawExpr
pExpr tab str = runParser P.pExpr str >>= fixFixity tab

runParser :: Monad m => Parser a -> B.ByteString -> WarnT [Error] m a
runParser p s = case evalState (runWarnT $ p ((1, 1), s)) [Layout 1] of
    (errs, Nothing) -> throwError (mapErrs errs)
    (errs, Just a)  -> warn (mapErrs errs) >> return a
  where
    mapErrs = map $ \(pos, err) -> Error Other $ emsgLC pos err enull

data Tree p a = Branch Fixity Name Syntax (Tree p a) (Tree p a) | Leaf (Term (p, Syntax) a)

fixFixity :: Monad m => [(Name,Fixity)] -> Term (Posn, Syntax) a -> WarnT [Error] m (Term (Posn, Syntax) a)
fixFixity tab = go
  where
    go :: Monad m => Term (Posn, Syntax) a -> WarnT [Error] m (Term (Posn, Syntax) a)
    go = liftM treeToExpr . exprToTree
    
    exprToTree :: Monad m => Term (Posn, Syntax) a -> WarnT [Error] m (Tree Posn a)
    exprToTree (Var a ts) = liftM (Leaf . Var a) (mapM go ts)
    exprToTree (Lambda t) = liftM (Leaf . Lambda) (go t)
    exprToTree (Apply (_, Name Infix{} s) [t1, t2]) = do
        t1' <- exprToTree t1
        t2' <- go t2
        let ft = fromMaybe (Infix InfixL 90) (lookup s tab)
        branch ft s (Name ft s) t1' (Leaf t2')
    exprToTree (Apply (_, At) [t1,t2]) = do
        t1' <- exprToTree t1
        t2' <- go t2
        branch (Infix InfixL 90) (Operator "@") At t1' (Leaf t2')
    exprToTree (Apply (_, Null) (t:ts)) = liftM Leaf $ go (apps t ts)
    exprToTree (Apply s ts) = liftM (Leaf . Apply s) (mapM go ts)
    
    treeToExpr :: Tree Posn a -> Term (Posn, Syntax) a
    treeToExpr (Leaf t) = t
    treeToExpr (Branch ft _ s t1 t2) =
        let t1' = treeToExpr t1
        in Apply (termPos t1', s) [t1', treeToExpr t2]
    
    branch :: Monad m => Fixity -> Name -> Syntax -> Tree Posn a -> Tree Posn a -> WarnT [Error] m (Tree Posn a)
    branch ft@(Infix ia p) n s (Branch ft'@(Infix ia' p') n' s' a1 a2) b | p' < p || p == p' && ia == InfixR && ia' == InfixR = do
        a2' <- branch ft n s a2 b
        return (Branch ft' n' s' a1 a2')
    branch ft@(Infix ia p) n s a@(Branch ft'@(Infix ia' p') n' _ _ _) b | p == p' && not (ia == InfixL && ia' == InfixL) = do
        let showOp ft'' s'' = nameToInfix s'' ++ " [" ++ show ft'' ++ "]"
            msg = "Precedence parsing error: cannot mix " ++ showOp ft  n ++
                                                  " and " ++ showOp ft' n' ++ " in the same infix expression"
        warn [Error Other $ emsgLC (termPos $ treeToExpr a) msg enull]
        return (Branch ft n s a b)
    branch ft name syn a b = return (Branch ft name syn a b)

fixFixityDef :: Monad m => [(Name,Fixity)] -> Def -> WarnT [Error] m Def
fixFixityDef tab (DefType name expr) = liftM (DefType name) (fixFixity tab expr)
fixFixityDef tab (DefFun name pats (Just expr)) = liftM (DefFun name pats . Just) (fixFixity tab expr)
fixFixityDef _ d@DefFun{} = return d
fixFixityDef tab (DefData name params cons clauses) = do
    params' <- forM params (fixFixityTele tab)
    cons' <- forM cons $ \(ConDef con teles) -> liftM (ConDef con) $ forM teles (fixFixityTele tab)
    clauses' <- forM clauses $ \(Clause name pats expr) -> liftM (Clause name pats) (fixFixity tab expr)
    return (DefData name params' cons' clauses')
fixFixityDef tab (DefRecord name params mcon fields clauses) = do
    params' <- forM params (fixFixityTele tab)
    fields' <- forM fields $ \(Field name expr) -> liftM (Field name) (fixFixity tab expr)
    clauses' <- forM clauses $ \(Clause name pats expr) -> liftM (Clause name pats) (fixFixity tab expr)
    return (DefRecord name params' mcon fields' clauses')
fixFixityDef _ d@DefImport{} = return d
fixFixityDef _ d@DefFixity{} = return d

fixFixityTele :: Monad m => [(Name,Fixity)] -> Tele -> WarnT [Error] m Tele
fixFixityTele tab (VarsTele e vars expr) = liftM (VarsTele e vars) (fixFixity tab expr)
fixFixityTele tab (TypeTele e      expr) = liftM (TypeTele e     ) (fixFixity tab expr)
