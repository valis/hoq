module File.Load
    ( loadFile
    ) where

import System.IO
import Control.Monad
import Control.Monad.Trans
import Control.Exception
import Data.Foldable(toList)
import Data.Traversable(sequenceA)
import Data.List
import Data.Either

import Eval
import Syntax.Term
import Syntax.ExprToTerm
import Syntax.BNFC.ErrM
import Syntax.BNFC.ParGrammar
import Syntax.BNFC.LayoutGrammar
import qualified Syntax.Expr as E

loadFile :: MonadIO m => String -> EvalT String Def Term m ()
loadFile filename = do
    errs <- do
        mcnt <- liftIO $ fmap Right (readFile filename)
                        `catch` \e -> return $ Left $ show (e :: SomeException)
        case mcnt of
            Right cnt -> parseDefs cnt
            Left err -> return [err]
    liftIO $ mapM_ (hPutStrLn stderr) errs

parseDefs :: Monad m => String -> EvalT String Def Term m [String]
parseDefs s = case parser s of
    Bad e -> return [e]
    Ok (E.Defs defs) -> evalExprDefs defs
  where
    parser :: String -> Err E.Defs
    parser = pDefs . resolveLayout True . myLexer

exprPatToPattern :: E.Pattern -> Pattern String
exprPatToPattern (E.Pattern (E.PIdent (_,name)) pats) = Pattern name (map parPatToPattern pats)

parPatToPattern :: E.ParPat -> Pattern String
parPatToPattern (E.ParVar (E.PIdent (_,name))) = Pattern name []
parPatToPattern (E.ParPat _ p) = exprPatToPattern p

evalExprDefs :: Monad m => [E.Def] -> EvalT String Def Term m [String]
evalExprDefs [] = return []
evalExprDefs (E.DefType (E.PIdent (_,name)) ty : defs) = do
    let (funs,defs') = splitDefs defs
        (errs,names) = partitionEithers $ map (uncurry $ evalDefFuns name) funs
    errs' <- case sequenceA (exprToTerm ty) of
        Right ty' -> evalDefRec name (Def ty' names) >> return errs
        Left err -> return (err:errs)
    liftM (errs' ++) (evalExprDefs defs')
  where
    splitDefs :: [E.Def] -> ([([E.ParPat],E.Expr)],[E.Def])
    splitDefs (E.DefFun (E.Pattern (E.PIdent (_,name')) pats) expr : defs) | name == name' =
        let (funs,defs') = splitDefs defs
        in ((pats,expr):funs,defs')
    splitDefs defs = ([],defs)
    evalDefFuns :: String -> [E.ParPat] -> E.Expr -> Either String (Name [Pattern String] Int Term String)
    evalDefFuns name pats expr =
        let pats' = map parPatToPattern pats
        in fmap (Name pats' . abstract (`elemIndex` toList (Pattern name pats'))) $ sequenceA (exprToTerm expr)
evalExprDefs (E.DefFun (E.Pattern (E.PIdent (_,name)) []) expr : defs) = case sequenceA (exprToTerm expr) of
    Right term -> evalDef name (Syn (error "TODO") term) >> evalExprDefs defs
    Left err -> liftM (err:) (evalExprDefs defs)
evalExprDefs (E.DefFun (E.Pattern (E.PIdent ((l,c),_)) _) expr : defs) = liftM (msg:) (evalExprDefs defs)
  where msg = show l ++ ": " ++ show c ++ ": Cannot infer type of arguments"
