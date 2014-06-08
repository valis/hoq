module File.Load
    ( loadFile
    ) where

import System.IO
import Control.Monad
import Control.Monad.Trans
import Control.Exception
import Data.Traversable(sequenceA)
import Data.List

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
    Ok (E.Defs defs) -> liftM concat (mapM evalExprDef defs)
  where
    parser :: String -> Err E.Defs
    parser = pDefs . resolveLayout True . myLexer

evalExprDef :: Monad m => E.Def -> EvalT String Def Term m [String]
evalExprDef (E.Def (E.DefType (E.PIdent (_,name)) ty) (E.DefFun (E.PIdent (_,name')) args expr)) =
    case (sequenceA (exprToTerm ty), sequenceA (exprToTerm expr), name == name') of
        (Right ty', Right term, True) -> do
            let vars = map E.unArg args
            if null vars
                then evalDef name (Syn ty' term)
                else evalDef name $ Def ty' $ Name vars $ abstract (\v -> v `elemIndex` vars) term
            return []
        (r1, r2, r3) -> return $ either return (const []) r1 ++ either return (const []) r2 ++ if r3 then [] else [msg]
  where
    msg = "The name of type signature '" ++ name ++ "' does not match the name of function '" ++ name' ++ "'"
