module REPL
    ( repl
    ) where

import System.Console.Readline
import System.Exit
import System.IO
import Control.Monad
import Control.Monad.Trans
import Data.Traversable(sequenceA)
import Text.PrettyPrint

import Syntax.BNFC.ParGrammar
import Syntax.BNFC.ErrM
import qualified Syntax.Expr as E
import Syntax.Term
import Syntax.PrettyPrinter
import Syntax.ErrorDoc
import TypeChecking
import Evaluation.Monad
import Evaluation.Normalization

parseExpr :: Monad m => String -> EvalT String Term m (Either [EMsg Term] (Term String))
parseExpr s = case parser s of
    Bad err -> return $ Left [emsg err enull]
    Ok expr -> do
        term <- typeCheck expr Nothing
        return $ case sequenceA term of
                    Hole errs _ -> Left errs
                    NoHole term -> Right term
  where
    parser :: String -> Err E.Expr
    parser = pExpr . myLexer

processCmd :: String -> String -> EvalT String Term IO ()
processCmd "quit" _ = liftIO exitSuccess
processCmd cmd str | Just mode <- nfMode cmd = do
    res <- parseExpr str
    liftIO $ case res of
        Left errs  -> mapM_ (hPutStrLn stderr . erender) errs
        Right term -> putStrLn $ render $ ppTerm (nf mode term)
  where
    nfMode "whnf" = Just WHNF
    nfMode "hnf"  = Just HNF
    nfMode "nf"   = Just NF
    nfMode _      = Nothing
processCmd cmd _ = liftIO $ hPutStrLn stderr $ "Unknown command " ++ cmd

repl :: EvalT String Term IO ()
repl = go ""
  where
    go last = do
        mline <- liftIO $ readline "> "
        case mline of
            Nothing   -> liftIO $ putStrLn ""
            Just line -> case break (== ' ') line of
                ("",_)      -> go last
                (cmd,line') -> do
                    when (line /= last) $ liftIO (addHistory line)
                    processCmd cmd line'
                    go line
