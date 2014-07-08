module REPL
    ( repl
    ) where

import System.Console.Readline
import System.Exit
import System.IO
import Control.Monad
import Control.Monad.Trans
import Text.PrettyPrint

import Syntax.BNFC.ParGrammar
import Syntax.BNFC.ErrM
import Syntax.Term
import Syntax.PrettyPrinter
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Expressions
import Normalization

parseExpr :: Monad m => String -> TCM m (Term String)
parseExpr s = case pExpr (myLexer s) of
    Bad err -> throwError [emsg err enull]
    Ok expr -> liftM fst (typeCheck expr Nothing)

ep :: NF -> String -> ScopeM IO ()
ep mode str = do
    mres <- runWarnT (parseExpr str)
    liftIO $ case mres of
        ([], Nothing)   -> return ()
        ([], Just term) -> putStrLn $ render $ ppTerm (nf mode term)
        (errs, _)       -> mapM_ (hPutStrLn stderr . erender) errs

processCmd :: String -> String -> ScopeM IO ()
processCmd "quit" _   = liftIO exitSuccess
processCmd "nf"   str = ep NF str
processCmd "hnf"  str = ep HNF str
processCmd "whnf" str = ep WHNF str
processCmd cmd _ = liftIO $ hPutStrLn stderr $ "Unknown command " ++ cmd

repl :: ScopeM IO ()
repl = go ""
  where
    go last = do
        mline <- liftIO $ readline "> "
        case mline of
            Nothing   -> liftIO $ putStrLn ""
            Just line -> case break (== ' ') line of
                ("",_)      -> go last
                (c:cmd,line') -> do
                    when (line /= last) $ liftIO (addHistory line)
                    if c == ':' then processCmd cmd line' else ep NF line
                    go line
