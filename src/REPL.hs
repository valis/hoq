module REPL
    ( repl
    ) where

import System.Console.Readline
import System.Exit
import System.IO
import Control.Monad
import Control.Monad.Trans
import Text.PrettyPrint
import qualified Data.ByteString.Char8 as C
import Data.Bifunctor

import Semantics
import Syntax.Parser
import Syntax.PrettyPrinter
import Syntax.ErrorDoc
import TypeChecking.Monad
import TypeChecking.Expressions
import Normalization

ep :: NF -> String -> ScopeM IO ()
ep mode str = do
    mres <- runWarnT $ do
        term <- pExpr (C.pack str)
        (term',_) <- typeCheck term Nothing
        return term'
    liftIO $ case mres of
        ([], Just term) -> putStrLn $ render $ ppTerm $ first syntax (nf mode term)
        (errs, _)       -> mapM_ (hPutStrLn stderr . erender) errs

processCmd :: String -> String -> ScopeM IO ()
processCmd "quit" _   = liftIO exitSuccess
processCmd "nf"   str = ep NF str
processCmd "step" str = ep Step str
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
