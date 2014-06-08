module REPL
    ( repl
    ) where

import System.Console.Readline
import System.Exit
import System.IO
import Control.Monad
import Control.Monad.Trans

import Syntax.Term
import Eval

processCmd :: String -> [String] -> EvalT String Def Term IO ()
processCmd "quit" _ = liftIO exitSuccess
processCmd cmd _ = liftIO $ hPutStrLn stderr $ "Unknown command " ++ cmd

repl :: EvalT String Def Term IO ()
repl = go ""
  where
    go last = do
        mline <- liftIO $ readline "> "
        case mline of
            Nothing   -> liftIO $ putStrLn ""
            Just line -> case words line of
                [] -> go last
                cmd:args -> do
                    when (line /= last) $ liftIO (addHistory line)
                    processCmd cmd args
                    go line
