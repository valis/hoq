module Main where

import System.Environment
import Text.PrettyPrint

import Syntax.Term
import File.Load
import Eval
import REPL

main :: IO ()
main = do
    args <- getArgs
    case args of
        "-repl":args' -> runEvalT $ mapM_ loadFile args' >> repl
        _ -> do
            defs <- runEvalT $ mapM_ loadFile args >> getEntries
            mapM_ (putStrLn . render . uncurry ppDef) defs
