module Main where

import System.Environment

import File.Load
import Evaluation.Monad
import REPL

main :: IO ()
main = do
    args <- getArgs
    runEvalT $ mapM_ loadFile args >> repl
