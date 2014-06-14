module Main where

import System.Environment

import File.Load
import TypeChecking.Monad.Scope
import REPL

main :: IO ()
main = do
    args <- getArgs
    runScopeT $ mapM_ loadFile args >> repl
