module Main where

import System.Environment

import File.Load
import TypeChecking.Monad.Scope
import REPL

main :: IO ()
main = do
    args <- getArgs
    runScopeT $ do
        tabs <- mapM loadFile args
        repl (concat tabs)
