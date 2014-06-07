module Main where

import System.Environment
import System.IO
import Control.Exception
import Control.Monad

import Syntax.Term
import Syntax.BNFC.ErrM
import Syntax.BNFC.AbsGrammar
import Syntax.BNFC.ParGrammar
import Syntax.BNFC.LayoutGrammar
import Syntax.BNFC.PrintGrammar

parser :: String -> Err Defs
parser = pDefs . resolveLayout True . myLexer

parseFile :: String -> IO [Def]
parseFile filename = do
    cnt <- readFile filename
    case parser cnt of
        Bad s -> handleError $ filename ++ ": " ++ s
        Ok (Defs defs) -> return defs
    `catch` \e -> handleError $ show (e :: SomeException)
  where
    handleError s = hPutStrLn stderr s >> return []

main :: IO ()
main = do
    args <- getArgs
    defs <- fmap concat (mapM parseFile args)
    unless (null defs) $ putStrLn (printTree defs)
