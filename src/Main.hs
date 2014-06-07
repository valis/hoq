module Main where

import System.Environment
import System.IO
import Control.Exception
import Control.Monad
import Data.Traversable(sequenceA)
import Text.PrettyPrint

import Syntax.Term
import Syntax.BNFC.ErrM
import Syntax.BNFC.AbsGrammar
import Syntax.BNFC.ParGrammar
import Syntax.BNFC.LayoutGrammar
import Syntax.ExprToTerm
import Syntax.Expr
import Normalization

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

printDef :: Def -> IO ()
printDef (Def (DefType (PIdent (_,name)) tp) (DefFun (PIdent (_,name')) args expr)) = do
    case sequenceA (exprToTerm tp) of
        Left e -> hPutStrLn stderr e
        Right t -> putStrLn $ name ++ " : " ++ render (ppOpenTerm t)
    case sequenceA (exprToTerm expr) of
        Left e -> hPutStrLn stderr e
        Right t -> putStrLn $ name' ++ " " ++ unwords (map unArg args) ++ " = " ++ render (ppOpenTerm t)

main :: IO ()
main = do
    args <- getArgs
    defs <- fmap concat (mapM parseFile args)
    mapM_ printDef defs
