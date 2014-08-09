module Syntax.Parser
    ( pDefs, pExpr
    ) where

import Control.Monad.State
import qualified Data.ByteString as B

import Syntax
import Syntax.ErrorDoc
import Syntax.Parser.Lexer
import qualified Syntax.Parser.Parser as P
import TypeChecking.Monad.Warn

pDefs :: Monad m => B.ByteString -> WarnT [EMsg f] m [Def]
pDefs = liftM reverse . runParser P.pDefs

pExpr :: Monad m => B.ByteString -> WarnT [EMsg f] m RawExpr
pExpr = runParser P.pExpr

runParser :: Monad m => Parser a -> B.ByteString -> WarnT [EMsg f] m a
runParser p s = case evalState (runWarnT $ p ((1, 1), s)) ([Layout 1], []) of
    (errs, Nothing) -> throwError (mapErrs errs)
    (errs, Just a)  -> warn (mapErrs errs) >> return a
  where
    mapErrs = map $ \(pos, err) -> emsgLC pos err enull
