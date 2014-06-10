module File.Load
    ( loadFile
    ) where

import System.IO
import Control.Monad.Trans
import Control.Exception

import Syntax.Term
import Syntax.BNFC.ErrM
import Syntax.BNFC.ParGrammar
import Syntax.BNFC.LayoutGrammar
import qualified Syntax.Expr as E
import TypeChecking
import Evaluation.Monad
import Evaluation.Normalization

loadFile :: MonadIO m => String -> EvalT String RTDef Term m ()
loadFile filename = do
    errs <- do
        mcnt <- liftIO $ fmap Right (readFile filename)
                        `catch` \e -> return $ Left $ show (e :: SomeException)
        case mcnt of
            Right cnt -> parseDefs cnt
            Left err -> return [err]
    liftIO $ mapM_ (hPutStrLn stderr) errs

parseDefs :: Monad m => String -> EvalT String RTDef Term m [String]
parseDefs s = case parser s of
    Bad e -> return [e]
    Ok (E.Defs defs) -> typeCheckDefs defs
  where
    parser :: String -> Err E.Defs
    parser = pDefs . resolveLayout True . myLexer
