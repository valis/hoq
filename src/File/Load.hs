module File.Load
    ( loadFile
    ) where

import System.IO
import System.FilePath
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans
import Control.Exception
import qualified Data.ByteString as B

import Syntax.Parser
import Syntax.Parser.Term
import Syntax.ErrorDoc
import Syntax.PrettyPrinter()
-- import TypeChecking.Definitions
import TypeChecking.Monad

loadFile :: (MonadIO m, MonadFix m) => String -> ScopeM m ()
loadFile filename = do
    (errs, _) <- runWarnT $ do
        mcnt <- liftIO $ fmap Right (B.readFile filename)
                        `catch` \e -> return $ Left $ show (e :: SomeException)
        case mcnt of
            Right cnt -> parseDefs cnt
            Left err  -> warn [emsg err enull]
    liftIO $ mapM_ (hPutStrLn stderr . erenderWithFilename filename) errs

parseDefs :: (MonadIO m, MonadFix m) => B.ByteString -> TCM m ()
parseDefs s = do
    defs <- pDefs s
    lift $ forM_ (defs >>= \def -> case def of
        DefImport imp -> [imp]
        _             -> []) $ \moduleName -> loadFile $ foldr1 combine moduleName <.> "hoq"
    -- typeCheckDefs defs
