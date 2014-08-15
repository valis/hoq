module File.Load
    ( loadFile
    ) where

import System.IO
import System.FilePath
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans
import Control.Monad.State
import Control.Exception
import qualified Data.ByteString as B

import Syntax
import Syntax.Parser
import Syntax.ErrorDoc
import Syntax.PrettyPrinter()
import TypeChecking.Expressions.Utils
import TypeChecking.Definitions
import TypeChecking.Monad

loadFile :: (MonadIO m, MonadFix m) => String -> ScopeT m ()
loadFile filename = do
    (errs, _) <- runWarnT $ evalStateT (loadFile' [] filename) []
    liftIO $ mapM_ (hPutStrLn stderr . erenderWithFilename filename . errorMsg) errs

loadFile' :: (MonadIO m, MonadFix m) => [String] -> String -> StateT [String] (TCM m) ()
loadFile' checking filename = do
    mcnt <- liftIO $ fmap Right (B.readFile filename)
                    `catch` \e -> return $ Left $ show (e :: SomeException)
    case mcnt of
        Right cnt -> parseDefs filename checking cnt
        Left err  -> lift $ warn [Error Other $ emsg err enull]

parseDefs :: (MonadIO m, MonadFix m) => String -> [String] -> B.ByteString -> StateT [String] (TCM m) ()
parseDefs cur checking s = do
    defs <- lift (pDefs s)
    forM_ (defs >>= \def -> case def of
        DefImport imp -> [imp]
        _             -> []) $ \moduleName ->
            let filename = foldr1 combine moduleName <.> "hoq"
            in if filename `elem` checking
                then lift $ warn [Error Other $ emsg ("Modules " ++ cur ++ " and " ++ filename ++ " form a cycle") enull]
                else do
                    checked <- get
                    if filename `elem` checked then return () else loadFile' (cur:checking) filename
    modify (cur:)
    lift (typeCheckDefs defs)
