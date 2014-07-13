module File.Load
    ( loadFile
    ) where

import System.IO
import System.FilePath
import Control.Monad
import Control.Monad.Fix
import Control.Monad.Trans
import Control.Exception

import Syntax.BNFC.ErrM
import Syntax.BNFC.ParGrammar
import Syntax.BNFC.LayoutGrammar
import Syntax.ErrorDoc
import Syntax.PrettyPrinter()
import Syntax.Expr
import TypeChecking.Definitions
import TypeChecking.Monad

loadFile :: (MonadIO m, MonadFix m) => String -> ScopeM m ()
loadFile filename = do
    (errs, _) <- runWarnT $ do
        mcnt <- liftIO $ fmap Right (readFile filename)
                        `catch` \e -> return $ Left $ show (e :: SomeException)
        case mcnt of
            Right cnt -> parseDefs cnt
            Left err  -> warn [emsg err enull]
    liftIO $ mapM_ (hPutStrLn stderr . erenderWithFilename filename) errs

parseDefs :: (MonadIO m, MonadFix m) => String -> TCM m ()
parseDefs s = case parser s of
    Ok (Module imports defs) -> do
        forM_ imports $ \(Import _ moduleName) ->
            lift $ loadFile $ foldr1 combine (map (\(Name (PIdent (_,name))) -> name) moduleName) <.> "hoq"
        typeCheckDefs defs
    Bad err -> warn [emsg err enull]
  where
    parser :: String -> Err Module
    parser = pModule . resolveLayout True . myLexer
