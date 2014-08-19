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

loadFile :: (MonadIO m, MonadFix m) => String -> ScopeT m [(Name,Fixity)]
loadFile filename = do
    ((errs, _), (_, tab)) <- runStateT (runWarnT $ loadFile' [] filename) ([],[])
    liftIO $ mapM_ (\(fn, err) -> hPutStrLn stderr $ erenderWithFilename fn $ errorMsg err) errs
    return tab

loadFile' :: (MonadIO m, MonadFix m) => [String] -> String
    -> WarnT [(String,Error)] (StateT ([String],[(Name,Fixity)]) (ScopeT m)) ()
loadFile' checking filename = do
    mcnt <- liftIO $ fmap Right (B.readFile filename)
                    `catch` \e -> return $ Left $ show (e :: SomeException)
    case mcnt of
        Right cnt -> parseDefs filename checking cnt
        Left err  -> warn [(filename, Error Other $ emsg err enull)]

parseDefs :: (MonadIO m, MonadFix m) => String -> [String] -> B.ByteString
    -> WarnT [(String,Error)] (StateT ([String],[(Name,Fixity)]) (ScopeT m)) ()
parseDefs cur checking s = do
    defs <- mapWarnT (map $ \e -> (cur,e)) (pDefs s)
    defs' <- forM defs $ \def -> case def of
        DefImport moduleName -> do
            let filename = foldr1 combine moduleName <.> "hoq"
            if filename `elem` checking
                then warn [(cur, Error Other $ emsg ("Modules " ++ cur ++ " and " ++ filename ++ " form a cycle") enull)]
                else do
                    (checked,_) <- lift get
                    if filename `elem` checked then return () else loadFile' (cur:checking) filename
            return def
        DefFixity pos inf pr ops -> do
            forM_ ops $ \op -> do
                (fns,tab) <- lift get
                case lookup op tab of
                    Just ft ->
                        let msg = "Multiple fixity declarations for " ++ nameToInfix op ++ " [" ++ show ft ++ "]"
                        in warn [(cur, Error Other $ emsgLC pos msg enull)]
                    Nothing -> return ()
                lift $ put (fns, (op, Infix inf pr):tab)
            return def
        _ -> lift get >>= \(_,tab) -> mapWarnT (map $ \e -> (cur,e)) (fixFixityDef tab def)
    lift $ modify $ \(fns,tab) -> (cur:fns,tab)
    (es,mr) <- lift $ lift $ runWarnT (typeCheckDefs defs')
    let es' = map (\e -> (cur,e)) es
    case mr of
        Nothing -> throwError es'
        Just r -> warn es' >> return r
