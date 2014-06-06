import Distribution.Simple
import Control.Monad
import System.Directory
import System.Process
import System.Exit

main :: IO ()
main = do
    b <- doesFileExist "src/Syntax/BNFC/AbsGrammar.hs"
    unless b bnfc
    t1 <- getModificationTime $ "src/" ++ grammar
    t2 <- getModificationTime "src/Syntax/BNFC"
    if t1 > t2 then bnfc else defaultMain
  where
    grammar = "Grammar.cf"
    bnfc = do
        dir <- getCurrentDirectory
        setCurrentDirectory "src"
        status <- system $ "bnfc -p Syntax.BNFC " ++ grammar
        setCurrentDirectory dir
        case status of
            ExitSuccess -> defaultMain
            _ -> return ()
        exitWith status
