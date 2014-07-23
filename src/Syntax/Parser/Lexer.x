{
module Syntax.Parser.Lexer
    ( alexScanTokens
    , Token(..), tokGetPos
    , Parser, ParserErr
    , Layout(..)
    ) where

import Data.Word
import Data.Char(isAlpha,isSpace)
import Data.Maybe
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Control.Monad.State

import Syntax.Parser.Term
import TypeChecking.Monad.Warn
}

$alpha      = [a-zA-Z]
$digit      = [0-9]
$any        = [\x00-\x10ffff]
@ident      = ($alpha | \_) ($alpha | $digit | \' | \- | \_)*
@lcomm      = "--".*
@mcomm      = "{-" ([$any # \-] | \- [$any # \}])* "-}"
@skip       = $white | @lcomm | @mcomm
@newline    = \n @skip*
@with       = "with" @skip*
@import     = "import" $white+ @ident ("." @ident)*

:-

[$white # \n]+;
@lcomm;
@mcomm;

"Type" $digit*  { \p s -> TokUniverse (p, listToMaybe $ map fst $ reads $ drop 4 s) }
"I"             { \p _ -> TokInterval p                                             }
"left"          { \p _ -> TokLeft p                                                 }
"right"         { \p _ -> TokRight p                                                }
"Path"          { \p _ -> TokPath p                                                 }
"path"          { \p _ -> Tokpath p                                                 }
"coe"           { \p _ -> TokCoe p                                                  }
"iso"           { \p _ -> TokIso p                                                  }
"squeeze"       { \p _ -> TokSqueeze p                                              }
@import         { \_ s -> TokImport $ breaks '.' $
                    dropWhile (\c -> not (isAlpha c) && c /= '_') (drop 6 s)        }
"data"          { \_ _ -> TokData                                                   }
@with           { \_ _ -> TokWith 0                                                 }
@ident          { \p s -> TokIdent (PIdent p s)                                     }
\\              { \p _ -> TokLam p                                                  }
\(              { \p _ -> TokLParen p                                               }
\:              { \_ _ -> TokColon                                                  }
\=              { \_ _ -> TokEquals                                                 }
\{              { \_ _ -> TokLBrace                                                 }
\}              { \_ _ -> TokRBrace                                                 }
\;              { \_ _ -> TokSemicolon                                              }
\.              { \_ _ -> TokDot                                                    }
\)              { \_ _ -> TokRParen                                                 }
\|              { \_ _ -> TokPipe                                                   }
\@              { \_ _ -> TokAt                                                     }
"->"            { \_ _ -> TokArrow                                                  }
@newline        { \_ _ -> TokNewLine                                                }

{
data Token
    = TokIdent !PIdent
    | TokUniverse !(Posn, Maybe Int)
    | TokInterval !Posn
    | TokLeft !Posn
    | TokRight !Posn
    | TokPath !Posn
    | Tokpath !Posn
    | TokCoe !Posn
    | TokIso !Posn
    | TokSqueeze !Posn
    | TokLam !Posn
    | TokLParen !Posn
    | TokImport ![String]
    | TokData
    | TokColon
    | TokEquals
    | TokLBrace
    | TokRBrace
    | TokSemicolon
    | TokDot
    | TokRParen
    | TokPipe
    | TokAt
    | TokArrow
    | TokWith !Int
    | TokNewLine
    | TokEOF

tokGetPos :: Token -> Maybe Posn
tokGetPos (TokIdent (PIdent pos _)) = Just pos
tokGetPos (TokUniverse (pos, _)) = Just pos
tokGetPos (TokLeft pos) = Just pos
tokGetPos (TokRight pos) = Just pos
tokGetPos (TokPath pos) = Just pos
tokGetPos (Tokpath pos) = Just pos
tokGetPos (TokCoe pos) = Just pos
tokGetPos (TokIso pos) = Just pos
tokGetPos (TokSqueeze pos) = Just pos
tokGetPos (TokLam pos) = Just pos
tokGetPos (TokLParen pos) = Just pos
tokGetPos _ = Nothing

breaks :: Eq a => a -> [a] -> [[a]]
breaks a as = case break (== a) as of
    (as1, [])    -> [as1]
    (as1, _:as2) -> as1 : breaks a as2

type AlexInput = (Posn, B.ByteString)

data Layout = Layout Int | NoLayout deriving Eq

type ParserErr a = WarnT [(Posn, String)] (State [Layout]) a
type Parser a = AlexInput -> ParserErr a

alexScanTokens :: (Token -> Parser a) -> Parser a
alexScanTokens cont = go
  where
    go inp@(pos,str) = case alexScan inp 0 of
        AlexEOF             -> cont TokEOF inp
        AlexError inp'      -> do
            warn [(pos, "Lexer error")]
            (go . findAGoodSymbol . skippingTheBadOne) inp'
        AlexSkip  inp' _    -> go inp'
        AlexToken inp'@((_, c), _) len act -> case act pos $ C.unpack (B.take len str) of
            TokNewLine -> do
                layout:layouts <- lift get
                case layout of
                    NoLayout -> go inp'
                    Layout n -> case compare n c of
                        LT -> go inp'
                        EQ -> cont TokSemicolon inp'
                        GT -> do
                            lift (put layouts)
                            cont TokRBrace inp
            TokRBrace  -> do
                layout <- lift get
                if NoLayout `elem` layout
                then do
                    lift $ put (tail layout)
                    cont TokRBrace $ if head layout == NoLayout then inp' else inp
                else do
                    warn [(pos, "Misplaced '}'")]
                    go inp'
            TokWith _  -> cont (TokWith c) inp'
            tok -> cont tok inp'

findAGoodSymbol :: AlexInput -> AlexInput
findAGoodSymbol ((l, c), str) =
    let (f,s) = C.break (\c -> isAlpha c || isSpace c || c `elem` "\\(_:={};.)|@") str
    in ((l, c + B.length f), s)

skippingTheBadOne :: AlexInput -> AlexInput
skippingTheBadOne inp@((l, c), str) = if B.null str then inp else ((l, c + 1), B.tail str)

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (pos, str) = fmap (\(h,t) -> (h, (alexMove pos $ C.head str, t))) (B.uncons str)

tabSize :: Int
tabSize = 4

alexMove :: Posn -> Char -> Posn
alexMove (l, c) '\t' = (l, ((c + tabSize - 1) `div` tabSize) * tabSize + 1)
alexMove (l, c) '\n' = (l + 1, 1)
alexMove (l, c) _    = (l , c + 1)

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = error "alexInputPrevChar"
}
