{
module Syntax.Parser.Lexer
    ( alexScanTokens
    , Token(..)
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
@newline    = \n $white*

:-

[$white # \n]+;
"--".*;
"{-" ([$any # \-] | \- [$any # \}])* "-}";

"Type" $digit*  {       TokUniverse . listToMaybe . map fst . reads }
"I"             { const TokInterval                                 }
"left"          { const TokLeft                                     }
"right"         { const TokRight                                    }
"Path"          { const TokPath                                     }
"path"          { const Tokpath                                     }
"coe"           { const TokCoe                                      }
"iso"           { const TokIso                                      }
"squeeze"       { const TokSqueeze                                  }
"import"        { const TokImport                                   }
"data"          { const TokData                                     }
"with"          { const TokWith                                     }
@ident          {       TokIdent                                    }
\\              { const TokLam                                      }
\(              { const TokLParen                                   }
\:              { const TokColon                                    }
\=              { const TokEquals                                   }
\{              { const TokLBrace                                   }
\}              { const TokRBrace                                   }
\;              { const TokSemicolon                                }
\.              { const TokDot                                      }
\)              { const TokRParen                                   }
\|              { const TokPipe                                     }
\@              { const TokAt                                       }
"->"            { const TokArrow                                    }
@newline        { const TokNewLine                                  }

{
data Token
    = TokIdent !String
    | TokUniverse !(Maybe Int)
    | TokInterval
    | TokLeft
    | TokRight
    | TokPath
    | Tokpath
    | TokCoe
    | TokIso
    | TokSqueeze
    | TokLam
    | TokLParen
    | TokImport
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
    | TokWith
    | TokNewLine
    | TokEOF

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
            go (findGoodSymbol $ skipOneSymbol inp')
        AlexSkip  inp' _    -> go inp'
        AlexToken inp'@((_, c), _) len act -> case act $ C.unpack (B.take len str) of
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
            tok -> cont tok inp'

findGoodSymbol :: AlexInput -> AlexInput
findGoodSymbol ((l, c), str) =
    let (f,s) = C.break (\c -> isAlpha c || isSpace c || c `elem` "\\(_:={};.)|@") str
    in ((l, c + B.length f), s)

skipOneSymbol :: AlexInput -> AlexInput
skipOneSymbol inp@((l, c), str) = if B.null str then inp else ((l, c + 1), B.tail str)

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
