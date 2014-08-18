{
module Syntax.Parser.Lexer
    ( alexScanTokens
    , Token(..), tokGetPos
    , Parser, ParserErr
    , Layout(..)
    ) where

import Data.Word
import Data.Char(isAlpha,isSpace)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Control.Monad.State

import TypeChecking.Monad.Warn
import Syntax
}

$alpha      = [a-zA-Z]
$digit      = [0-9]
$any        = [\x00-\x10ffff]
$operator   = [\~\!\@\#\$\%\^\&\*\-\+\=\|\?\<\>\,\.\/\:\;\[\]\{\}]
@ident      = ($alpha | \_) ($alpha | $digit | \' | \- | \_)*
@lcomm      = "--".*
@mcomm      = "{-" ([$any # \-] | \- [$any # \}])* "-}"
@skip       = $white | @lcomm | @mcomm
@newline    = \n @skip*
@with       = "with" @skip*
@of         = "of" @skip*
@import     = "import" $white+ @ident ("." @ident)*

:-

[$white # \n]+;
@lcomm;
@mcomm;

@import         { \_ s -> TokImport $ breaks '.' $
                    dropWhile (\c -> not (isAlpha c) && c /= '_') (drop 6 s)        }
"data"          { \_ _ -> TokData                                                   }
"case"          { \p _ -> TokCase p                                                 }
@of             { \_ _ -> TokOf 0                                                   }
@with           { \_ _ -> TokWith 0                                                 }
\\              { \p _ -> TokLam p                                                  }
\(              { \p _ -> TokLParen p                                               }
\:              { \_ _ -> TokColon                                                  }
\=              { \_ _ -> TokEquals                                                 }
\{              { \p _ -> TokLBrace p                                               }
\}              { \_ _ -> TokRBrace                                                 }
\;              { \_ _ -> TokSemicolon                                              }
\)              { \_ _ -> TokRParen                                                 }
\|              { \_ _ -> TokPipe                                                   }
\@              { \_ _ -> TokAt                                                     }
\`              { \_ _ -> TokApos                                                   }
"->"            { \_ _ -> TokArrow                                                  }
$operator+      { \p s -> TokOperator (PIdent p s)                                  }
$digit+         { \p s -> TokInteger (p, read s)                                    }
"infixl"        { \p _ -> TokInfix (p, InfixL)                                      }
"infixr"        { \p _ -> TokInfix (p, InfixR)                                      }
"infix"         { \p _ -> TokInfix (p, InfixNA)                                     }
@ident          { \p s -> TokIdent (PIdent p s)                                     }
@newline        { \_ _ -> TokNewLine                                                }

{
data Token
    = TokIdent !PIdent
    | TokOperator !PIdent
    | TokLam !Posn
    | TokLParen !Posn
    | TokImport ![String]
    | TokData
    | TokCase !Posn
    | TokOf !Int
    | TokColon
    | TokEquals
    | TokLBrace !Posn
    | TokRBrace
    | TokSemicolon
    | TokDot
    | TokRParen
    | TokPipe
    | TokAt
    | TokApos
    | TokArrow
    | TokWith !Int
    | TokNewLine
    | TokInfix !(Posn, Infix)
    | TokInteger !(Posn, Int)
    | TokEOF

tokGetPos :: Token -> Maybe Posn
tokGetPos (TokIdent (PIdent pos _)) = Just pos
tokGetPos (TokLam pos) = Just pos
tokGetPos (TokLParen pos) = Just pos
tokGetPos (TokOperator (PIdent pos _)) = Just pos
tokGetPos _ = Nothing

breaks :: Eq a => a -> [a] -> [[a]]
breaks a as = case break (== a) as of
    (as1, [])    -> [as1]
    (as1, _:as2) -> as1 : breaks a as2

type AlexInput = (Posn, B.ByteString)

data Layout = Layout Int | NoLayout deriving Eq

type ParserErr a = WarnT [(Posn, String)] (State ([Layout], [(Name,Fixity)])) a
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
                (layout:layouts, ft) <- lift get
                case layout of
                    NoLayout -> go inp'
                    Layout n -> case compare n c of
                        LT -> go inp'
                        EQ -> cont TokSemicolon inp'
                        GT -> do
                            lift $ put (layouts, ft)
                            cont TokRBrace inp
            TokRBrace  -> do
                (layout, ft) <- lift get
                if NoLayout `elem` layout
                then do
                    lift $ put (tail layout, ft)
                    cont TokRBrace $ if head layout == NoLayout then inp' else inp
                else do
                    warn [(pos, "Misplaced '}'")]
                    go inp'
            TokWith{} -> cont (TokWith c) inp'
            TokOf{} -> cont (TokOf c) inp'
            tok -> cont tok inp'

findAGoodSymbol :: AlexInput -> AlexInput
findAGoodSymbol ((l, c), str) =
    let (f,s) = C.break (\c -> isAlpha c || isSpace c || c `elem` "~!@#$%^&*-+=|?<>,./:l[]{}()\\_") str
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
