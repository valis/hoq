{
module Lexer where

import Data.Char
import Data.Word
import Data.Maybe
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
}

$alpha = [a-zA-Z]
$digit = [0-9]
$any   = [\x00-\x10ffff]
@ident = $alpha ($alpha | $digit | \' | \- | \_)*

:-

$white+;
"--".*;
"{-" ([$any # \-] | \- [$any # \}])* "-}";

"Type" $digit*  {         TokenPos . TokUniverse . listToMaybe . map fst . reads }
"I"             { const $ TokenPos TokInterval }
"left"          { const $ TokenPos TokLeft }
"right"         { const $ TokenPos TokRight }
"Path"          { const $ TokenPos TokPath }
"path"          { const $ TokenPos Tokpath }
"coe"           { const $ TokenPos TokCoe }
"iso"           { const $ TokenPos TokIso }
"squeeze"       { const $ TokenPos TokSqueeze }
"import"        { const $ TokenPos TokImport }
@ident          {         TokenPos . TokIdent }
\\              { const $ TokenPos TokLam }
\(              { const $ TokenPos TokLParen }
\_              { const $ TokenPos TokUnderscore }
\:              { \_ _ -> TokColon }
\=              { \_ _ -> TokEquals }
\{              { \_ _ -> TokLBrace }
\}              { \_ _ -> TokRBrace }
\;              { \_ _ -> TokSemicolon }
\.              { \_ _ -> TokDot }
\)              { \_ _ -> TokRParen }
\|              { \_ _ -> TokPipe }
\@              { \_ _ -> TokAt }
"->"            { \_ _ -> TokArrow }

{
data TokenPos
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
    | TokUnderscore
    | TokImport
    | TokError
    deriving Show

data Token
    = TokenPos !TokenPos !Posn
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
    deriving Show

data Posn = Posn !Int !Int
    deriving Show

type AlexInput = (Posn, B.ByteString)

alexScanTokens :: B.ByteString -> [Token]
alexScanTokens str = go (Posn 1 1, str)
  where
    go :: AlexInput -> [Token]
    go inp@(pos, str) = case alexScan inp 0 of
        AlexEOF                -> []
        AlexError inp'         -> TokenPos TokError pos : go (findGoodSymbol $ skipOneSymbol inp')
        AlexSkip  inp' _       -> go inp'
        AlexToken inp' len act -> act (C.unpack $ B.take len str) pos : go inp'

findGoodSymbol :: AlexInput -> AlexInput
findGoodSymbol (Posn l c, str) =
    let (f,s) = C.break (\c -> isAlpha c || isSpace c || c `elem` "\\(_:={};.)|@") str
    in (Posn l (c + B.length f), s)

skipOneSymbol :: AlexInput -> AlexInput
skipOneSymbol inp@(Posn l c, str) = if B.null str then inp else (Posn l (c + 1), B.tail str)

alexGetByte :: AlexInput -> Maybe (Word8, AlexInput)
alexGetByte (pos, str) = fmap (\(h,t) -> (h, (alexMove pos $ C.head str, t))) (B.uncons str)

tabSize :: Int
tabSize = 4

alexMove :: Posn -> Char -> Posn
alexMove (Posn l c) '\t' = Posn l (((c + tabSize - 1) `div` tabSize) * tabSize + 1)
alexMove (Posn l c) '\n' = Posn (l + 1) 1
alexMove (Posn l c) _    = Posn l (c + 1)

alexInputPrevChar :: AlexInput -> Char
alexInputPrevChar = error "alexInputPrevChar"
}
