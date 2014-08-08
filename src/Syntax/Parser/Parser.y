--
{
module Syntax.Parser.Parser
    ( pDefs, pExpr
    ) where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Error
import Data.Void

import Syntax.Parser.Lexer
import Syntax
}

%name pDefs Defs
%name pExpr Expr
%tokentype { Token }
%error { parseError }
%monad { Parser } { bind } { return' }
%lexer { alexScanTokens } { TokEOF }

%token
    TIdent      { TokIdent    $$    }
    Import      { TokImport   $$    }
    Operator    { TokOperator $$    }
    '\\'        { TokLam      $$    }
    '('         { TokLParen   $$    }
    'data'      { TokData           }
    ':'         { TokColon          }
    '='         { TokEquals         }
    '{'         { TokLBrace         }
    '}'         { TokRBrace         }
    ';'         { TokSemicolon      }
    ')'         { TokRParen         }
    '|'         { TokPipe           }
    '@'         { TokAt             }
    '->'        { TokArrow          }
    'with'      { TokWith     $$    }

%%

PIdent :: { PIdent }
    : TIdent    { uncurry PIdent $1 }

Name :: { PName }
    : TIdent            { (fst $1, Ident (snd $1))      }
    | '(' Operator ')'  { (fst $2, Operator (snd $2))   }

with :: { () }
    : 'with' '{'   {% \_ -> lift $ modify (NoLayout  :) }
    | 'with' error {% \_ -> lift $ modify (Layout $1 :) }

Def :: { Def }
    : Name ':' Expr                                     { DefType $1 $3                                     }
    | Name Patterns '=' Expr                            { DefFun $1 (reverse $2) (Just $4)                  }
    | Name Patterns                                     { DefFun $1 (reverse $2) Nothing                    }
    | 'data' Name Teles                                 { DefData $2 (reverse $3) [] []                     }
    | 'data' Name Teles '=' Cons                        { DefData $2 (reverse $3) (reverse $5) []           }
    | 'data' Name Teles '=' Cons with FunClauses '}'    { DefData $2 (reverse $3) (reverse $5) (reverse $7) }
    | Import                                            { DefImport $1                                      }

Defs :: { [Def] }
    : {- empty -}   { []    }
    | Def           { [$1]  }
    | Defs ';'      { $1    }
    | Defs ';' Def  { $3:$1 }

FunClauses :: { [Clause] }
    : Name Patterns '=' Expr                { [Clause $1 (reverse $2) $4]       }
    | FunClauses ';'                        { $1                                }
    | FunClauses ';' Name Patterns '=' Expr { Clause $3 (reverse $4) $6 : $1    }

Pattern :: { PatternP }
    : PIdent                    { PatternVar $1                                 }
    | '(' ')'                   { PatternEmpty $1                               }
    | '(' PIdent Patterns ')'   { Pattern (PatternCon 0 0 $2 []) (reverse $3)   }

Patterns :: { [PatternP] }
    : {- empty -}       { []    }
    | Patterns Pattern  { $2:$1 }

Con :: { Con }
    : PIdent Teles  { ConDef $1 (reverse $2) } 

Cons :: { [Con] }
    : Con           { [$1]  } 
    | Cons '|' Con  { $3:$1 }

Tele :: { Tele }
    : Expr5                     { TypeTele $1                                                               }
    | '(' Exprs ':' Expr ')'    {% \_ -> mapM exprToVar $2 >>= \vars -> return (VarsTele (reverse vars) $4) }

Teles :: { [Tele] }
    : {- empty -}   { []    }
    | Teles Tele    { $2:$1 }

PiTele :: { PiTele }
    : '(' Exprs ':' Expr ')' { PiTele $1 (reverse $2) $4 }

PiTeles :: { [PiTele] }
    : PiTele            { [$1]  }
    | PiTeles PiTele    { $2:$1 }

PIdents :: { [PIdent] }
    : PIdent            { [$1]  }
    | PIdents PIdent    { $2:$1 }

Expr :: { RawExpr }
    : Expr1                     { $1                                                }
    | '\\' PIdents '->' Expr    { Apply ($1, Lam $ reverse $ map getName $2) [$4]   }

Expr1 :: { RawExpr }
    : Expr2                 { $1                                                    }
    | Expr2 '->' Expr1      { Apply (termPos $1, Pi []) [$1, $3]                    }
    | PiTeles '->' Expr1    {% \_ -> piExpr (reverse $1) $3                         }

Expr2 :: { RawExpr }
    : Expr3             { $1                                    }
    | Expr3 '=' Expr3   { Apply (termPos $1, PathImp) [$1,$3]   }

Expr3 :: { RawExpr }
    : Expr4             { $1                                }
    | Expr3 '@' Expr4   { Apply (termPos $1, At) [$1, $3]   }

Expr4 :: { RawExpr }
    : Exprs { let e:es = reverse $1 in apps e es }

Exprs :: { [RawExpr] }
    : Expr5         { [$1]  }
    | Exprs Expr5   { $2:$1 }

Expr5 :: { RawExpr }
    : Name          { Apply (fst $1, Name $ snd $1) []  }
    | '(' Expr ')'  { $2                                }

{
return' :: a -> Parser a
return' a _ = return a

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p k e = p e >>= \a -> k a e

data PiTele = PiTele Posn [RawExpr] RawExpr

piExpr :: [PiTele] -> RawExpr -> ParserErr RawExpr
piExpr [] term = return term
piExpr (PiTele pos t1 t2 : teles) term = do
    vars <- mapM exprToVar t1
    term' <- piExpr teles term
    return $ Apply (pos, Pi $ map getName vars) [t2,term']

termPos :: RawExpr -> Posn
termPos (Apply (pos, _) _) = pos
termPos _ = error "termPos"

exprToVar :: RawExpr -> ParserErr PIdent
exprToVar (Apply (pos, Name (Ident v)) []) = return (PIdent pos v)
exprToVar term = throwError [(termPos term, "Expected a list of identifiers")]

parseError :: Token -> Parser a
parseError tok (pos,_) = throwError [(maybe pos id (tokGetPos tok), "Syntax error")]

myLexer = alexScanTokens
}
