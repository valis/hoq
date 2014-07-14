--
{
module Syntax.Parser.Parser
    ( pModule, pExpr
    ) where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Error

import Syntax.Parser.Lexer
import Syntax.Term
}

%name pModule Module
%name pExpr Expr
%tokentype { Token }
%error { parseError }
%monad { Parser } { bind } { return' }
%lexer { alexScanTokens } { TokEOF }

%token
    Ident       { TokIdent $$       }
    Universe    { TokUniverse $$    }
    'I'         { TokInterval       }
    'left'      { TokLeft           }
    'right'     { TokRight          }
    'Path'      { TokPath           }
    'path'      { Tokpath           }
    'coe'       { TokCoe            }
    'iso'       { TokIso            }
    'squeeze'   { TokSqueeze        }
    '\\'        { TokLam            }
    '('         { TokLParen         }
    'import'    { TokImport         }
    'data'      { TokData           }
    ':'         { TokColon          }
    '='         { TokEquals         }
    '{'         { TokLBrace         }
    '}'         { TokRBrace         }
    ';'         { TokSemicolon      }
    '.'         { TokDot            }
    ')'         { TokRParen         }
    '|'         { TokPipe           }
    '@'         { TokAt             }
    '->'        { TokArrow          }
    'with'      { TokWith           }

%%

open :: { () }
    : '{'   {% \_ -> lift $ modify (NoLayout :)             }
    | error {% \(Posn _ c, _) -> lift $ modify (Layout c :) }

close :: { () }
    : '}'   { () }

posn :: { Posn }
    : {- empty -}   {% \(pos,_) -> return pos }

PIdent :: { PIdent }
    : posn Ident    { PIdent $1 $2 }

Module :: { Module }
    : Imports Defs { Module (reverse $1) (reverse $2) } 

Imports :: { [Import] }
    : {- empty -}                   { []                } 
    | Imports 'import' Import ';'   { $3 : reverse $1   }

Import :: { Import }
    : Ident             { [$1] } 
    | Import '.' Ident  { $3 : $1 }

Def :: { Def }
    : PIdent ':' Expr                                               { DefType $1 $3                                     }
    | PIdent Patterns '=' Expr                                      { DefFun $1 $2 (Just $4)                            }
    | PIdent Patterns                                               { DefFun $1 $2 Nothing                              }
    | 'data' PIdent DataTeles                                       { DefData $2 (reverse $3) [] []                     }
    | 'data' PIdent DataTeles '=' Cons                              { DefData $2 (reverse $3) (reverse $5) []           }
    | 'data' PIdent DataTeles '=' Cons 'with' open FunClauses close { DefData $2 (reverse $3) (reverse $5) (reverse $8) }

DataTeles :: { [(Expr,Expr)] }
    : {- empty -}                     { []              }
    | DataTeles '(' Expr ':' Expr ')' { ($3, $5) : $1   }

Defs :: { [Def] }
    : {- empty -}   { []    }
    | Def           { [$1]  }
    | Defs ';' Def  { $3:$1 }

FunClauses :: { [Clause] }
    : PIdent Patterns '=' Expr                  { [Clause $1 $2 $4]     }
    | FunClauses ';' PIdent Patterns '=' Expr   { Clause $3 $4 $6 : $1  }

Pattern :: { PatternC' (Attr Posn PatternC' PIdent) }
    : PIdent                        { PatternVar (AttrVar $1)                               }
    | posn 'left'                   { PatternVar (Attr $1 $ PatternI ILeft)                 }
    | posn 'right'                  { PatternVar (Attr $1 $ PatternI IRight)                }
    | posn '(' ')'                  { PatternVar (Attr $1 PatternEmpty)                     }
    | posn '(' PIdent Patterns ')'  { Pattern (PatternCon 0 0 (AttrVar $3) []) (reverse $4) }

Patterns :: { [PatternC' (Attr Posn PatternC' PIdent)] }
    : {- empty -}       { []    }
    | Patterns Pattern  { $2:$1 }

Con :: { Con }
    : PIdent ConTeles { ConDef $1 (reverse $2) } 

Cons :: { [Con] }
    : Con { [$1] } 
    | Cons '|' Con { $3:$1 }

ConTele :: { ConTele }
    : Expr5                         { TypeTele $1       }
    | posn '(' Expr ':' Expr ')'    { VarsTele $3 $5    }

ConTeles :: { [ConTele] }
    : {- empty -}       { []    }
    | ConTeles ConTele  { $2:$1 }

PiTele :: { PiTele }
    : posn '(' Expr ':' Expr ')' { PiTele $1 $3 $5 } 

PiTeles :: { [PiTele] }
    : PiTele            { [$1]  }
    | PiTeles PiTele    { $2:$1 }

PIdents :: { [PIdent] }
    : PIdent            { [$1]  }
    | PIdents PIdent    { $2:$1 }

Expr :: { Expr }
    : Expr1                         { $1                                                    }
    | posn '\\' PIdents '->' Expr   { Var $ Attr $1 $5 {- TODO: (Lam (reverse $3) $5) -}    }

Expr1 :: { Expr }
    : Expr2 { $1 }
    | Expr2 '->' Expr1      { Pi (Type $1 NoLevel) (ScopeTerm $3) NoLevel   } 
    | PiTeles '->' Expr1    { {- TODO: Pi $1 -} $3                          }

Expr2 :: { Expr }
    : Expr3             { $1                            }
    | Expr3 '=' Expr3   { Path Implicit Nothing [$1,$3] }

Expr3 :: { Expr }
    : Expr4             { $1                }
    | Expr3 '@' Expr4   { At Nothing $1 $3  }

Expr4 :: { Expr }
    : Expr5 { $1 }
    | Expr4 Expr5 { App $1 $2 } 

Expr5 :: { Expr }
    : posn Ident        { Var $ Attr $1 $ Var (AttrVar $2)  }
    | Universe          { Universe (maybe NoLevel Level $1) }
    | 'I'               { Interval                          }
    | 'left'            { ICon ILeft                        }
    | 'right'           { ICon IRight                       }
    | 'Path'            { Path Explicit Nothing []          }
    | 'path'            { PCon Nothing                      }
    | 'coe'             { Coe []                            }
    | 'iso'             { Iso []                            }
    | 'squeeze'         { Squeeze []                        }
    | posn '(' Expr ')' { Var (Attr $1 $3)                  }

{
return' :: a -> Parser a
return' a _ = return a

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p k e = p e >>= \a -> k a e

parseError :: Token -> Parser a
parseError _ (pos,_) = throwError [(pos, "Syntax error")]

myLexer = alexScanTokens
}
