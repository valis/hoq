--
{
module Syntax.Parser.Parser
    ( pDefs, pExpr
    ) where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Error
import Data.Bifunctor
import Data.Void
import Data.Maybe

import Syntax.Parser.Lexer
import Syntax
import TypeChecking.Monad.Warn
}

%name pDefs Defs
%name pExpr Expr
%tokentype { Token }
%error { parseError }
%monad { Parser } { bind } { return' }
%lexer { alexScanTokens } { TokEOF }

%token
    PIdent          { TokIdent    $$    }
    Import          { TokImport   $$    }
    Operator        { TokOperator $$    }
    Infix           { TokInfix    $$    }
    Integer         { TokInteger  $$    }
    FieldAcc        { TokField    $$    }
    '\\'            { TokLam      $$    }
    '('             { TokLParen   $$    }
    'case'          { TokCase     $$    }
    'of'            { TokOf       $$    }
    'data'          { TokData           }
    'record'        { TokRecord         }
    'constructor'   { TokConstructor    }
    'where'         { TokWhere    $$    }
    ':'             { TokColon          }
    '='             { TokEquals         }
    '{'             { TokLBrace   $$    }
    '}'             { TokRBrace         }
    ';'             { TokSemicolon      }
    ')'             { TokRParen         }
    '|'             { TokPipe           }
    '@'             { TokAt             }
    '`'             { TokApos           }
    '->'            { TokArrow          }
    'with'          { TokWith     $$    }

%%

Name :: { PName }
    : PIdent            { (getPos $1, Ident (getName $1))       }
    | '(' Operator ')'  { (getPos $2, Operator (getName $2))    }

InfixOp :: { PName }
    : Operator          { (getPos $1, Operator (getName $1))    }
    | '`' PIdent '`'    { (getPos $2, Ident (getName $2))       }

InfixOps :: { [PName] }
    : InfixOp           { [$1]  }
    | InfixOps InfixOp  { $2:$1 }

LBrace :: { Posn }
    : '{'           {% \_ -> lift  (modify (NoLayout :)) >> return $1 }

with :: { () }
    : 'with' '{'    {% \_ -> lift $ modify (NoLayout  :) }
    | 'with' error  {% \_ -> lift $ modify (Layout $1 :) }

where :: { () }
    : 'where' '{'   {% \_ -> lift $ modify (NoLayout  :) }
    | 'where' error {% \_ -> lift $ modify (Layout $1 :) }

of :: { () }
    : 'of' '{'      {% \_ -> lift $ modify (NoLayout  :) }
    | 'of' error    {% \_ -> lift $ modify (Layout $1 :) }

Def :: { Def }
    : Name ':' Expr                                     { DefType $1 $3                                     }
    | Name Patterns '=' Expr                            { DefFun $1 (reverse $2) (Just $4)                  }
    | Name Patterns                                     { DefFun $1 (reverse $2) Nothing                    }
    | 'data' Name Teles                                 { DefData $2 (reverse $3) [] []                     }
    | 'data' Name Teles '=' Cons MaybeFunClauses        { DefData $2 (reverse $3) (reverse $5) $6           }
    | 'record' Name Teles where
        MaybeConstructor Fields '}' MaybeFunClauses     { DefRecord $2 (reverse $3) $5 (reverse $6) $8      }
    | Infix Integer InfixOps                            { DefFixity (fst $1) (snd $1) (snd $2) (map snd $3) }
    | Import                                            { DefImport $1 }

Defs :: { [Def] }
    : {- empty -}   { []    }
    | Def           { [$1]  }
    | Defs ';'      { $1    }
    | Defs ';' Def  { $3:$1 }

MaybeConstructor :: { Maybe PName }
    : {- empty -}           { Nothing   }
    | 'constructor' Name    { Just $2   }

Fields :: { [Field] }
    : {- empty -}       { []    }
    | Field             { [$1]  }
    | Fields ';'        { $1    }
    | Fields ';' Field  { $3:$1 }

Field :: { Field }
    : PIdent ':' Expr { Field $1 $3 }

MaybeFunClauses :: { [Clause] }
    : {- empty -}           { []            }
    | with FunClauses '}'   { reverse $2    }

FunClauses :: { [Clause] }
    : Name Patterns '=' Expr                { [Clause $1 (reverse $2) $4]       }
    | FunClauses ';'                        { $1                                }
    | FunClauses ';' Name Patterns '=' Expr { Clause $3 (reverse $4) $6 : $1    }

Pattern :: { Term PName Void }
    : Name                  { Apply (fst $1, snd $1) []             }
    | '(' ')'               { Apply ($1, Operator "") []            }
    | '(' Name Patterns ')' { Apply (fst $2, snd $2) (reverse $3)   }

Patterns :: { [Term PName Void] }
    : {- empty -}       { []    }
    | Patterns Pattern  { $2:$1 }

Con :: { Con }
    : Name Teles  { ConDef $1 (reverse $2) } 

Cons :: { [Con] }
    : Con           { [$1]  } 
    | Cons '|' Con  { $3:$1 }

Tele :: { Tele }
    : Expr5                     { TypeTele Explicit $1                                                               }
    | LBrace Expr5 '}'          { TypeTele Implicit $2                                                               }
    | '(' Exprs ':' Expr ')'    {% \_ -> mapM exprToVar $2 >>= \vars -> return (VarsTele Explicit (reverse vars) $4) }
    | LBrace Exprs ':' Expr '}' {% \_ -> mapM exprToVar $2 >>= \vars -> return (VarsTele Implicit (reverse vars) $4) }

Teles :: { [Tele] }
    : {- empty -}   { []    }
    | Teles Tele    { $2:$1 }

PiTele :: { (Explicit,PiTele) }
    : '(' Exprs ':' Expr ')'    { (Explicit, PiTele $1 (reverse $2) $4) }
    | LBrace Exprs ':' Expr '}' { (Implicit, PiTele $1 (reverse $2) $4) }

PiTeles :: { [(Explicit,PiTele)] }
    : PiTele            { [$1]  }
    | PiTeles PiTele    { $2:$1 }

PIdents :: { [PIdent] }
    : PIdent            { [$1]  }
    | PIdents PIdent    { $2:$1 }

Expr :: { RawExpr }
    : Expr1                     { $1                                                }
    | '\\' PIdents '->' Expr    { Apply ($1, Lam $ reverse $ map getName $2) [$4]   }

Expr1 :: { RawExpr }
    : Expr2                 { $1                                            }
    | Expr2 '->' Expr1      { Apply (termPos $1, Pi Explicit []) [$1, $3]   }
    | PiTeles '->' Expr1    {% \_ -> piExpr (reverse $1) $3                 }

Expr2 :: { RawExpr }
    : Expr3             { $1                                    }
    | Expr3 '=' Expr3   { Apply (termPos $1, PathImp) [$1,$3]   }

Expr3 :: { RawExpr }
    : Expr4                 { Apply (termPos $1, Null) [$1]                                 }
    | Expr3 '@' Expr4       { Apply (termPos $1, At) [$1, $3]                               }
    | Expr3 InfixOp Expr4   { Apply (termPos $1, Name (Infix InfixL 90) $ snd $2) [$1, $3]  }

Expr4 :: { RawExpr }
    : Exprs                 { let e:es = reverse $1 in apps e es }
    | Expr4 FieldAcc EExprs { Apply (termPos $1, FieldAcc $2) ($1 : reverse $3) }

EExprs :: { [RawExpr] }
    : {- empty -}   { []  }
    | EExprs Expr5  { $2:$1 }

Exprs :: { [RawExpr] }
    : Expr5         { [$1]  }
    | Exprs Expr5   { $2:$1 }

Expr5 :: { RawExpr }
    : Name                              { Apply (fst $1, Name Prefix $ snd $1) []                                   }
    | '(' Expr ')'                      { $2                                                                        }
    | 'case' Expr of CaseClauses '}'    { Apply ($1, Case $ map vacuous $ reverse $ fst $4) ($2 : reverse (snd $4)) }

CaseClauses :: { ([Term PName Void], [RawExpr]) }
    : Name Patterns '->' Expr                   { ([Apply $1 $2], [$4])                 }
    | CaseClauses ';'                           { $1                                    }
    | CaseClauses ';' Name Patterns '->' Expr   { (Apply $3 $4 : fst $1, $6 : snd $1)   }

{
return' :: a -> Parser a
return' a _ = return a

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p k e = p e >>= \a -> k a e

data PiTele = PiTele Posn [RawExpr] RawExpr

piExpr :: [(Explicit,PiTele)] -> RawExpr -> ParserErr RawExpr
piExpr [] term = return term
piExpr ((e, PiTele pos t1 t2) : teles) term = do
    vars <- mapM exprToVar t1
    term' <- piExpr teles term
    return $ Apply (pos, Pi e $ map getName vars) [t2,term']

termPos :: RawExpr -> Posn
termPos (Apply (pos, _) _) = pos
termPos _ = error "termPos"

exprToVar :: RawExpr -> ParserErr PIdent
exprToVar (Apply (pos, Name Prefix (Ident v)) []) = return (PIdent pos v)
exprToVar term = throwError [(termPos term, "Expected a list of identifiers")]

parseError :: Token -> Parser a
parseError tok (pos,_) = throwError [(maybe pos id (tokGetPos tok), "Syntax error")]

myLexer = alexScanTokens
}
