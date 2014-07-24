--
{
module Syntax.Parser.Parser
    ( pDefs, pExpr
    ) where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Error

import Syntax.Parser.Lexer
import Syntax.Term
}

%name pDefs Defs
%name pExpr Expr
%tokentype { Token }
%error { parseError }
%monad { Parser } { bind } { return' }
%lexer { alexScanTokens } { TokEOF }

%token
    PIdent      { TokIdent    $$    }
    Import      { TokImport   $$    }
    '\\'        { TokLam      $$    }
    '('         { TokLParen   $$    }
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
    'with'      { TokWith     $$    }

%%

with :: { () }
    : 'with' '{'   {% \_ -> lift $ modify (NoLayout  :) }
    | 'with' error {% \_ -> lift $ modify (Layout $1 :) }

Def :: { Def }
    : PIdent ':' Expr                                   { DefType $1 $3                                     }
    | PIdent Patterns '=' Expr                          { DefFun $1 (reverse $2) (Just $4)                  }
    | PIdent Patterns                                   { DefFun $1 (reverse $2) Nothing                    }
    | 'data' PIdent Teles                               { DefData $2 (reverse $3) [] []                     }
    | 'data' PIdent Teles '=' Cons                      { DefData $2 (reverse $3) (reverse $5) []           }
    | 'data' PIdent Teles '=' Cons with FunClauses '}'  { DefData $2 (reverse $3) (reverse $5) (reverse $7) }
    | Import                                            { DefImport $1                                      }

Defs :: { [Def] }
    : {- empty -}   { []    }
    | Def           { [$1]  }
    | Defs ';'      { $1    }
    | Defs ';' Def  { $3:$1 }

FunClauses :: { [Clause] }
    : PIdent Patterns '=' Expr                  { [Clause $1 (reverse $2) $4]       }
    | FunClauses ';'                            { $1                                }
    | FunClauses ';' PIdent Patterns '=' Expr   { Clause $3 (reverse $4) $6 : $1    }

Pattern :: { PatternC Posn PIdent }
    : PIdent                    { PatternVar $1                                 }
    | '(' ')'                   { PatternEmpty $1                               }
    | '(' PIdent Patterns ')'   { Pattern (PatternCon 0 0 $2 []) (reverse $3)   }

Patterns :: { [PatternC Posn PIdent] }
    : {- empty -}       { []    }
    | Patterns Pattern  { $2:$1 }

Con :: { Con }
    : PIdent Teles  { ConDef $1 (reverse $2) } 

Cons :: { [Con] }
    : Con           { [$1]  } 
    | Cons '|' Con  { $3:$1 }

Tele :: { Tele Posn PIdent }
    : Expr5                 { TypeTele $1                                                   }
    | '(' Expr ':' Expr ')' {% \_ -> exprToVars $2 >>= \vars -> return (VarsTele vars $4)   }

Teles :: { [Tele Posn PIdent] }
    : {- empty -}   { []    }
    | Teles Tele    { $2:$1 }

PiTele :: { PiTele }
    : '(' Expr ':' Expr ')' { PiTele $1 $2 $4 }

PiTeles :: { [PiTele] }
    : PiTele            { [$1]  }
    | PiTeles PiTele    { $2:$1 }

PIdents :: { [PIdent] }
    : PIdent            { [$1]  }
    | PIdents PIdent    { $2:$1 }

Expr :: { Expr }
    : Expr1                     { $1            }
    | '\\' PIdents '->' Expr    { lam $1 $2 $4  }

Expr1 :: { Expr }
    : Expr2 { $1 }
    | Expr2 '->' Expr1      { Pi (termPos $1) (Type $1 NoLevel) (ScopeTerm $3) NoLevel  }
    | PiTeles '->' Expr1    {% \_ -> piExpr (reverse $1) $3                             }

Expr2 :: { Expr }
    : Expr3             { $1                                            }
    | Expr3 '=' Expr3   { Path (termPos $1) Implicit Nothing [$1,$3]    }

Expr3 :: { Expr }
    : Expr4             { $1                }
    | Expr3 '@' Expr4   { At Nothing $1 $3  }

Expr4 :: { Expr }
    : Expr5         { $1        }
    | Expr4 Expr5   { App $1 $2 }

Expr5 :: { Expr }
    : PIdent        { Var $1    }
    | '(' Expr ')'  { $2        }

{
return' :: a -> Parser a
return' a _ = return a

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p k e = p e >>= \a -> k a e

lam :: Posn -> [PIdent] -> Expr -> Expr
lam pos vars term = case go vars term of
    Lam _ s -> Lam pos s
    term' -> term'
  where
    go [] e = e
    go (PIdent pos x : vs) e = go vs $ Lam pos $ Scope1 x (fmap Free e)

type Expr = Term Posn PIdent
data PiTele = PiTele Posn Expr Expr

piExpr :: [PiTele] -> Expr -> ParserErr Expr
piExpr [] term = return term
piExpr (PiTele pos e1 e2 : teles) term = do
    vars <- exprToVars e1
    term' <- piExpr teles term
    return $ Pi pos (Type e2 NoLevel) (go (map getName vars) $ ScopeTerm term') NoLevel
  where
    go :: [String] -> Scope String Posn (Term Posn) PIdent -> Scope String Posn (Term Posn) PIdent
    go [] scope = scope
    go (d:ds) scope = Scope d $ fmap Free (go ds scope)

termPos :: Expr -> Posn
termPos = getAttr getPos

exprToVars :: Expr -> ParserErr [PIdent]
exprToVars term = fmap reverse (go term)
  where
    go (Var v) = return [v]
    go (App as (Var v)) = fmap (v:) (go as)
    go e = throwError [(termPos term, "Expected a list of identifiers")]

parseError :: Token -> Parser a
parseError tok (pos,_) = throwError [(maybe pos id (tokGetPos tok), "Syntax error")]

myLexer = alexScanTokens
}