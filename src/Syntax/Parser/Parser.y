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

Pattern :: { PatternC Posn PIdent }
    : PIdent                        { PatternVar $1                                 }
    | posn 'left'                   { PatternI $1 ILeft                             }
    | posn 'right'                  { PatternI $1 IRight                            }
    | posn '(' ')'                  { PatternEmpty $1                               }
    | posn '(' PIdent Patterns ')'  { Pattern (PatternCon 0 0 $3 []) (reverse $4)   }

Patterns :: { [PatternC Posn PIdent] }
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
    : Expr1                         { $1            }
    | posn '\\' PIdents '->' Expr   { lam $1 $3 $5  }

Expr1 :: { Expr }
    : Expr2 { $1 }
    | Expr2 '->' Expr1      { Pi (getPos $1) (Type $1 NoLevel) (ScopeTerm $3) NoLevel   }
    | PiTeles '->' Expr1    {% \_ -> piExpr $1 $3                                       }

Expr2 :: { Expr }
    : Expr3             { $1                                        }
    | Expr3 '=' Expr3   { Path (getPos $1) Implicit Nothing [$1,$3] }

Expr3 :: { Expr }
    : Expr4             { $1                }
    | Expr3 '@' Expr4   { At Nothing $1 $3  }

Expr4 :: { Expr }
    : Expr5 { $1 }
    | Expr4 Expr5 { App $1 $2 } 

Expr5 :: { Expr }
    : PIdent            { Var $1                                }
    | posn Universe     { Universe $1 (maybe NoLevel Level $2)  }
    | posn 'I'          { Interval $1                           }
    | posn 'left'       { ICon $1 ILeft                         }
    | posn 'right'      { ICon $1 IRight                        }
    | posn 'Path'       { Path $1 Explicit Nothing []           }
    | posn 'path'       { PCon $1 Nothing                       }
    | posn 'coe'        { Coe $1 []                             }
    | posn 'iso'        { Iso $1 []                             }
    | posn 'squeeze'    { Squeeze $1 []                         }
    | posn '(' Expr ')' { $3                                    }

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
    go (v@(PIdent pos x) : vs) e = go vs $ Lam pos $ Scope1 x (abstract1 v e)

type Expr = Term Posn PIdent
data PiTele = PiTele Posn Expr Expr

piExpr :: [PiTele] -> Expr -> ParserErr Expr
piExpr [] term = return term
piExpr (PiTele pos e1 e2 : teles) term = do
    vars <- exprToVars e1
    term' <- piExpr teles term
    return $ Pi pos (Type e2 NoLevel) (mkScope (PIdent pos) vars term') NoLevel

getPos :: Term Posn PIdent -> Posn
getPos = getAttr $ \(PIdent pos _) -> pos

exprToVars :: Term Posn PIdent -> ParserErr [String]
exprToVars term = fmap reverse (go term)
  where
    go (Var (PIdent _ v)) = return [v]
    go (App as (Var (PIdent _ v))) = fmap (v:) (go as)
    go e = throwError [(getPos term, "Expected a list of identifiers")]

mkScope :: (Functor f, Eq a) => (s -> a) -> [s] -> f a -> Scope s f a
mkScope f vars term = go vars $ map f (reverse vars)
  where
    go [] [] = ScopeTerm term
    go (d:ds) (r:rs) = Scope d $ fmap (\a -> if a == r then Bound else Free a) (go ds rs)

parseError :: Token -> Parser a
parseError _ (pos,_) = throwError [(pos, "Syntax error")]

myLexer = alexScanTokens
}
