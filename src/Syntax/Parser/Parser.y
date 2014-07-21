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
    Universe    { TokUniverse $$    }
    'I'         { TokInterval $$    }
    'left'      { TokLeft     $$    }
    'right'     { TokRight    $$    }
    'Path'      { TokPath     $$    }
    'path'      { Tokpath     $$    }
    'coe'       { TokCoe      $$    }
    'iso'       { TokIso      $$    }
    'squeeze'   { TokSqueeze  $$    }
    '\\'        { TokLam      $$    }
    '('         { TokLParen   $$    }
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
    'with'      { TokWith     $$    }

%%

with :: { () }
    : 'with' '{'   {% \_ -> lift $ modify (NoLayout  :) }
    | 'with' error {% \_ -> lift $ modify (Layout $1 :) }

Ident :: { String }
    : PIdent    { getName $1 }

Import :: { Import }
    : Ident             { [$1]  } 
    | Import '.' Ident  { $3:$1 }

Def :: { Def }
    : PIdent ':' Expr                                       { DefType $1 $3                                             }
    | PIdent Patterns '=' Expr                              { DefFun $1 (reverse $2) (Just $4)                          }
    | PIdent Patterns                                       { DefFun $1 (reverse $2) Nothing                            }
    | 'data' PIdent DataTeles                               {% \_ -> defData $2 (reverse $3) [] []                      }
    | 'data' PIdent DataTeles '=' Cons                      {% \_ -> defData $2 (reverse $3) (reverse $5) []            }
    | 'data' PIdent DataTeles '=' Cons with FunClauses '}'  {% \_ -> defData $2 (reverse $3) (reverse $5) (reverse $7)  }
    | 'import' Import                                       { DefImport $2                                              }

DataTeles :: { [(Expr,Expr)] }
    : {- empty -}                     { []              }
    | DataTeles '(' Expr ':' Expr ')' { ($3, $5) : $1   }

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
    | 'left'                    { PatternI $1 ILeft                             }
    | 'right'                   { PatternI $1 IRight                            }
    | '(' ')'                   { PatternEmpty $1                               }
    | '(' PIdent Patterns ')'   { Pattern (PatternCon 0 0 $2 []) (reverse $3)   }

Patterns :: { [PatternC Posn PIdent] }
    : {- empty -}       { []    }
    | Patterns Pattern  { $2:$1 }

Con :: { Con }
    : PIdent ConTeles { ConDef $1 (reverse $2) } 

Cons :: { [Con] }
    : Con           { [$1]  } 
    | Cons '|' Con  { $3:$1 }

ConTele :: { Tele Posn PIdent }
    : Expr5                 { TypeTele $1                                                   }
    | '(' Expr ':' Expr ')' {% \_ -> exprToVars $2 >>= \vars -> return (VarsTele vars $4)   }

ConTeles :: { [Tele Posn PIdent] }
    : {- empty -}       { []    }
    | ConTeles ConTele  { $2:$1 }

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
    : PIdent        { Var $1                                            }
    | Universe      { Universe (fst $1) $ maybe NoLevel Level (snd $1)  }
    | 'I'           { Interval $1                                       }
    | 'left'        { ICon $1 ILeft                                     }
    | 'right'       { ICon $1 IRight                                    }
    | 'Path'        { Path $1 Explicit Nothing []                       }
    | 'path'        { PCon $1 Nothing                                   }
    | 'coe'         { Coe $1 []                                         }
    | 'iso'         { Iso $1 []                                         }
    | 'squeeze'     { Squeeze $1 []                                     }
    | '(' Expr ')'  { $2                                                }

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
    go (PIdent pos x : vs) e = go vs $ Lam pos $ Scope1 x $ abstract1 (\(PIdent p a) -> if a == x then Just p else Nothing) e

type Expr = Term Posn PIdent
data PiTele = PiTele Posn Expr Expr

defData :: PIdent -> [(Expr,Expr)] -> [Con] -> [Clause] -> ParserErr Def
defData dt params cons conds = do
    params' <- forM params $ \(e1,e2) -> do
        vars <- exprToVars e1
        return (VarsTele vars e2)
    return (DefData dt params' cons conds)

piExpr :: [PiTele] -> Expr -> ParserErr Expr
piExpr [] term = return term
piExpr (PiTele pos e1 e2 : teles) term = do
    vars <- exprToVars e1
    term' <- piExpr teles term
    return $ Pi pos (Type e2 NoLevel) (mkScope (map getName vars) term') NoLevel

termPos :: Expr -> Posn
termPos = getAttr getPos

exprToVars :: Expr -> ParserErr [PIdent]
exprToVars term = fmap reverse (go term)
  where
    go (Var v) = return [v]
    go (App as (Var v)) = fmap (v:) (go as)
    go e = throwError [(termPos term, "Expected a list of identifiers")]

mkScope :: Functor f => [String] -> f PIdent -> Scope String Posn f PIdent
mkScope vars term = go vars
  where
    go [] = ScopeTerm term
    go (d:ds) = Scope d $ fmap (\a@(PIdent p v) -> if v == d then Bound p else Free a) (go ds)

parseError :: Token -> Parser a
parseError tok (pos,_) = throwError [(maybe pos id (tokGetPos tok), "Syntax error")]

myLexer = alexScanTokens
}
