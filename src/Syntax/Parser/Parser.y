--
{
module Syntax.Parser.Parser
    ( pDefs, pExpr
    ) where

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Error
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
    PIdent      { TokIdent    $$    }
    Import      { TokImport   $$    }
    Operator    { TokOperator $$    }
    Infix       { TokInfix    $$    }
    Integer     { TokInteger  $$    }
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
    '`'         { TokApos           }
    '->'        { TokArrow          }
    'with'      { TokWith     $$    }

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

with :: { () }
    : 'with' '{'   {% \_ -> lift $ modify (\(ls, fds) -> (NoLayout  : ls, fds)) }
    | 'with' error {% \_ -> lift $ modify (\(ls, fds) -> (Layout $1 : ls, fds)) }

Def :: { [Def] }
    : Name ':' Expr                                     { [DefType $1 $3]                                       }
    | Name Patterns '=' Expr                            { [DefFun $1 (reverse $2) (Just $4)]                    }
    | Name Patterns                                     { [DefFun $1 (reverse $2) Nothing]                      }
    | 'data' Name Teles                                 { [DefData $2 (reverse $3) [] []]                       }
    | 'data' Name Teles '=' Cons                        { [DefData $2 (reverse $3) (reverse $5) []]             }
    | 'data' Name Teles '=' Cons with FunClauses '}'    { [DefData $2 (reverse $3) (reverse $5) (reverse $7)]   }
    | Infix Integer InfixOps                            {% \_ -> fixityDecl $1 $2 $3 >> return []               }
    | Import                                            { [DefImport $1]                                        }

Defs :: { [Def] }
    : {- empty -}   { []        }
    | Def           { $1        }
    | Defs ';'      { $1        }
    | Defs ';' Def  { $3 ++ $1  }

FunClauses :: { [Clause] }
    : Name Patterns '=' Expr                { [Clause $1 (reverse $2) $4]       }
    | FunClauses ';'                        { $1                                }
    | FunClauses ';' Name Patterns '=' Expr { Clause $3 (reverse $4) $6 : $1    }

Pattern :: { Term PName Void }
    : PIdent                    { Apply (getPos $1, Ident $ getName $1) []                                 }
    | '(' ')'                   { Apply ($1, Operator "") []                              }
    | '(' PIdent Patterns ')'   { Apply (getPos $2, Ident $ getName $2) (reverse $3)   }

Patterns :: { [Term PName Void] }
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
    : ExprT { treeToExpr $1 }

ExprT :: { Tree }
    : Expr4                 { Leaf $1                                                                           }
    | ExprT '@' Expr4       {% \_ -> branch (Infix InfixL 90) At $1 (Leaf $3)                                   }
    | ExprT InfixOp Expr4   {% \_ -> getInfixOp (snd $2) >>= \ft -> branch ft (Name ft $ snd $2) $1 (Leaf $3)   }

Expr4 :: { RawExpr }
    : Exprs { let e:es = reverse $1 in apps e es }

Exprs :: { [RawExpr] }
    : Expr5         { [$1]  }
    | Exprs Expr5   { $2:$1 }

Expr5 :: { RawExpr }
    : Name          { Apply (fst $1, Name Prefix $ snd $1) []   }
    | '(' Expr ')'  { $2                                        }

{
return' :: a -> Parser a
return' a _ = return a

bind :: Parser a -> (a -> Parser b) -> Parser b
bind p k e = p e >>= \a -> k a e

data Tree = Branch Fixity Syntax Tree Tree | Leaf RawExpr

branch :: Fixity -> Syntax -> Tree -> Tree -> ParserErr Tree
branch ft@(Infix ia p) name (Branch ft'@(Infix ia' p') name' a1 a2) b | p' < p || p == p' && ia == InfixR && ia' == InfixR = do
    a2' <- branch ft name a2 b
    return (Branch ft' name' a1 a2')
branch ft@(Infix ia p) name a@(Branch ft'@(Infix ia' p') name' _ _) b | p == p' && not (ia == InfixL && ia' == InfixL) = do
    let showOp ft'' name'' = syntaxToString name'' ++ " [" ++ show ft'' ++ "]"
        msg = "Precedence parsing error: cannot mix " ++ showOp ft  name ++
                                              " and " ++ showOp ft' name' ++ " in the same infix expression"
    warn [(termPos $ treeToExpr a, msg)]
    return (Branch ft name a b)
  where
    syntaxToString :: Syntax -> String
    syntaxToString Lam{} = "\\"
    syntaxToString Pi{} = "->"
    syntaxToString PathImp = "="
    syntaxToString At = "@"
    syntaxToString (Name _ (Ident s)) = "`" ++ s ++ "`"
    syntaxToString (Name _ (Operator s)) = s
branch ft name a b = return (Branch ft name a b)

treeToExpr :: Tree -> RawExpr
treeToExpr (Leaf e) = e
treeToExpr (Branch ft name a b) =
    let a' = treeToExpr a
    in Apply (termPos a', name) [a', treeToExpr b]

data PiTele = PiTele Posn [RawExpr] RawExpr

piExpr :: [PiTele] -> RawExpr -> ParserErr RawExpr
piExpr [] term = return term
piExpr (PiTele pos t1 t2 : teles) term = do
    vars <- mapM exprToVar t1
    term' <- piExpr teles term
    return $ Apply (pos, Pi $ map getName vars) [t2,term']

fixityDecl :: (Posn, Infix) -> (Posn, Int) -> [PName] -> ParserErr ()
fixityDecl (pos, fd) (_, pr) names = forM_ names $ \(_,name) -> do
    (ls, fds) <- lift get
    case lookup name fds of
        Just _  -> warn [(pos, "Multiple fixity declarations for " ++ show (getStr name))]
        Nothing -> return ()
    lift $ put (ls, (name, Infix fd pr):fds)

getInfixOp :: Name -> ParserErr Fixity
getInfixOp name = do
    (_,fds) <- lift get
    return $ fromMaybe (Infix InfixL 90) (lookup name fds)

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
