module Syntax.Expr
    ( module Syntax.BNFC.AbsGrammar
    , getPos
    , unArg, unCons
    ) where

import Syntax.BNFC.AbsGrammar

getPos :: Expr -> (Int,Int)
getPos (Lam (PLam (p,_)) _ _) = p
getPos (Arr e _) = getPos e
getPos (Pi [] e) = getPos e
getPos (Pi (PiTele (PPar (p,_)) _ _ : _) _) = p
getPos (App e _) = getPos e
getPos (Var (Arg (PIdent (p,_)))) = p
getPos (Var (NoArg (Pus (p,_)))) = p
getPos (Universe (U (p,_))) = p
getPos (Paren (PPar (p,_)) _) = p

unArg :: Arg -> String
unArg NoArg{} = "_"
unArg (Arg (PIdent (_,s))) = s

unCons :: Cons -> [Con]
unCons NoCons = []
unCons (Cons cons) = cons
