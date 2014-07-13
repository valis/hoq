module Syntax.Expr
    ( module Syntax.BNFC.AbsGrammar
    , getPos, argGetPos, parPatGetPos
    , unArg
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
getPos (PathImp e _) = getPos e
getPos (Interval (I (p,_))) = p
getPos (ELeft (PLeft (p,_))) = p
getPos (ERight (PRight (p,_))) = p
getPos (Path (PPath (p,_))) = p
getPos (PathCon (Ppath (p,_))) = p
getPos (At e _) = getPos e
getPos (Coe (PCoe (p,_))) = p
getPos (Iso (PIso (p,_))) = p
getPos (Squeeze (PSqueeze (p,_))) = p

argGetPos :: Arg -> (Int,Int)
argGetPos (Arg (PIdent (p,_))) = p
argGetPos (NoArg (Pus  (p,_))) = p

parPatGetPos :: Pattern -> (Int,Int)
parPatGetPos (PatVar arg) = argGetPos arg
parPatGetPos (PatEmpty (PPar (p,_))) = p
parPatGetPos (Pattern (PPar (p,_)) _) = p
parPatGetPos (PatLeft (PLeft (p,_))) = p
parPatGetPos (PatRight (PRight (p,_))) = p

unArg :: Arg -> String
unArg NoArg{} = "_"
unArg (Arg (PIdent (_,s))) = s
