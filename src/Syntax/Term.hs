module Syntax.Term
    ( Term(..)
    ) where

import Bound
import Bound.Name

data Level = Level Int | NoLevel

level :: Level -> Int
level (Level n) = n
level NoLevel = 0

data Term a
    = Var a
    | App (Term a) (Term a)
    | Lam (Scope (Name String Int) Term a)
    | Arr (Term a) (Term a)
    | Pi (Term a) (Scope (Name String Int) Term a)
    | Universe Level
