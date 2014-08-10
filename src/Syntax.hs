module Syntax
    ( Syntax(..)
    , RawExpr, PIdent(..)
    , Clause(..), Con(..)
    , Import, Def(..), Tele(..)
    , Infix(..), Fixity(..)
    , module Syntax.Term, module Syntax.Pattern
    ) where

import Data.Void

import Syntax.Term
import Syntax.Pattern

data PIdent = PIdent { getPos :: Posn, getName :: String }
data Clause = Clause PName [Term PName Void] RawExpr
type Import = [String]
data Tele = VarsTele [PIdent] RawExpr | TypeTele RawExpr
data Con = ConDef PIdent [Tele]
data Infix = InfixL | InfixR | InfixNA deriving Eq
data Fixity = Infix Infix Int | Prefix deriving Eq

data Def
    = DefType PName RawExpr
    | DefFun PName [Term PName Void] (Maybe RawExpr)
    | DefData PName [Tele] [Con] [Clause]
    | DefImport Import

data Syntax
    = Lam [String]
    | Pi [String]
    | PathImp
    | At
    | Name Fixity Name

type RawExpr = Term (Posn, Syntax) Void

instance Eq PIdent where
    PIdent _ s == PIdent _ s' = s == s'

instance Show Infix where
    show InfixL = "infixl"
    show InfixR = "infixr"
    show InfixNA = "infix"

instance Show Fixity where
    show (Infix ia p) = show ia ++ " " ++ show p
    show Prefix = "prefix"
