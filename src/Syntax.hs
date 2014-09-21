module Syntax
    ( Syntax(..), Explicit(..)
    , RawExpr, PIdent(..)
    , Clause(..), Con(..), Field(..)
    , Import, Def(..), Tele(..)
    , Infix(..), Fixity(..)
    , Posn, Name(..), PName
    , nameToString, nameToInfix, nameToPrefix
    , module Syntax.Term
    ) where

import Data.Void

import Syntax.Term

data PIdent = PIdent { getPos :: Posn, getName :: String }
data Clause = Clause PName [Term PName Void] RawExpr
type Import = [String]
data Tele = VarsTele Explicit [PIdent] RawExpr | TypeTele Explicit RawExpr
data Con = ConDef PName [Tele]
data Field = Field PIdent RawExpr

data Infix = InfixL | InfixR | InfixNA deriving Eq
data Fixity = Infix Infix Int | Prefix deriving Eq

type Posn = (Int, Int)
data Name = Ident String | Operator String deriving Eq
type PName = (Posn, Name)

data Def
    = DefType PName RawExpr
    | DefFun PName [Term PName Void] (Maybe RawExpr)
    | DefData PName [Tele] [Con] [Clause]
    | DefRecord PName [Tele] (Maybe PName) [Field] [Clause]
    | DefImport Import
    | DefFixity Posn Infix Int [Name]

data Syntax
    = Lam [String]
    | Pi Explicit [String]
    | PathImp
    | At
    | Name Fixity Name
    | Case [Term PName String]
    | Null
    | Conds Int
    | FieldAcc PIdent

data Explicit = Explicit | Implicit deriving Eq

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

nameToString :: Name -> String
nameToString (Ident s) = s
nameToString (Operator s) = s

nameToInfix :: Name -> String
nameToInfix (Ident s) = "`" ++ s ++ "`"
nameToInfix (Operator s) = s

nameToPrefix :: Name -> String
nameToPrefix (Ident s) = s
nameToPrefix (Operator s) = "(" ++ s ++ ")"
