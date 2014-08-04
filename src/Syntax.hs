module Syntax
    ( Syntax(..), PatternP
    , RawExpr, Posn, PIdent(..)
    , Clause(..), Con(..)
    , Import, Def(..), Tele(..)
    , module Syntax.Term, module Syntax.Pattern
    ) where

import Data.Void

import Syntax.Term
import Syntax.Pattern

type Posn = (Int, Int)
data PIdent = PIdent { getPos :: Posn, getName :: String }
data Clause = Clause PIdent [PatternP PIdent] RawExpr
type Import = [String]
data Tele = VarsTele [PIdent] RawExpr | TypeTele RawExpr
data Con = ConDef PIdent [Tele]
type PatternP = Pattern Posn (Closed (Term (Posn, Syntax)))

data Def
    = DefType PIdent RawExpr
    | DefFun PIdent [PatternP PIdent] (Maybe RawExpr)
    | DefData PIdent [Tele] [Con] [Clause]
    | DefImport Import

data Syntax
    = App
    | Lam [String]
    | Pi [String]
    | PathImp
    | At
    | Ident String

type RawExpr = Term (Posn, Syntax) Void

instance Eq PIdent where
    PIdent _ s == PIdent _ s' = s == s'
