module TypeChecking.Hole where

import Control.Applicative

import Syntax.Term
import Syntax.ErrorDoc
import qualified Syntax.Expr as E

data MaybeTerm h = JustTerm (Term h) | JustExpr E.Expr | JustStr String | NoTerm
data Hole h a = Hole [EMsg Term] (MaybeTerm h) | NoHole a

instance Eq a => Eq (Hole a) where
    NoHole a == NoHole a' = a == a'
    _        == _         = False

instance Functor MaybeTerm where
    fmap f (JustTerm t)    = JustTerm (fmap f t)
    fmap _ (JustExpr expr) = JustExpr expr
    fmap _ (JustStr str)   = JustStr str
    fmap _ NoTerm          = NoTerm

instance Functor (Hole h) where
    fmap f (NoHole a)     = NoHole (f a)
    fmap _ (Hole errs mt) = Hole errs mt

instance Applicative Hole where
    pure = NoHole
    NoHole f     <*> NoHole a     = NoHole (f a)
    NoHole _     <*> Hole errs  _ = Hole errs NoTerm
    Hole errs  _ <*> NoHole _     = Hole errs NoTerm
    Hole errs1 _ <*> Hole errs2 _ = Hole (errs1 ++ errs2) NoTerm

instance Monad Hole where
    return = NoHole
    NoHole a     >>= k = k a
    Hole errs mt >>= _ = Hole errs mt

instance Pretty h Term => Pretty (MaybeTerm h) Term where
    pretty (JustTerm t) = epretty (fmap pretty t)
    pretty (JustExpr e) = pretty (printTree e)
    pretty (JustStr  s) = pretty s
    pretty NoTerm       = enull

instance (Pretty h Term, Pretty a Term) => Pretty (Hole h a) Term where
    pretty (NoHole a)  = pretty a
    pretty (Hole _ mt) = pretty "{#Error" <+> pretty mt <+> pretty "#}"
