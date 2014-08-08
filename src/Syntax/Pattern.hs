module Syntax.Pattern where

data ICon = ILeft | IRight deriving Eq
data PatternCon p c a = PatternCon Int Int a [([Pattern p c a], c)]
data Pattern p c a = Pattern (PatternCon p c a) [Pattern p c a] | PatternVar a | PatternI p ICon | PatternEmpty p

patternGetAttr :: (a -> p) -> Pattern p c a -> p
patternGetAttr f (Pattern (PatternCon _ _ a _) _) = f a
patternGetAttr f (PatternVar a) = f a
patternGetAttr _ (PatternI p _) = p
patternGetAttr _ (PatternEmpty p) = p

instance Show ICon where
    show ILeft  = "left"
    show IRight = "right"

instance Eq (PatternCon p c a) where
    PatternCon i _ _ _ == PatternCon i' _ _ _ = i == i'

instance Eq (Pattern p c a) where
    PatternI _ c   == PatternI _ c'  = c == c'
    PatternVar _   == PatternVar _   = True
    Pattern c _    == Pattern c' _   = c == c'
    PatternEmpty _ == PatternEmpty _ = True
    _              == _              = False

type Posn = (Int, Int)
data Name = Ident String | Operator String deriving Eq
type PName = (Posn, Name)

getStr :: Name -> String
getStr (Ident s) = s
getStr (Operator s) = s
