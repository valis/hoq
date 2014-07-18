module Syntax.Pattern where

data ICon = ILeft | IRight deriving Eq
data PatternCon p c a = PatternCon Int Int a [([Pattern p c a], c)]
data Pattern p c a = Pattern (PatternCon p c a) [Pattern p c a] | PatternVar a | PatternI p ICon | PatternEmpty p

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
