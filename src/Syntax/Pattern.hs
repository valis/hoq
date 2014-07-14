module Syntax.Pattern where

data ICon = ILeft | IRight deriving Eq
data PatternCon c a = PatternCon Int Int a [([Pattern c a], c)]
data Pattern c a = Pattern (PatternCon c a) [Pattern c a] | PatternVar a | PatternI ICon | PatternEmpty

instance Eq (PatternCon c a) where
    PatternCon i _ _ _ == PatternCon i' _ _ _ = i == i'

instance Eq (Pattern c a) where
    PatternI c   == PatternI c'  = c == c'
    PatternVar _ == PatternVar _ = True
    Pattern c _  == Pattern c' _ = c == c'
    PatternEmpty == PatternEmpty = True
    _            == _            = False
