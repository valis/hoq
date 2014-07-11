module Syntax.Pattern where

data ICon = ILeft | IRight deriving Eq
data PatternCon c = PatternCon Int Int String [([Pattern c], c)]
data Pattern c = Pattern (PatternCon c) [Pattern c] | PatternVar String | PatternI ICon

instance Eq (PatternCon c) where
    PatternCon i _ _ _ == PatternCon i' _ _ _ = i == i'

instance Eq (Pattern c) where
    PatternI c   == PatternI c'  = c == c'
    PatternVar _ == PatternVar _ = True
    Pattern c _  == Pattern c' _ = c == c'
    _            == _            = False
