module Syntax.Pattern where

data ICon = ILeft | IRight deriving Eq
data PatternCon = PatternCon Int Int [[Pattern]]
data Pattern = Pattern PatternCon [Pattern] | PatternVar | PatternI ICon
