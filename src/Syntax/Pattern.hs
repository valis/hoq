module Syntax.Pattern where

data ICon = ILeft | IRight deriving Eq
data PatternCon = PatternCon Int Int String [[Pattern]]
data Pattern = Pattern PatternCon [Pattern] | PatternVar String | PatternI ICon

infix 4 `cmpPatternCon`, `cmpPattern`

cmpPatternCon :: PatternCon -> PatternCon -> Bool
cmpPatternCon (PatternCon i _ _ _) (PatternCon i' _ _ _) = i == i'

cmpPattern :: Pattern -> Pattern -> Bool
cmpPattern (PatternI c) (PatternI c') = c == c'
cmpPattern (PatternVar _) (PatternVar _) = True
cmpPattern (Pattern c _) (Pattern c' _) = cmpPatternCon c c'
cmpPattern _ _ = False
