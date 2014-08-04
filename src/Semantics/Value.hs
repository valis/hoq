module Semantics.Value
    ( Value(..), Eval(..)
    , Level(..), level
    , ID
    ) where

import Syntax.Pattern

data Value t
    = Lam
    | App
    | Pi Level Level
    | Con Int (Eval t)
    | FunCall ID (Eval t)
    | Universe Level
    | DataType ID Int
    | Interval
    | ICon ICon
    | Path Level
    | PCon
    | At
    | Coe
    | Iso
    | Squeeze

data Eval t = SynEval t | PatEval [([Pattern () t String], t)]

type ID = Int
data Level = Level Int | NoLevel

instance Eq (Value t) where
    Lam == Lam = True
    App == App = True
    Pi{} == Pi{} = True
    Con i _ == Con i' _ = i == i'
    FunCall n _ == FunCall n' _ = n == n'
    Universe l == Universe l' = l == l'
    DataType n _ == DataType n' _ = n == n'
    Interval == Interval = True
    ICon c == ICon c' = c == c'
    Path{} == Path{} = True
    PCon == PCon = True
    At == At = True
    Coe == Coe = True
    Iso == Iso = True
    Squeeze == Squeeze = True
    _ == _ = False

instance Eq Level where
    l1 == l2 = level l1 == level l2

instance Ord Level where
    compare l1 l2 = compare (level l1) (level l2)

instance Show Level where
    show NoLevel = "Type"
    show (Level l) = "Type" ++ show l

instance Read Level where
    readsPrec _ ('T':'y':'p':'e':s) = case reads s of
        [] -> [(NoLevel, s)]
        is -> map (\(i,r) -> (Level i, r)) is
    readsPrec _ _ = []

instance Enum Level where
    toEnum 0 = NoLevel
    toEnum n = Level n
    fromEnum = level

level :: Level -> Int
level (Level l) = l
level NoLevel = 0
