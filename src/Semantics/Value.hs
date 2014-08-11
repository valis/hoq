module Semantics.Value
    ( Value(..), Eval(..)
    , Level(..), level
    , Con(..), ICon(..)
    , ID
    ) where

import Syntax.Term

data Value t
    = Lam
    | Pi Level Level
    | Con (Con t)
    | FunCall ID (Eval t)
    | Universe Level
    | DataType ID Int
    | Interval
    | Path Level
    | At
    | Coe
    | Iso
    | Squeeze
    | Case [Term (String, Con t) String]

data Con t = DCon Int Int (Eval t) | PCon | ICon ICon
data ICon = ILeft | IRight deriving Eq

data Eval t = SynEval t | PatEval [([Term (String, Con t) String], t)]

type ID = Int
data Level = Level Int | NoLevel

instance Eq (Value t) where
    Lam == Lam = True
    Pi{} == Pi{} = True
    Con c == Con c' = c == c'
    FunCall n _ == FunCall n' _ = n == n'
    Universe l == Universe l' = l == l'
    DataType n _ == DataType n' _ = n == n'
    Interval == Interval = True
    Path{} == Path{} = True
    At == At = True
    Coe == Coe = True
    Iso == Iso = True
    Squeeze == Squeeze = True
    Case pats == Case pats' = and (zipWith cmpPats pats pats')
      where
        cmpPats :: Term (s, Con t) u -> Term (s', Con t) u' -> Bool
        cmpPats Var{} Var{} = True
        cmpPats (Apply (_,c) pats) (Apply (_,c') pats') = c == c' && and (zipWith cmpPats pats pats')
        cmpPats _ _ = False
    _ == _ = False

instance Eq (Con t) where
    DCon i _ _ == DCon i' _ _ = i == i'
    ICon c == ICon c' = c == c'
    PCon == PCon = True
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
