module Semantics.Value
    ( Value(..), Eval
    , Level(..), level
    , ICon(..), ID, Sort(..)
    , POrd(..), DOrd(..), lessOrEqual
    ) where

import Syntax.Term

data Value t
    = Lam
    | Pi Sort Sort
    | DCon ID Int Int (Eval t)
    | PCon
    | ICon ICon
    | CCon
    | FunCall ID (Eval t)
    | Universe Sort
    | DataType ID Int
    | Interval
    | Path Sort
    | At
    | Coe
    | Iso
    | Squeeze
    | Case [Term Int String]
    | Conds Int (Eval t)
    | FieldAcc Int Int Int (Eval t)

data ICon = ILeft | IRight deriving (Eq, Show)

type Eval t = [([Term Int String], t)]

type ID = Int
data Level = Level Int | NoLevel
data Sort = TypeK Level | Set Level | Prop | Contr deriving Eq

instance Eq (Value t) where
    Lam == Lam = True
    Pi{} == Pi{} = True
    DCon dt i _ _ == DCon dt' i' _ _ = dt == dt' && i == i'
    PCon == PCon = True
    ICon c == ICon c' = c == c'
    CCon == CCon = True
    FunCall n _ == FunCall n' _ = n == n'
    Universe k == Universe k' = k == k'
    DataType n _ == DataType n' _ = n == n'
    Interval == Interval = True
    Path{} == Path{} = True
    At == At = True
    Coe == Coe = True
    Iso == Iso = True
    Squeeze == Squeeze = True
    Case pats == Case pats' = and (zipWith cmpPats pats pats')
      where
        cmpPats :: Term Int u -> Term Int u' -> Bool
        cmpPats Var{} Var{} = True
        cmpPats (Apply c pats) (Apply c' pats') = c == c' && and (zipWith cmpPats pats pats')
        cmpPats _ _ = False
    Conds{} == Conds{} = True
    FieldAcc i _ _ _ == FieldAcc i' _ _ _ = i == i'
    _ == _ = False

instance Show (Value t) where
    show Lam = "Lam"
    show (Pi s1 s2) = "Pi " ++ show s1 ++ " " ++ show s2
    show (DCon n k m _) = "DCon " ++ show n ++ " " ++ show k ++ " " ++ show m
    show PCon = "PCon"
    show (ICon c) = "ICon " ++ show c
    show CCon = "CCon"
    show (FunCall n _) = "FunCall " ++ show n
    show (Universe s) = "Universe " ++ show s
    show (DataType n k) = "DataType " ++ show n ++ " " ++ show k
    show Interval = "Interval"
    show (Path s) = "Path " ++ show s
    show At = "At"
    show Coe = "Coe"
    show Iso = "Iso"
    show Squeeze = "Squeeze"
    show (Case ts) = "Case " ++ show ts
    show (Conds n _) = "Conds " ++ show n
    show (FieldAcc n k m _) = "FieldAcc " ++ show n ++ " " ++ show k ++ " " ++ show m

instance Eq Level where
    l1 == l2 = level l1 == level l2

instance Ord Level where
    compare l1 l2 = compare (level l1) (level l2)

instance Show Level where
    show NoLevel = ""
    show (Level l) = show l

instance Read Level where
    readsPrec _ s = case reads s of
        [] -> [(NoLevel, s)]
        is -> map (\(i,r) -> (Level i, r)) is

instance Enum Level where
    toEnum 0 = NoLevel
    toEnum n = Level n
    fromEnum = level

level :: Level -> Int
level (Level l) = l
level NoLevel = 0

class POrd a where
    pcompare :: a -> a -> Maybe Ordering

class POrd a => DOrd a where
    dmax :: a -> a -> a
    dmaximum :: [a] -> a
    dmaximum [] = error "dmaximum: empty list"
    dmaximum xs = foldl1 dmax xs

lessOrEqual :: POrd a => a -> a -> Bool
lessOrEqual t t' = case pcompare t t' of
    Just r | r == EQ || r == LT -> True
    _                           -> False

instance POrd Sort where
    pcompare Contr Contr = Just EQ
    pcompare Contr _ = Just LT
    pcompare _ Contr = Just GT
    pcompare Prop Prop = Just EQ
    pcompare Prop _ = Just LT
    pcompare _ Prop = Just GT
    pcompare (Set a) (Set b) = Just (compare a b)
    pcompare (TypeK a) (TypeK b) = Just (compare a b)
    pcompare (Set a) (TypeK b) = if a <= b then Just LT else Nothing
    pcompare (TypeK a) (Set b) = if a >= b then Just GT else Nothing

instance DOrd Sort where
    dmax a b = case pcompare a b of
        Just LT -> b
        Just _  -> a
        Nothing -> case (a, b) of
            (Set l1, TypeK l2)  -> TypeK (max l1 l2)
            (TypeK l1, Set l2)  -> TypeK (max l1 l2)
            _                   -> a
    dmaximum [] = TypeK NoLevel
    dmaximum ks = foldl1 dmax ks

instance Show Sort where
    show Contr = "Contr"
    show Prop = "Prop"
    show (Set a) = "Set" ++ show a
    show (TypeK a) = "Type" ++ show a

instance Read Sort where
    readsPrec _ ('C':'o':'n':'t':'r':s) = [(Contr,s)]
    readsPrec _ ('P':'r':'o':'p':s) = [(Prop,s)]
    readsPrec _ ('S':'e':'t':s) = map (\(l,s) -> (Set l, s)) (reads s)
    readsPrec _ ('T':'y':'p':'e':s) = map (\(l,s) -> (TypeK l, s)) (reads s)
    readsPrec _ _ = []

instance Enum Sort where
    succ Contr = Prop
    succ Prop = Set NoLevel
    succ (Set l) = TypeK (succ l)
    succ (TypeK l) = TypeK (succ l)
    toEnum n = TypeK (toEnum n)
    fromEnum Contr = -2
    fromEnum Prop = -1
    fromEnum (Set l) = fromEnum l
    fromEnum (TypeK l) = fromEnum l
