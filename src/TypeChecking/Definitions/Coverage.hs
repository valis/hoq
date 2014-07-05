module TypeChecking.Definitions.Coverage
    ( checkCoverage
    , Pattern(..)
    ) where

import Data.List

data Pattern = PatLeft | PatRight | PatVar | Pattern Int Int [Pattern]
data PatternType = Interval | DataType Int | Unknown

instance Eq Pattern where
    PatLeft == PatLeft = True
    PatRight == PatRight = True
    PatVar == PatVar = True
    Pattern i _ _ == Pattern i' _ _ = i == i'
    _ == _ = False

data OK = OK | Incomplete deriving Eq
data Result = Result OK [Int]

checkCoverage :: [((Int,Int),[Pattern])] -> Maybe [(Int,Int)]
checkCoverage []      = Just []
checkCoverage clauses = case checkClauses (map snd clauses) of
    Result Incomplete _ -> Nothing
    Result OK used -> Just $ map (\i -> fst $ clauses !! i) $ [0 .. length clauses - 1] \\ used

checkClauses :: [[Pattern]] -> Result
checkClauses [] = Result Incomplete []
checkClauses clauses =
    let (t, clauses', b) = checkNull 0 Unknown clauses in
    case (b, checkNonEmptyClauses t clauses') of
        (Just i, Result Incomplete u) -> Result OK (i:u)
        (_, r) -> r

checkNull :: Int -> PatternType -> [[Pattern]] -> (PatternType, [(Pattern, [Pattern])], Maybe Int)
checkNull _ t [] = (t, [], Nothing)
checkNull i t ([] : cs) = (t, [], Just i)
checkNull i t ((pat:pats) : cs) =
    let (t1, cs', b) = checkNull (i + 1) t cs
        t2 = case pat of
                PatLeft       -> Interval
                PatRight      -> Interval
                PatVar        -> t1
                Pattern _ n _ -> DataType n
    in (t2, (pat, pats) : cs', b)

checkNonEmptyClauses :: PatternType -> [(Pattern, [Pattern])] -> Result
checkNonEmptyClauses _ [] = Result Incomplete []
checkNonEmptyClauses Interval     clauses = checkIntervalClauses clauses
checkNonEmptyClauses (DataType n) clauses = checkDataTypeClauses n clauses
checkNonEmptyClauses Unknown      clauses = checkClauses (map snd clauses)

checkIntervalClauses :: [(Pattern, [Pattern])] -> Result
checkIntervalClauses clauses =
    let get con = map (\(i,(_,ps)) -> (i,ps)) $ filterWithIndex (\(c,_) -> c == con) clauses
        lefts   = get PatLeft
        rights  = get PatRight
        vars    = get PatVar
        Result _  is0 = checkClauses (map snd lefts)
        Result _  is1 = checkClauses (map snd rights)
        Result ok is2 = checkClauses (map snd vars)
    in  Result ok $ getIndices lefts is0 ++ getIndices rights is1 ++ getIndices vars is2

checkDataTypeClauses :: Int -> [(Pattern, [Pattern])] -> Result
checkDataTypeClauses n clauses = getResults $ flip map [0 .. n-1] $ \j ->
    let len [] = 0
        len (Pattern i _ args : _) | i == j = length args
        len (_ : pats) = len pats
        
        getPatterns (Pattern _ _ pats) = pats
        getPatterns _                  = replicate (len $ map fst clauses) PatVar
    in map (\(i,(p,ps)) -> (i, getPatterns p ++ ps))
           (filterWithIndex (\(c,_) -> c == Pattern j n [] || c == PatVar) clauses)
  where
    getResults :: [[(Int,[Pattern])]] -> Result
    getResults [] = Result OK []
    getResults (con:cons) =
        let Result ok1 is1 = checkClauses (map snd con)
            Result ok2 is2 = getResults cons
        in Result (if ok1 == OK && ok2 == OK then OK else Incomplete) (getIndices con is1 ++ is2)

getIndices :: [(a,b)] -> [Int] -> [a]
getIndices list = map (\i -> fst $ list !! i)

filterWithIndex :: (a -> Bool) -> [a] -> [(Int,a)]
filterWithIndex p = go 0
  where
    go _ [] = []
    go i (x:xs) =
        let rs = go (i + 1) xs
        in if p x then (i,x):rs else rs
