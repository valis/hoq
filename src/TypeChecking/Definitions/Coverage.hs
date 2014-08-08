module TypeChecking.Definitions.Coverage
    ( checkCoverage
    ) where

import Data.List

import Syntax.Pattern

data PatternType c p a = Interval | DataType Int [(Int, [Pattern c p a])] | Unknown

data OK = OK | Incomplete deriving Eq
data Result = Result OK [Int]

checkCoverage :: [((Int,Int),[Pattern c p a])] -> Maybe [(Int,Int)]
checkCoverage []      = Just []
checkCoverage clauses = case checkClauses (map snd clauses) of
    Result Incomplete _ -> Nothing
    Result OK used -> Just $ map (\i -> fst $ clauses !! i) $ [0 .. length clauses - 1] \\ used

checkClauses :: [[Pattern c p a]] -> Result
checkClauses [] = Result Incomplete []
checkClauses clauses =
    let (t, clauses', b) = checkNull 0 Unknown clauses in
    case (b, checkNonEmptyClauses t clauses') of
        (Just i, Result Incomplete u) -> Result OK (i:u)
        (_, r) -> r

checkNull :: Int -> PatternType c p a -> [[Pattern c p a]]
    -> (PatternType c p a, [(Pattern c p a, [Pattern c p a])], Maybe Int)
checkNull _ t [] = (t, [], Nothing)
checkNull i t ([] : cs) = (t, [], Just i)
checkNull i t ((pat:pats) : cs) =
    let (t1, cs', b) = checkNull (i + 1) t cs
        t2 = case pat of
                PatternI{}                     -> Interval
                PatternVar{}                   -> t1
                PatternEmpty{}                 -> t1
                Pattern (PatternCon _ n _ _) _ ->
                    let heads = pat : concatMap (\c -> if null c then [] else [head c]) cs
                    in DataType n $ heads >>= \p -> case p of
                        Pattern (PatternCon i _ _ conds) _ -> map (\(cond,_) -> (i,cond)) conds
                        _ -> []
    in (t2, (pat, pats) : cs', b)

checkNonEmptyClauses :: PatternType c p a -> [(Pattern c p a, [Pattern c p a])] -> Result
checkNonEmptyClauses _ [] = Result Incomplete []
checkNonEmptyClauses Interval           clauses = checkIntervalClauses clauses
checkNonEmptyClauses (DataType n conds) clauses = checkDataTypeClauses n conds clauses
checkNonEmptyClauses Unknown            clauses = checkClauses (map snd clauses)

checkIntervalClauses :: [(Pattern c p a, [Pattern c p a])] -> Result
checkIntervalClauses clauses =
    let get con = map (\(i,(_,ps)) -> (i,ps)) $ filterWithIndex (\(c,_) -> c == con) clauses
        lefts   = get $ PatternI (error "") ILeft
        rights  = get $ PatternI (error "") IRight
        vars    = get $ PatternVar (error "")
        Result _  is0 = checkClauses (map snd lefts)
        Result _  is1 = checkClauses (map snd rights)
        Result ok is2 = checkClauses (map snd vars)
    in  Result ok $ getIndices lefts is0 ++ getIndices rights is1 ++ getIndices vars is2

checkDataTypeClauses :: Int -> [(Int, [Pattern c p a])] -> [(Pattern c p a, [Pattern c p a])] -> Result
checkDataTypeClauses n conds clauses = getResults $ flip map [0 .. n-1] $ \j ->
    let getLength [] = 0
        getLength (Pattern (PatternCon i _ _ _) args : _) | i == j = length args
        getLength (_ : pats) = getLength pats
        len = getLength (map fst clauses)
        
        getPatterns (Pattern _ pats) = pats
        getPatterns _                = replicate len $ PatternVar (error "")
    in map (\(i,(p,ps)) -> (i, getPatterns p ++ ps))
           (filterWithIndex (\(c,_) -> c == Pattern (PatternCon j n (error "") []) [] || c == PatternVar (error "")) clauses)
       ++ (conds >>= \(c,ps) -> if j == c then [(-1, ps)] else [])
  where
    getResults :: [[(Int, [Pattern c p a])]] -> Result
    getResults [] = Result OK []
    getResults (con:cons) =
        let Result ok1 is1 = checkClauses (map snd con)
            Result ok2 is2 = getResults cons
        in Result (if ok1 == OK && ok2 == OK then OK else Incomplete) (getIndices con is1 ++ is2)

getIndices :: [(Int,b)] -> [Int] -> [Int]
getIndices list = filter (>= 0) . map (\i -> fst $ list !! i)

filterWithIndex :: (a -> Bool) -> [a] -> [(Int,a)]
filterWithIndex p = go 0
  where
    go _ [] = []
    go i (x:xs) =
        let rs = go (i + 1) xs
        in if p x then (i,x):rs else rs
