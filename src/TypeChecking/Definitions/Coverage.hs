module TypeChecking.Definitions.Coverage
    ( checkCoverage
    ) where

import Data.List
import Data.Bifunctor

import Syntax.Term
import Semantics.Value hiding (Value(..))

instance Eq s => Eq (Term s a) where
    Apply s _ == Apply s' _ = s == s'
    Var{} == Var{} = True
    _ == _ = False

data PatternType t = Interval | DataType Int [(Int, [Term (Con t) String])] | Path | Unknown

data OK = OK | Incomplete deriving Eq
data Result = Result OK [Int]

checkCoverage :: [((Int,Int),[Term (Con t) String])] -> Maybe [(Int,Int)]
checkCoverage []      = Just []
checkCoverage clauses = case checkClauses (map snd clauses) of
    Result Incomplete _ -> Nothing
    Result OK used -> Just $ map (\i -> fst $ clauses !! i) $ [0 .. length clauses - 1] \\ used

checkClauses :: [[Term (Con t) String]] -> Result
checkClauses [] = Result Incomplete []
checkClauses clauses =
    let (t, clauses', b) = checkNull 0 Unknown clauses in
    case (b, checkNonEmptyClauses t clauses') of
        (Just i, Result Incomplete u) -> Result OK (i:u)
        (_, r) -> r

checkNull :: Int -> PatternType t -> [[Term (Con t) String]] ->
    (PatternType t, [(Term (Con t) String, [Term (Con t) String])], Maybe Int)
checkNull _ t [] = (t, [], Nothing)
checkNull i t ([] : cs) = (t, [], Just i)
checkNull i t ((pat:pats) : cs) =
    let (t1, cs', b) = checkNull (i + 1) t cs
        t2 = case pat of
                Var{}                -> t1
                Apply ICon{} _       -> Interval
                Apply PCon _         -> Path
                Apply (DCon _ n _) _ ->
                    let heads = pat : concatMap (\c -> if null c then [] else [head c]) cs
                    in DataType n $ heads >>= \p -> case p of
                        Apply (DCon i _ (PatEval conds)) _ -> map (\(cond,_) -> (i, map (first snd) cond)) conds
                        _ -> []
                Lambda{} -> error "checkNull"
    in (t2, (pat, pats) : cs', b)

checkNonEmptyClauses :: PatternType t -> [(Term (Con t) String, [Term (Con t) String])] -> Result
checkNonEmptyClauses _                  []      = Result Incomplete []
checkNonEmptyClauses Interval           clauses = checkIntervalClauses clauses
checkNonEmptyClauses (DataType n conds) clauses = checkDataTypeClauses n conds clauses
checkNonEmptyClauses Path               clauses = checkClauses (map snd clauses)
checkNonEmptyClauses Unknown            clauses = checkClauses (map snd clauses)

checkIntervalClauses :: [(Term (Con t) String, [Term (Con t) String])] -> Result
checkIntervalClauses clauses =
    let get con = map (\(i,(_,ps)) -> (i,ps)) $ filterWithIndex (\(c,_) -> c == con) clauses
        lefts   = get $ Apply (ICon ILeft) []
        rights  = get $ Apply (ICon IRight) []
        vars    = get $ Var (error "") []
        Result _  is0 = checkClauses (map snd lefts)
        Result _  is1 = checkClauses (map snd rights)
        Result ok is2 = checkClauses (map snd vars)
    in  Result ok $ getIndices lefts is0 ++ getIndices rights is1 ++ getIndices vars is2

checkDataTypeClauses :: Int -> [(Int, [Term (Con t) String])] -> [(Term (Con t) String, [Term (Con t) String])] -> Result
checkDataTypeClauses n conds clauses = getResults $ flip map [0 .. n-1] $ \j ->
    let getLength [] = 0
        getLength (Apply (DCon i _ _) args : _) | i == j = length args
        getLength (_ : pats) = getLength pats
        len = getLength (map fst clauses)
        
        getPatterns (Apply _ pats) = pats
        getPatterns _              = replicate len $ Var (error "") []
    in map (\(i,(p,ps)) -> (i, getPatterns p ++ ps))
           (filterWithIndex (\(c,_) -> c == Apply (DCon j n $ PatEval []) [] || c == Var (error "") []) clauses)
       ++ (conds >>= \(c,ps) -> if j == c then [(-1, ps)] else [])
  where
    getResults :: [[(Int, [Term (Con t) String])]] -> Result
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
