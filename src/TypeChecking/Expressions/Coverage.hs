{-# LANGUAGE GADTs #-}

module TypeChecking.Expressions.Coverage
    ( checkCoverage
    ) where

import Data.List

import Syntax.Term
import Semantics.Value hiding (Value(..))
import qualified Semantics.Pattern as P

data Pattern = PatDCon Int Int [[Term Pattern String]] | PatPCon | PatICon ICon
data PatternType = Interval | DataType Int [(Int, [Term Pattern String])] | Path | Unknown

data OK = OK | Incomplete deriving Eq
data Result = Result OK [Int]

checkCoverage :: [((Int,Int), P.Clause b)] -> Maybe [(Int,Int)]
checkCoverage []      = Just []
checkCoverage clauses = case checkClauses $ map (\(_, P.Clause pats _) -> patternsToTerms pats) clauses of
    Result Incomplete _ -> Nothing
    Result OK used -> Just $ map (\i -> fst $ clauses !! i) $ [0 .. length clauses - 1] \\ used
  where
    patternToTerm :: P.Pattern b a -> Term Pattern String
    patternToTerm (P.PatDCon i n cs pats) =
        Apply (PatDCon i n $ map (\(P.Clause ps _) -> patternsToTerms ps) cs) (patternsToTerms pats)
    patternToTerm (P.PatPCon pat) = Apply PatPCon [patternToTerm pat]
    patternToTerm (P.PatICon con) = capply (PatICon con)
    patternToTerm (P.PatVar var) = cvar var
    
    patternsToTerms :: P.Patterns b a -> [Term Pattern String]
    patternsToTerms P.Nil = []
    patternsToTerms (P.Cons p ps) = patternToTerm p : patternsToTerms ps

checkClauses :: [[Term Pattern String]] -> Result
checkClauses [] = Result Incomplete []
checkClauses clauses =
    let (t, clauses', b) = checkNull 0 Unknown clauses in
    case (b, checkNonEmptyClauses t clauses') of
        (Just i, Result Incomplete u) -> Result OK (i:u)
        (_, r) -> r

checkNull :: Int -> PatternType -> [[Term Pattern String]] ->
    (PatternType, [(Term Pattern String, [Term Pattern String])], Maybe Int)
checkNull _ t [] = (t, [], Nothing)
checkNull i t ([] : cs) = (t, [], Just i)
checkNull i t ((pat:pats) : cs) =
    let (t1, cs', b) = checkNull (i + 1) t cs
        t2 = case pat of
                Var{}                   -> t1
                Apply PatICon{} _       -> Interval
                Apply PatPCon _         -> Path
                Apply (PatDCon _ n _) _ ->
                    let heads = pat : concatMap (\c -> if null c then [] else [head c]) cs
                    in DataType n $ heads >>= \p -> case p of
                        Apply (PatDCon i _ conds) _ -> map (\cond -> (i, cond)) conds
                        _ -> []
                Lambda{} -> error "checkNull"
    in (t2, (pat, pats) : cs', b)

checkNonEmptyClauses :: PatternType -> [(Term Pattern String, [Term Pattern String])] -> Result
checkNonEmptyClauses _                  []      = Result Incomplete []
checkNonEmptyClauses Interval           clauses = checkIntervalClauses clauses
checkNonEmptyClauses (DataType n conds) clauses = checkDataTypeClauses n conds clauses
checkNonEmptyClauses Path               clauses = checkClauses (map snd clauses)
checkNonEmptyClauses Unknown            clauses = checkClauses (map snd clauses)

checkIntervalClauses :: [(Term Pattern String, [Term Pattern String])] -> Result
checkIntervalClauses clauses =
    let get pcon = map (\(i,(_,ps)) -> (i,ps)) $ filterWithIndex (pcon . fst) clauses
        lefts   = get $ \c -> case c of { Apply (PatICon ILeft) _ -> True; _ -> False }
        rights  = get $ \c -> case c of { Apply (PatICon IRight) _ -> True; _ -> False }
        vars    = get $ \c -> case c of { Var{} -> True; _ -> False }
        Result _  is0 = checkClauses (map snd lefts)
        Result _  is1 = checkClauses (map snd rights)
        Result ok is2 = checkClauses (map snd vars)
    in  Result ok $ getIndices lefts is0 ++ getIndices rights is1 ++ getIndices vars is2

checkDataTypeClauses :: Int -> [(Int, [Term Pattern String])] -> [(Term Pattern String, [Term Pattern String])] -> Result
checkDataTypeClauses n conds clauses = getResults $ flip map [0 .. n-1] $ \j ->
    let getLength [] = 0
        getLength (Apply (PatDCon i _ _) args : _) | i == j = length args
        getLength (_ : pats) = getLength pats
        len = getLength (map fst clauses)
        
        getPatterns (Apply _ pats) = pats
        getPatterns _              = replicate len $ Var (error "") []
    in map (\(i,(p,ps)) -> (i, getPatterns p ++ ps))
           (filterWithIndex (\(c,_) -> case c of
                Apply (PatDCon j' _ _) _ | j == j' -> True
                Var{} -> True
                _ -> False) clauses)
       ++ (conds >>= \(c,ps) -> if j == c then [(-1, ps)] else [])
  where
    getResults :: [[(Int, [Term Pattern String])]] -> Result
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
