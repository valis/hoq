module TypeChecking.Interactive
    ( TCM, runTCM, EDocM
    , Hole(..), MaybeTerm
    , typeCheck
    ) where

import Data.Maybe
import Data.List
import Data.Either
import Data.Traversable(sequenceA)
import Control.Monad
import Control.Applicative

import Syntax.Expr
import qualified Syntax.Term as T
import Evaluation.Normalization
import Evaluation.Monad
import Syntax.ErrorDoc
import Syntax.PrettyPrinter
import Syntax.BNFC.PrintGrammar
import TypeChecking.Hole

type EDocM = WarnT [EMsg T.Term]
type TCM m = EDocM (EvalT String T.Term m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runEvalT . runWarnT

notInScope :: Show a => (Int,Int) -> String -> a -> EMsg f
notInScope lc s a = emsgLC lc ("Not in scope: " ++ (if null s then "" else s ++ " ") ++ show a) enull

type Term = Term (Hole (T.Var Int String))

abstractVars :: Monad f => [n] -> f (Hole (T.Var Int a)) -> T.Names n f (Hole (T.Var Int a))
abstractVars ns t = undefined

inferErrorMsg :: (Int,Int) -> EMsg T.Term
inferErrorMsg lc = emsgLC  lc "Cannot infer type of the argument" enull

prettyOpen :: Pretty a T.Term => [String] -> T.Term (T.Var Int a) -> EDoc T.Term
prettyOpen vars term = epretty $ fmap pretty $ term >>= \v -> return $ case v of
    T.B i -> Left (vars !! i)
    T.F a -> Right a

parseLevel :: String -> T.Level
parseLevel "Type" = T.NoLevel
parseLevel ('T':'y':'p':'e':s) = T.Level (read s)
parseLevel s = error $ "parseLevel: " ++ s

exprToVars :: Expr -> Either (Int,Int) [Arg]
exprToVars = fmap reverse . go
  where
    go (Var a) = Right [a]
    go (App as (Var a)) = fmap (a:) (go as)
    go e = Left (getPos e)

lookupIndex :: Eq a => a -> [(a,b)] -> Maybe (Int,b)
lookupIndex _ [] = Nothing
lookupIndex a ((a',b):r) | a == a' = Just (0,b)
                         | otherwise = fmap (\(i,b') -> (i + 1, b')) (lookupIndex a r)

checkUniverses :: Pretty a T.Term => [String] -> Expr -> Expr
    -> T.Term (T.Var Int a) -> T.Term (T.Var Int a) -> Either [EMsg T.Term] (T.Term b)
checkUniverses _ _ _ (T.Universe u1) (T.Universe u2) = Right $ T.Universe (max u1 u2)
checkUniverses ctx e1 e2 t1 t2 = Left $ msg e1 t1 ++ msg e2 t2
  where
    msg _ (T.Universe _) = []
    msg e t = [emsgLC (getPos e) "" $ pretty "Expected type: Type" $$
                                      pretty "Actual type:" <+> prettyOpen ctx t]

typeCheck :: Monad m => Expr -> Maybe (T.Term String) -> EvalT String T.Term m (T.Term (Hole String), T.Term String)
typeCheck expr ty = liftM (\(te,ty) -> (fmap (fmap fromVar) te, fmap fromVar ty)) $ go [] expr $ fmap (fmap T.F) ty
  where
    fromVar :: T.Var a b -> b
    fromVar (T.B _) = error "typeCheck"
    fromVar (T.F b) = b
    
    go :: Monad m => [(String, T.Term (T.Var Int String))] -> Expr -> Maybe (T.Term (T.Var Int String))
        -> EvalT String T.Term m (Term, T.Term (T.Var Int String))
    go ctx (Paren _ e) ty = go ctx e ty
    go ctx (Lam _ args e) (Just ty@(T.Pi fl a b)) = do
        let vars = map unArg args
        (r, t) <- go (reverse (map (\v -> (v, a)) vars) ++ ctx) e $ Just (T.instantiateVars b)
        return (T.Lam $ abstractVars vars r, ty)
    go ctx e@Lam{} (Just ty) =
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen (fmap fst ctx) ty $$
                                         pretty "But lambda expression has pi type"
        in return $ (T.Var $ Hole [msg] $ JustExpr e, ty)
    go ctx e (Just ty) = do
        (r, t) <- go ctx e Nothing
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen (fmap fst ctx) ty $$
                                         pretty "Actual type:"   <+> prettyOpen (fmap fst ctx) t
        return $ if t `T.lessOrEqual` ty
                    then (r, t)
                    else (T.Var $ Hole [msg] $ JustTerm t, ty)
    go ctx (Pi [] e) Nothing = go ctx e Nothing
    go ctx expr@(Pi (PiTele _ e1 e2 : tvs) e) Nothing = case exprToVars e1 of
        Left lc    -> let msg = emsgLC lc "Expected a list of identifiers" enull
                      in return (T.Var $ Hole [msg] $ JustExpr e1, T.Universe T.NoLevel)
        Right args -> let vars = map unArg args
                      in do
                        (hr1, t1) <- go ctx e2 Nothing
                        case sequenceA hr1 of
                            Hole errs mr1 -> return (T.Var $ Hole errs $ JustExpr expr, T.Universe T.NoLevel)
                            NoHole r1 -> do
                                (r2, t2) <- go (map (\v -> (v, r1)) vars ++ ctx) (Pi tvs e) Nothing
                                let r = T.Pi (null tvs) hr1 (abstractVars vars r2)
                                return $ case checkUniverses (fmap fst ctx) e2 (Pi tvs e) t1 t2 of
                                            Right t   -> (r, t)
                                            Left errs -> (T.Var $ join $ Hole errs $ JustTerm r, T.Universe T.NoLevel)
    go ctx (App e1 e2) Nothing = do
        (r1, t1) <- go ctx e1 Nothing
        case t1 of
            T.Pi fl a b -> do
                (hr2, _) <- go ctx e2 (Just a)
                case sequenceA hr2 of
                    Hole errs mr2 -> ...
                    NoHole r2     -> return (T.App r1 r2, either (T.Pi fl a) id $ T.instantiateNames1 r2 b)
            _ -> let msg = emsgLC (getPos e1) "" $ pretty "Expected pi type" $$
                                                   pretty "Actual type:" <+> prettyOpen (fmap fst ctx) t1
                     err = T.Var $ Hole [msg] (JustTerm r1)
                 in return (err,err)
    go _ e@Lam{} Nothing = let err = T.Var . Hole [inferErrorMsg (getPos e)]
                           in return (err (JustExpr e), err NoTerm)
    go ctx (Arr e1 e2) Nothing = do
        (r1,t1) <- go ctx e1 Nothing
        (r2,t2) <- go ctx e2 Nothing
        return $ case checkUniverses (fmap fst ctx) e1 e2 t1 t2 of
                    Right t   -> (T.Arr r1 r2, t)
                    Left errs -> (T.Var $ Hole errs $ JustTerm (T.Arr r1 r2), T.Universe T.NoLevel)
    go ctx (Var x) Nothing =
        let v = unArg x in
        case lookupIndex v ctx of
            Just (i,t) -> return (T.Var (T.B i), t) -- TODO
            Nothing    -> do
                mt <- getEntry v
                return $ case mt of
                    Just (te,ty) -> (fmap (T.F . NoHole) (T.Var v), fmap (T.F . NoHole) ty)
                    Nothing      -> let err = T.Var $ Hole [notInScope (argGetPos x) "" v] (JustStr v)
                                    in (err,err)
    go _ (Universe (U (_,u))) Nothing = let l = parseLevel u
                                        in return $ (T.Universe l, T.Universe $ T.Level $ T.level l + 1)
