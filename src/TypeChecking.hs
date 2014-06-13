{-# LANGUAGE MultiParamTypeClasses, FlexibleContexts #-}

module TypeChecking
    ( TCM, runTCM, EDocM
    , Hole(..), MaybeTerm
    , typeCheck, typeCheckDefs
    ) where

import Data.Maybe
import Data.List
import Data.Either
import Data.Traversable(sequenceA)
import Control.Monad
import Control.Monad.Error.Class
import Control.Monad.Trans
import Control.Applicative

import Syntax.Expr
import qualified Syntax.Term as T
import Evaluation.Normalization
import Evaluation.Monad
import Syntax.ErrorDoc
import Syntax.PrettyPrinter
import Syntax.BNFC.PrintGrammar

type EDocM = WarnT [EMsg T.Term]
type TCM m = EDocM (EvalT String T.Term m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runEvalT . runWarnT

notInScope :: Show a => (Int,Int) -> String -> a -> EMsg f
notInScope lc s a = emsgLC lc ("Not in scope: " ++ (if null s then "" else s ++ " ") ++ show a) enull

data MaybeTerm a = JustTerm (T.Term a) | JustExpr Expr | JustStr String | NoTerm
data Hole a = Hole [EMsg T.Term] (MaybeTerm a) | NoHole a
type Term = T.Term (T.Var Int (Hole String))

instance Eq a => Eq (Hole a) where
    NoHole a == NoHole a' = a == a'
    _        == _         = False

instance Functor MaybeTerm where
    fmap f (JustTerm t)    = JustTerm (fmap f t)
    fmap _ (JustExpr expr) = JustExpr expr
    fmap _ (JustStr str)   = JustStr str
    fmap _ NoTerm          = NoTerm

instance Functor Hole where
    fmap f (NoHole a)     = NoHole (f a)
    fmap f (Hole errs mt) = Hole errs (fmap f mt)

instance Applicative MaybeTerm where
    pure = JustTerm . T.Var
    JustTerm tf <*> JustTerm ta = JustTerm (tf <*> ta)
    JustExpr ef <*> JustExpr ea = JustExpr (App ef ea)
    JustExpr ef <*> JustStr  sa = JustStr $ printTree ef ++ " " ++ sa
    JustStr  sf <*> JustExpr ea = JustStr $ sf ++ " " ++ printTree ea
    JustStr  sf <*> JustStr  sa = JustStr $ sf ++ " " ++ sa
    _           <*> _           = NoTerm

instance Applicative Hole where
    pure = NoHole
    NoHole f <*> NoHole a     = NoHole (f a)
    NoHole f <*> Hole errs ma = Hole errs (fmap f ma)
    Hole errs mf <*> NoHole a = Hole errs $ fmap (\f -> f a) mf
    Hole e1 mf <*> Hole e2 ma = Hole (e1 ++ e2) $ mf <*> ma

inferErrorMsg :: (Int,Int) -> EMsg T.Term
inferErrorMsg lc = emsgLC  lc "Cannot infer type of the argument" enull

prettyOpen :: Pretty a T.Term => [String] -> T.Term (T.Var Int a) -> EDoc T.Term
prettyOpen vars term = epretty $ fmap pretty $ term >>= \v -> return $ case v of
    T.B i -> Left (vars !! i)
    T.F a -> Right a

instance Pretty a T.Term => Pretty (MaybeTerm a) T.Term where
    pretty (JustTerm t) = epretty (fmap pretty t)
    pretty (JustExpr e) = pretty (printTree e)
    pretty (JustStr  s) = pretty s
    pretty NoTerm       = enull

instance Pretty a T.Term => Pretty (Hole a) T.Term where
    pretty (NoHole a)  = pretty a
    pretty (Hole _ mt) = pretty "{#Error" <+> pretty mt <+> pretty "#}"

-- Type checking expressions

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

typeCheck :: Monad m => Expr -> Maybe (T.Term (Hole String)) -> EvalT String T.Term m (T.Term (Hole String))
typeCheck expr ty = liftM (fmap fromVar . fst) $ go [] expr $ fmap (fmap T.F) ty
  where
    fromVar :: T.Var a b -> b
    fromVar (T.B _) = error "typeCheck"
    fromVar (T.F b) = b
    
    go :: Monad m => [(String, Term)] -> Expr -> Maybe Term -> EvalT String T.Term m (Term, Term)
    go ctx (Paren _ e) ty = go ctx e ty
    go ctx (Lam _ args e) (Just ty@(T.Pi fl a b)) = do
        let vars = map unArg args
        (r, t) <- go (reverse (map (\v -> (v, a)) vars) ++ ctx) e $ Just (T.instantiateVars b)
        return (T.Lam $ T.abstractVars vars r, ty)
    go ctx e@Lam{} (Just ty) =
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen (fmap fst ctx) ty $$
                                         pretty "But lambda expression has pi type"
        in return $ (T.Var $ T.F $ Hole [msg] $ JustExpr e, ty)
    go ctx e (Just ty) = do
        (r, t) <- go ctx e Nothing
        let msg = emsgLC (getPos e) "" $ pretty "Expected type:" <+> prettyOpen (fmap fst ctx) ty $$
                                         pretty "Actual type:"   <+> prettyOpen (fmap fst ctx) t
        return $ if t `T.lessOrEqual` ty
                    then (r, t)
                    else (T.Var $ T.F $ Hole [msg] NoTerm {- TODO $ JustTerm t -}, ty)
    go ctx (Pi [] e) Nothing = go ctx e Nothing
    go ctx (Pi (PiTele _ e1 e2 : tvs) e) Nothing = case exprToVars e1 of
        Left lc    -> let msg = emsgLC lc "Expected a list of identifiers" enull
                      in return (T.Var $ T.F $ Hole [msg] $ JustExpr e1, T.Universe T.NoLevel)
        Right args -> let vars = map unArg args
                      in do
                        (r1, t1) <- go ctx e2 Nothing
                        (r2, t2) <- go (map (\v -> (v, r1)) vars ++ ctx) (Pi tvs e) Nothing
                        return $ case checkUniverses (fmap fst ctx) e2 (Pi tvs e) t1 t2 of
                                    Right t   -> (T.Pi (null tvs) r1 (T.abstractVars vars r2), t)
                                    Left errs -> (T.Var $ T.F $ Hole errs NoTerm {- TODO -}, T.Universe T.NoLevel)
    go ctx (App e1 e2) Nothing = do
        (r1, t1) <- go ctx e1 Nothing
        case t1 of
            T.Pi fl a b -> do
                (r2, _) <- go ctx e2 (Just a)
                return (T.App r1 r2, either (T.Pi fl a) id $ T.instantiateNames1 r2 b)
            _ -> let msg = emsgLC (getPos e1) "" $ pretty "Expected pi type" $$
                                                   pretty "Actual type:" <+> prettyOpen (fmap fst ctx) t1
                     err = T.Var $ T.F $ Hole [msg] NoTerm {- TODO (JustTerm r1) -}
                 in return (err,err)
    go _ e@Lam{} Nothing = let err = T.Var . T.F . Hole [inferErrorMsg (getPos e)]
                           in return (err (JustExpr e), err NoTerm)
    go ctx (Arr e1 e2) Nothing = do
        (r1,t1) <- go ctx e1 Nothing
        (r2,t2) <- go ctx e2 Nothing
        return $ case checkUniverses (fmap fst ctx) e1 e2 t1 t2 of
                    Right t   -> (T.Arr r1 r2, t)
                    Left errs -> (T.Var $ T.F $ Hole errs NoTerm {- TODO $ JustTerm (T.Arr r1 r2) -}, T.Universe T.NoLevel)
    go ctx (Var x) Nothing =
        let v = unArg x in
        case lookupIndex v ctx of
            Just (i,t) -> return (T.Var (T.B i), t) -- TODO
            Nothing    -> do
                mt <- getEntry v
                return $ case mt of
                    Just t  -> (fmap (T.F . NoHole) t, error "TODO")
                    Nothing -> let err = T.Var $ T.F $ Hole [notInScope (argGetPos x) "" v] (JustStr v)
                               in (err,err)
    go _ (Universe (U (_,u))) Nothing = let l = parseLevel u
                                        in return $ (T.Universe l, T.Universe $ T.Level $ T.level l + 1)

-- Type checking definitions

exprPatToPattern :: Monad m => Pattern -> TCM m T.RTPattern
exprPatToPattern (Pattern (PIdent (lc,name)) pats) = do
    d <- lift (getEntry name)
    case d of
        Just (T.Con i _ _) -> liftM (T.RTPattern i) (mapM parPatToPattern pats)
        _ -> throwError [notInScope lc "data constructor" name]

parPatToPattern :: Monad m => ParPat -> TCM m T.RTPattern
parPatToPattern (ParVar arg) = do
    d <- lift $ getEntry (unArg arg)
    return $ case d of
        Just (T.Con i _ _) -> T.RTPattern i []
        _ -> T.RTPatternVar
parPatToPattern (ParPat _ pat) = exprPatToPattern pat

toListPat :: T.RTPattern -> Pattern -> [String]
toListPat T.RTPatternVar (Pattern (PIdent (_,name)) _) = [name]
toListPat (T.RTPattern _ pats) (Pattern _ pats') = concat (zipWith toListPar pats pats')
  where
    toListPar :: T.RTPattern -> ParPat -> [String]
    toListPar pat (ParPat _ pat') = toListPat pat pat'
    toListPar T.RTPatternVar (ParVar arg) = [unArg arg]
    toListPar (T.RTPattern _ _) (ParVar _) = []

data PDef = PDefSyn String Expr | PDefCases String Expr [([ParPat],Expr)] | PDefData String [(Expr,Expr)] [Con]

theSameAs :: String -> Def -> Bool
theSameAs name (DefFun (Pattern (PIdent (_,name')) _) _) = name == name'
theSameAs _ _ = False

splitDefs :: Monad m => [Def] -> EDocM m [PDef]
splitDefs [] = return []
splitDefs (DefType (PIdent (_,name)) ty : defs) =
    let (defs1,defs2) = span (theSameAs name) defs
    in liftM (PDefCases name ty (map (\(DefFun (Pattern _ pats) expr) -> (pats,expr)) defs1) :) (splitDefs defs2)
splitDefs (DefFun (Pattern (PIdent (_,name)) []) expr : defs) = liftM (PDefSyn name expr :) (splitDefs defs)
splitDefs (DefFun (Pattern (PIdent (lc,name)) _) _    : defs) = do
    warn [inferErrorMsg lc]
    splitDefs $ dropWhile (theSameAs name) defs
splitDefs (DefData (PIdent (_,name)) teles cons : defs) =
    liftM (PDefData name (map (\(DataTele _ e1 e2) -> (e1,e2)) teles) (unCons cons) :) (splitDefs defs)

typeCheckPDef :: Monad m => PDef -> TCM m ()
typeCheckPDef (PDefSyn name expr) = do
    term <- lift (typeCheck expr Nothing)
    case sequenceA term of
        NoHole term -> lift $ addDef name (T.FunSyn name term)
        Hole errs _ -> warn errs
typeCheckPDef (PDefCases name ty cases) = mapM (uncurry funsToTerm) cases >>= lift . addDefRec name . T.FunCall name
  where
    funsToTerm :: Monad m => [ParPat] -> Expr -> TCM m (T.Names T.RTPattern T.Term String)
    funsToTerm pats expr = do
        pats' <- mapM parPatToPattern pats
        let list = toListPat (T.RTPattern 0 pats') (Pattern (error "typeCheckPDef") pats)
        term <- lift (typeCheck expr Nothing) -- TODO
        case sequenceA term of
            NoHole term -> return $ T.Name pats' $ T.abstract (`elemIndex` list) term
            Hole errs _ -> throwError errs
typeCheckPDef (PDefData name params cons) = lift $ do
    addDef name (T.DataType name)
    forM_ (zip cons [0..]) $ \(Con (PIdent (_,con)) _, i) -> addDef con $ T.Con i con []

typeCheckDefs :: Monad m => [Def] -> TCM m ()
typeCheckDefs defs = splitDefs defs >>= mapM_ (\t -> typeCheckPDef t `catchError` warn)
