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
import Syntax.BNFC.PrintGrammar

type EDocM = WarnT [EMsg T.Term]
type TCM m = EDocM (EvalT String T.Term m)

runTCM :: Monad m => TCM m a -> m (Maybe a)
runTCM = liftM snd . runEvalT . runWarnT

-- Type checking expressions

data MaybeTerm a = JustTerm (T.Term a) | JustStr String | NoTerm
data Hole a = Hole [EMsg T.Term] (MaybeTerm a)

bindEitherMaybe :: Either a b -> (b -> Maybe c) -> Maybe c
bindEitherMaybe Left{} _ = Nothing
bindEitherMaybe (Right b) k = k b

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

typeCheck :: Expr -> T.Term (Either (Hole String) String)
typeCheck (Lam _ args e) =
    let vars = map unArg args
    in T.Lam $ T.Name vars $ T.abstract (\x -> x `bindEitherMaybe` \v -> v `elemIndex` vars) (typeCheck e)
typeCheck (Arr e1 e2) = T.Arr (typeCheck e1) (typeCheck e2)
typeCheck (Pi [] e) = typeCheck e
typeCheck (Pi (PiTele _ e1 e2 : tvs) e) = T.Pi (null tvs) (typeCheck e2) $ case exprToVars e1 of
    Left lc ->
        let msg = emsgLC lc "Expected a list of identifiers" enull
        in T.Name [] $ T.Scope $ T.Var $ T.F $ T.Var $ Left $ Hole [msg] $ JustStr (printTree e1)
    Right args ->
        let vars = map unArg args
        in T.Name vars $ T.abstract (\x -> x `bindEitherMaybe` \v -> v `elemIndex` vars) $ typeCheck (Pi tvs e)
typeCheck (App e1 e2) = T.App (typeCheck e1) (typeCheck e2)
typeCheck (Var x) = T.Var $ Right (unArg x)
typeCheck (Universe (U (_,u))) = T.Universe (parseLevel u)
typeCheck (Paren _ e) = typeCheck e

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
    warn [msg]
    splitDefs $ dropWhile (theSameAs name) defs
  where
    msg = emsgLC  lc "Cannot infer type of the argument" enull
splitDefs (DefData (PIdent (_,name)) teles cons : defs) =
    liftM (PDefData name (map (\(DataTele _ e1 e2) -> (e1,e2)) teles) (unCons cons) :) (splitDefs defs)

typeCheckPDef :: Monad m => PDef -> TCM m ()
typeCheckPDef (PDefSyn   name    expr)  = case sequenceA (typeCheck expr) of
    Right term -> lift $ addDef name (T.FunSyn name term)
    Left (Hole errs _) -> warn errs
typeCheckPDef (PDefCases name ty cases) = mapM (uncurry funsToTerm) cases >>= lift . addDefRec name . T.FunCall name
  where
    funsToTerm :: Monad m => [ParPat] -> Expr -> TCM m (T.Names T.RTPattern T.Term String)
    funsToTerm pats expr = do
        pats' <- mapM parPatToPattern pats
        let list = toListPat (T.RTPattern 0 pats') (Pattern (error "typeCheckPDef") pats)
        case sequenceA (typeCheck expr) of
            Right term -> return $ T.Name pats' $ T.abstract (`elemIndex` list) term
            Left (Hole errs _) -> throwError errs
typeCheckPDef (PDefData  name params cons) =
    forM_ (zip cons [0..]) $ \(Con (PIdent (_,con)) _, i) -> lift $ addDef con $ T.Con i con []

typeCheckDefs :: Monad m => [Def] -> TCM m ()
typeCheckDefs defs = splitDefs defs >>= mapM_ (\t -> typeCheckPDef t `catchError` warn)
