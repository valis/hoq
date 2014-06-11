module TypeChecking where

import Data.Maybe
import Data.List
import Data.Either
import Data.Traversable(sequenceA)
import Control.Monad

import Syntax.Expr
import qualified Syntax.Term as T
import Evaluation.Normalization
import Evaluation.Monad

-- Type checking expressions

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

typeCheck :: Expr -> T.Term (Either String String)
typeCheck (Lam _ args e) =
    let vars = map unArg args
    in T.Lam $ T.Name vars $ T.abstract (\x -> x `bindEitherMaybe` \v -> v `elemIndex` vars) (typeCheck e)
typeCheck (Arr e1 e2) = T.Arr (typeCheck e1) (typeCheck e2)
typeCheck (Pi [] e) = typeCheck e
typeCheck (Pi (PiTele _ e1 e2 : tvs) e) = T.Pi (null tvs) (typeCheck e2) $ case exprToVars e1 of
    Left p -> T.Name [] $ T.Scope $ T.Var $ T.F $ T.Var $ Left $ "error at " ++ show p
    Right args ->
        let vars = map unArg args
        in T.Name vars $ T.abstract (\x -> x `bindEitherMaybe` \v -> v `elemIndex` vars) $ typeCheck (Pi tvs e)
typeCheck (App e1 e2) = T.App (typeCheck e1) (typeCheck e2)
typeCheck (Var x) = T.Var $ Right (unArg x)
typeCheck (Universe (U (_,u))) = T.Universe (parseLevel u)
typeCheck (Paren _ e) = typeCheck e

-- Type checking definitions

type Ev = EvalT String T.Term

exprPatToPattern :: Monad m => Pattern -> Ev m T.RTPattern
exprPatToPattern (Pattern (PIdent (_,name)) pats) = do
    d <- getEntry name
    case d of
        Just (T.Con i _ _) -> liftM (T.RTPattern i) (mapM parPatToPattern pats)
        _ -> error "TODO"

parPatToPattern :: Monad m => ParPat -> Ev m T.RTPattern
parPatToPattern (ParVar arg) = do
    d <- getEntry (unArg arg)
    return $ case d of
        Just (T.Con i _ _) -> T.RTPattern i []
        _ -> T.RTPatternVar
parPatToPattern (ParPat _ pat) = exprPatToPattern pat

toList :: T.RTPattern -> Pattern -> [String]
toList T.RTPatternVar (Pattern (PIdent (_,name)) _) = [name]
toList (T.RTPattern _ pats) (Pattern _ pats') = concat (zipWith toListPar pats pats')
  where
    toListPar :: T.RTPattern -> ParPat -> [String]
    toListPar pat (ParPat _ pat') = toList pat pat'
    toListPar T.RTPatternVar (ParVar arg) = [unArg arg]
    toListPar (T.RTPattern _ _) (ParVar _) = []

typeCheckDefs :: Monad m => [Def] -> Ev m [String]
typeCheckDefs [] = return []
typeCheckDefs (DefType p@(PIdent (_,name)) ty : defs) = do
    let (funs,defs') = splitDefs defs
    funs' <- mapM (uncurry $ funsToTerm p) funs
    let (errs,names) = partitionEithers funs'
    errs' <- case sequenceA (typeCheck ty) of
        Right _ -> addDefRec name (T.FunCall name names) >> return errs
        Left err -> return (err:errs)
    liftM (errs' ++) (typeCheckDefs defs')
  where
    splitDefs :: [Def] -> ([([ParPat],Expr)],[Def])
    splitDefs (DefFun (Pattern (PIdent (_,name')) pats) expr : defs) | name == name' =
        let (funs,defs') = splitDefs defs
        in ((pats,expr):funs,defs')
    splitDefs defs = ([],defs)
    
    funsToTerm :: Monad m => PIdent -> [ParPat] -> Expr -> Ev m (Either String (T.Names T.RTPattern T.Term String))
    funsToTerm name pats expr = do
        pats' <- mapM parPatToPattern pats
        return $ fmap (T.Name pats' . T.abstract (`elemIndex` toList (T.RTPattern 0 pats') (Pattern name pats))) $ sequenceA (typeCheck expr)
typeCheckDefs (DefFun (Pattern (PIdent (_,name)) []) expr : defs) = case sequenceA (typeCheck expr) of
    Right term -> addDef name (T.FunSyn name term) >> typeCheckDefs defs
    Left err -> liftM (err:) (typeCheckDefs defs)
typeCheckDefs (DefFun (Pattern (PIdent ((l,c),_)) _) expr : defs) = liftM (msg:) (typeCheckDefs defs)
  where msg = show l ++ ": " ++ show c ++ ": Cannot infer type of arguments"
typeCheckDefs (DefData _ teles NoCons : defs) = typeCheckDefs defs
typeCheckDefs (DefData _ teles (Cons cons) : defs) = do
    forM_ (zip cons [0..]) $ \(Con (PIdent (_,con)) _, i) -> addDef con $ T.Con i con []
    typeCheckDefs defs
