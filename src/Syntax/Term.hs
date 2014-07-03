module Syntax.Term
    ( Term(..), ICon(..)
    , Level(..), level
    , Pattern(..), RTPattern(..)
    , module Syntax.Name, module Bound
    , POrd(..), lessOrEqual, greaterOrEqual
    , collectDataTypes, apps
    ) where

import Prelude.Extras
import Data.Function
import Bound
import Data.Traversable hiding (mapM)
import Data.Foldable hiding (msum)
import Data.Monoid(mappend)
import Control.Applicative
import Control.Monad

import Syntax.Name

data Level = Level Int | NoLevel

instance Eq Level where
    (==) = (==) `on` level

instance Ord Level where
    compare = compare `on` level

instance Show Level where
    show = show . level

level :: Level -> Int
level (Level l) = l
level NoLevel = 0

data Term a
    = Var a
    | App (Term a) (Term a)
    | Lam (Names String Term a)
    | Arr (Term a) (Term a)
    | Pi Bool (Term a) (Names String Term a)
    | Con Int String [Term a] [ClosedNames RTPattern Term]
    | FunCall String [ClosedNames RTPattern Term]
    | FunSyn  String (Term a)
    | Universe Level
    | DataType String [Term a]
    | Interval
    | ICon ICon
    | Path [Term a]
    | PathImp (Maybe (Term a)) (Term a) (Term a)
    | PCon (Maybe (Term a))
    | At (Term a) (Term a) (Term a) (Term a)
    | Coe [Term a]
    | Iso [Term a]
    | Squeeze [Term a]
data ICon = ILeft | IRight deriving (Eq,Show)
data RTPattern = RTPattern Int [RTPattern] | RTPatternVar | RTPatternI ICon deriving Show

instance Show a => Show (Term a) where
    show _ = "Not implemented"

instance Show1 Term where showsPrec1 = showsPrec

instance Eq a => Eq (Term a) where
    e1 == e2 = go e1 [] e2 []
      where
        go (Var a) es (Var a') es' = a == a' && es == es'
        go (App a b) es e2 es' = go a (b:es) e2 es'
        go e1 es (App a b) es' = go e1 es a (b:es')
        go (Lam (Name n s)) es (Lam (Name n' s')) es' = es == es' &&
            let d = length n - length n'
                d' = -d
            in case () of
                _ | d  > 0 -> s == Scope (addApps d $ fmap (succ d) $ unscope s')
                _ | d' > 0 -> Scope (addApps d' $ fmap (succ d') $ unscope s) == s'
                _          -> s == s'
         where
            succ :: Int -> Var Int a -> Var Int a
            succ d (B i) = B (d + i)
            succ _ (F a) = F a
        go (Lam (Name n s)) es t es' =
            let (l1,l2) = splitAt (length es' - length es) es'
            in l2 == es && s == Scope (addApps (length n) $ Var $ F $ apps t l1)
        go t1 es t2@Lam{} es' = go t2 es' t1 es
        go (Arr a b) es (Arr a' b') es' = a == a' && b == b' && es == es'
        go e1@Pi{} es e2@Pi{} es' = es == es' && pcompare e1 e2 == Just EQ
        go (Pi fl a ns) es (Arr a' b') es' =
            a == a' && es == es' && fmap F b' == either (Pi fl $ fmap F a) id (namesToVar ns)
        go e@Arr{} es e'@Pi{} es' = go e' es' e es
        go (Con c _ as _) es (Con c' _ as' _) es' = c == c' && as ++ es == as' ++ es'
        go (FunCall n _) es (FunCall n' _) es' = n == n' && es == es'
        go (FunSyn n _) es (FunSyn n' _) es' = n == n' && es == es'
        go (Universe u) es (Universe u') es' = u == u' && es == es'
        go (DataType d as) es (DataType d' as') es' = d == d' && as ++ es == as' ++ es'
        go Interval es Interval es' = es == es'
        go (ICon c) es (ICon c') es' = c == c' && es == es'
        go (Path as) es (Path as') es' = as ++ es == as' ++ es'
        go (Path as) es (PathImp ma' b' c') es' = case as ++ es of
            a:b:c:es1 -> maybe True (\a' -> Lam (Name ["x"] (toScope $ fmap F a')) == a) ma'
                && b == b' && c == c' && es1 == es'
            _       -> False
        go e@PathImp{} es e'@Path{} es' = go e' es' e es
        go (PathImp ma b c) es (PathImp ma' b' c') es' = maybe True id (liftM2 (==) ma ma') && b == b' && c == c' && es == es'
        go (PCon f) es (PCon f') es' = maybe [] return f ++ es == maybe [] return f' ++ es'
        go (PCon e) es e' es' = case maybe [] return e ++ es of
            e1:es1 -> e1 == Lam (Name ["x"] $ Scope $ At (error "PCon") (error "PCon") (Var $ F e') $ Var $ B 0) && es1 == es'
            _ -> False
        go e es e'@PCon{} es' = go e' es' e es
        go (At _ _ a b) es (At _ _ a' b') es' = a == a' && b == b' && es == es'
        go (Coe as) es (Coe as') es' = as ++ es == as' ++ es'
        go (Iso as) es (Iso as') es' = as ++ es == as' ++ es'
        go (Squeeze as) es (Squeeze as') es' = as ++ es == as' ++ es'
        go _ _ _ _ = False
        
        addApps :: Int -> Term (Var Int a) -> Term (Var Int a)
        addApps 0 t = t
        addApps d t = addApps (d - 1) $ App t $ Var $ B (d - 1)

namesToVar :: Names n Term a -> Either (Names n Term (Var () a)) (Term (Var () a))
namesToVar (Name (_:ns) (Scope b)) | not (null ns) = Left $ Name ns $ Scope $ b >>= \v -> case v of
    B i | i == length ns - 1 -> return $ F $ Var $ B ()
        | otherwise          -> return (B i)
    F t                      -> fmap (F . Var . F) t
namesToVar (Name _ (Scope b)) = Right $ b >>= \v -> case v of
    B _ -> return $ B ()
    F t -> fmap F t

class POrd a where
    pcompare :: a -> a -> Maybe Ordering

instance Eq a => POrd (Term a) where
    pcompare (Pi fl a (Name n b)) (Pi fl' a' (Name n' b')) = contraCovariant (pcompare a a') $
        let d = length n - length n'
            d' = -d
        in case () of
            _ | d' > 0 -> pcompare (fromScope b) $ Pi fl' (fmap F a') (Name (drop (length n) n') $ Scope $ unscope b' >>= \v -> case v of
                B i | i >= d'   -> return $ F $ Var $ B (i - d')
                    | otherwise -> return (B i)
                F t             -> fmap (F . Var . F) t)
            _ | d > 0 -> pcompare (Pi fl (fmap F a) $ Name (drop (length n') n) $ Scope $ unscope b >>= \v -> case v of
                B i | i >= d    -> return $ F $ Var $ B (i - d)
                    | otherwise -> return (B i)
                F t             -> fmap (F . Var . F) t) (fromScope b')
            _ -> pcompare (fromScope b) (fromScope b')
    pcompare (Pi fl a ns) (Arr a' b')                         = contraCovariant (pcompare a a') $
        pcompare (either (Pi fl $ fmap F a) id $ namesToVar ns) (fmap F b')
    pcompare (Arr a b) (Pi fl a' ns')                         = contraCovariant (pcompare a a') $
        pcompare (fmap F b) (either (Pi fl $ fmap F a') id $ namesToVar ns')
    pcompare (Arr a b) (Arr a' b')                            = contraCovariant (pcompare a a') (pcompare b b')
    pcompare (Universe u) (Universe u')                       = Just $ compare (level u) (level u')
    pcompare (Path []) (Path [])                              = Just EQ
    pcompare (Path (Lam (Name [_] a):as))
             (Path (Lam (Name [_] a'):as'))                   = if as == as' then pcompare (fromScope a) (fromScope a')
                                                                                                         else Nothing
    pcompare (Path (a:as)) (Path (a':as'))                    = if as == as'          then pcompare a a' else Nothing
    pcompare (Path [a,b,c]) (PathImp Nothing b' c')           = if b == b' && c == c' then Just EQ       else Nothing
    pcompare (Path [Lam (Name [_] s),b,c])
             (PathImp (Just a') b' c')                        = if b == b' && c == c' then pcompare (fromScope s) (fmap F a')
                                                                                                         else Nothing
    pcompare (PathImp Nothing  b c) (Path [a',b',c'])         = if b == b' && c == c' then Just EQ       else Nothing
    pcompare (PathImp (Just a) b c)
             (Path [Lam (Name [_] s),b',c'])                  = if b == b' && c == c' then pcompare (fmap F a) (fromScope s)
                                                                                                         else Nothing
    pcompare (PathImp (Just a) b c) (PathImp (Just a') b' c') = if b == b' && c == c' then pcompare a a' else Nothing
    pcompare (PathImp _  b c) (PathImp _ b' c')               = if b == b' && c == c' then Just EQ       else Nothing
    pcompare e1 e2                                            = if e1 == e2           then Just EQ       else Nothing

contraCovariant :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
contraCovariant (Just LT) (Just r) | r == EQ || r == GT = Just GT
contraCovariant (Just EQ) r                             = r
contraCovariant (Just GT) (Just r) | r == LT || r == EQ = Just LT
contraCovariant _ _                                     = Nothing

lessOrEqual :: POrd a => a -> a -> Bool
lessOrEqual a b = case pcompare a b of
    Just r | r == EQ || r == LT -> True
    _                           -> False

greaterOrEqual :: POrd a => a -> a -> Bool
greaterOrEqual a b = case pcompare a b of
    Just r | r == EQ || r == GT -> True
    _                           -> False

instance Eq1   Term where (==#) = (==)

instance Functor  Term where fmap    = fmapDefault
instance Foldable Term where foldMap = foldMapDefault

instance Applicative Term where
    pure  = Var
    (<*>) = ap

instance Traversable Term where
    traverse f (Var a)               = Var                         <$> f a
    traverse f (App e1 e2)           = App                         <$> traverse f e1 <*> traverse f e2
    traverse f (Lam (Name n e))      = Lam . Name n                <$> traverse f e
    traverse f (At e1 e2 e3 e4)      = At                          <$> traverse f e1 <*> traverse f e2 <*> traverse f e3 <*> traverse f e4
    traverse f (Arr e1 e2)           = Arr                         <$> traverse f e1 <*> traverse f e2
    traverse f (Pi b e1 (Name n e2)) = (\e1' -> Pi b e1' . Name n) <$> traverse f e1 <*> traverse f e2
    traverse f (PathImp me1 e2 e3)   = PathImp                     <$> traverse (traverse f) me1 <*> traverse f e2 <*> traverse f e3
    traverse f (PCon e)              = PCon                        <$> traverse (traverse f) e
    traverse f (Path es)             = Path                        <$> traverse (traverse f) es
    traverse f (Con c n as cs)       = (\as' -> Con c n as' cs)    <$> traverse (traverse f) as
    traverse f (Coe as)              = Coe                         <$> traverse (traverse f) as
    traverse f (Iso as)              = Iso                         <$> traverse (traverse f) as
    traverse f (Squeeze as)          = Squeeze                     <$> traverse (traverse f) as
    traverse f (FunSyn n e)          = FunSyn n                    <$> traverse f e
    traverse f (DataType d as)       = DataType d                  <$> traverse (traverse f) as
    traverse _ (FunCall n cs)        = pure (FunCall n cs)
    traverse _ (Universe l)          = pure (Universe l)
    traverse _ Interval              = pure Interval
    traverse _ (ICon c)              = pure (ICon c)

instance Monad Term where
    return                     = Var
    Var a                >>= k = k a
    App e1 e2            >>= k = App  (e1 >>= k) (e2 >>= k)
    Lam e                >>= k = Lam  (e >>>= k)
    Arr e1 e2            >>= k = Arr  (e1 >>= k) (e2 >>= k)
    Pi b e1 e2           >>= k = Pi b (e1 >>= k) (e2 >>>= k)
    Con c n as cs        >>= k = Con c n (map (>>= k) as) cs
    FunCall n cs         >>= k = FunCall n cs
    FunSyn n e           >>= k = FunSyn n (e >>= k)
    Universe l           >>= _ = Universe l
    DataType d as        >>= k = DataType d $ map (>>= k) as
    Interval             >>= _ = Interval
    ICon c               >>= _ = ICon c
    Path es              >>= k = Path $ map (>>= k) es
    PathImp me1 e2 e3    >>= k = PathImp (fmap (>>= k) me1) (e2 >>= k) (e3 >>= k)
    PCon e               >>= k = PCon $ fmap (>>= k) e
    At e1 e2 e3 e4       >>= k = At (e1 >>= k) (e2 >>= k) (e3 >>= k) (e4 >>= k)
    Coe es               >>= k = Coe $ map (>>= k) es
    Iso es               >>= k = Iso $ map (>>= k) es
    Squeeze es           >>= k = Squeeze $ map (>>= k) es

data Pattern v = Pattern v [Pattern v]

instance Functor  Pattern where
    fmap f (Pattern v pats) = Pattern (f v) $ map (fmap f) pats

instance Foldable Pattern where
    foldMap f (Pattern v []) = f v
    foldMap f (Pattern _ [pat]) = foldMap f pat
    foldMap f (Pattern v (pat:pats)) = foldMap f pat `mappend` foldMap f (Pattern v pats)

collectDataTypes :: Term a                    -> [String]
collectDataTypes (Var _)                       = []
collectDataTypes (App e1 e2)                   = collectDataTypes e1 ++ collectDataTypes e2
collectDataTypes (Lam (Name _ (Scope e)))      = collectDataTypes e
collectDataTypes (Arr e1 e2)                   = collectDataTypes e1 ++ collectDataTypes e2
collectDataTypes (Pi _ e1 (Name _ (Scope e2))) = collectDataTypes e1 ++ collectDataTypes e2
collectDataTypes (Con _ _ as _)                = as >>= collectDataTypes
collectDataTypes (FunCall _ _)                 = []
collectDataTypes (FunSyn _ _)                  = []
collectDataTypes (DataType d as)               = d : (as >>= collectDataTypes)
collectDataTypes (Universe _)                  = []
collectDataTypes Interval                      = []
collectDataTypes (ICon _)                      = []
collectDataTypes (Path es)                     = es >>= collectDataTypes
collectDataTypes (PathImp me1 e2 e3)           = maybe [] collectDataTypes me1 ++ collectDataTypes e2 ++ collectDataTypes e3
collectDataTypes (PCon me)                     = maybe [] collectDataTypes me
collectDataTypes (At e1 e2 e3 e4)              = collectDataTypes e1 ++ collectDataTypes e2 ++ collectDataTypes e3 ++ collectDataTypes e4
collectDataTypes (Coe es)                      = es >>= collectDataTypes
collectDataTypes (Iso es)                      = es >>= collectDataTypes
collectDataTypes (Squeeze es)                  = es >>= collectDataTypes

apps :: Term a -> [Term a] -> Term a
apps e [] = e
apps (Con c n as cs) es = Con c n (as ++ es) cs
apps (Coe as) es = Coe (as ++ es)
apps (Iso as) es = Iso (as ++ es)
apps (Squeeze as) es = Squeeze (as ++ es)
apps e1 (e2:es) = apps (App e1 e2) es
