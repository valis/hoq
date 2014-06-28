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
    | Con Int String [Term a]
    | FunCall String [Names RTPattern Term a]
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
    deriving Show
data ICon = ILeft | IRight deriving (Eq,Show)
data RTPattern = RTPattern Int [RTPattern] | RTPatternVar | RTPatternI ICon deriving Show

instance Show1 Term where showsPrec1 = showsPrec

instance Eq a => Eq (Term a) where
    Var a          == Var a'            = a == a'
    App a b        == App a' b'         = a == a' && b == b'
    Lam n          == Lam n'            = n == n'
    Arr a b        == Arr a' b'         = a == a' && b == b'
    Pi _ a b       == Pi _ a' b'        = a == a' && b == b'
    Con c _ a      == Con c' _ a'       = c == c' && a == a'
    FunCall n _    == FunCall n' _      = n == n'
    FunSyn n _     == FunSyn n' _       = n == n'
    Universe u     == Universe u'       = u == u'
    DataType d a   == DataType d' a'    = d == d' && a == a'
    Interval       == Interval          = True
    ICon c         == ICon c'           = c == c'
    Path as        == Path as'          = as == as'
    Path [a,b,c]   == PathImp ma' b' c' = maybe True (== a) ma' && b == b' && c == c'
    PathImp ma b c == Path [a',b',c']   = maybe True (== a') ma && b == b' && c == c'
    PathImp ma b c == PathImp ma' b' c' = maybe True id (liftM2 (==) ma ma') && b == b' && c == c'
    PCon f         == PCon f'           = f == f'
    At _ _ a b     == At _ _ a' b'      = a == a' && b == b'
    Coe as         == Coe as'           = as == as'
    Iso as         == Iso as'           = as == as'
    Squeeze as     == Squeeze as'       = as == as'
    _              == _                 = False

class POrd a where
    pcompare :: a -> a -> Maybe Ordering

instance Eq a => POrd (Term a) where
    pcompare (Pi _ a (Name _ (Scope b))) (Pi _ a' (Name _ (Scope b')))
                                                              = contraCovariant (pcompare a a') (pcompare b b')
    pcompare (Arr a b) (Arr a' b')                            = contraCovariant (pcompare a a') (pcompare b b')
    pcompare (Universe u) (Universe u')                       = Just $ compare (level u) (level u')
    pcompare (Path []) (Path [])                              = Just EQ
    pcompare (Path (a:as)) (Path (a':as'))                    = if as == as'          then pcompare a a' else Nothing
    pcompare (Path [a,b,c]) (PathImp Nothing   b' c')         = if b == b' && c == c' then Just EQ       else Nothing
    pcompare (Path [a,b,c]) (PathImp (Just a') b' c')         = if b == b' && c == c' then pcompare a a' else Nothing
    pcompare (PathImp Nothing  b c) (Path [a',b',c'])         = if b == b' && c == c' then Just EQ       else Nothing
    pcompare (PathImp (Just a) b c) (Path [a',b',c'])         = if b == b' && c == c' then pcompare a a' else Nothing
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
    traverse f (Con c n as)          = Con c n                     <$> traverse (traverse f) as
    traverse f (Coe as)              = Coe                         <$> traverse (traverse f) as
    traverse f (Iso as)              = Iso                         <$> traverse (traverse f) as
    traverse f (Squeeze as)          = Squeeze                     <$> traverse (traverse f) as
    traverse f (FunCall n cs)        = FunCall n                   <$> traverse (\(Name p c) -> Name p <$> traverse f c) cs
    traverse f (FunSyn n e)          = FunSyn n                    <$> traverse f e
    traverse f (DataType d as)       = DataType d                  <$> traverse (traverse f) as
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
    Con c n as           >>= k = Con c n $ map (>>= k) as
    FunCall n cs         >>= k = FunCall n $ map (>>>= k) cs
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
collectDataTypes (Con _ _ as)                  = as >>= collectDataTypes
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
apps (Con c n as) es = Con c n (as ++ es)
apps e1 (e2:es) = apps (App e1 e2) es
