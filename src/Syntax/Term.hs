module Syntax.Term
    ( Term(..)
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
import Control.Monad.State

import Syntax.Name
import Syntax.ErrorDoc

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
data RTPattern = RTPattern Int [RTPattern] | RTPatternVar

instance Eq a => Eq (Term a) where
    Var a        == Var a'         = a == a'
    App a b      == App a' b'      = a == a' && b == b'
    Lam n        == Lam n'         = n == n'
    Arr a b      == Arr a' b'      = a == a' && b == b'
    Pi _ a b     == Pi _ a' b'     = a == a' && b == b'
    Con c _ a    == Con c' _ a'    = c == c' && a == a'
    FunCall n _  == FunCall n' _   = n == n'
    FunSyn n _   == FunSyn n' _    = n == n'
    Universe u   == Universe u'    = u == u'
    DataType d a == DataType d' a' = d == d' && a == a'
    _            == _              = False

class POrd a where
    pcompare :: a -> a -> Maybe Ordering

instance Eq a => POrd (Term a) where
    pcompare (Arr a b) (Arr a' b') = contraCovariant (pcompare a a') (pcompare b b')
    pcompare (Pi _ a (Name _ (Scope b))) (Pi _ a' (Name _ (Scope b'))) = contraCovariant (pcompare a a') (pcompare b b')
    pcompare (Universe u) (Universe u') = Just $ compare (level u) (level u')
    pcompare e1 e2 = if e1 == e2 then Just EQ else Nothing

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
    traverse f (Arr e1 e2)           = Arr                         <$> traverse f e1 <*> traverse f e2
    traverse f (Pi b e1 (Name n e2)) = (\e1' -> Pi b e1' . Name n) <$> traverse f e1 <*> traverse f e2
    traverse f (Con c n as)          = Con c n                     <$> traverse (traverse f) as
    traverse f (FunCall n cs)        = FunCall n                   <$> traverse (\(Name p c) -> Name p <$> traverse f c) cs
    traverse f (FunSyn n e)          = FunSyn n                    <$> traverse f e
    traverse f (DataType d as)       = DataType d                  <$> traverse (traverse f) as
    traverse f (Universe l)          = pure (Universe l)

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

data Pattern v = Pattern v [Pattern v]

instance Functor  Pattern where
    fmap f (Pattern v pats) = Pattern (f v) $ map (fmap f) pats

instance Foldable Pattern where
    foldMap f (Pattern v []) = f v
    foldMap f (Pattern _ [pat]) = foldMap f pat
    foldMap f (Pattern v (pat:pats)) = foldMap f pat `mappend` foldMap f (Pattern v pats)

collectDataTypes :: Term a -> [String]
collectDataTypes (Var _) = []
collectDataTypes (App e1 e2) = collectDataTypes e1 ++ collectDataTypes e2
collectDataTypes (Lam (Name _ (Scope e))) = collectDataTypes e
collectDataTypes (Arr e1 e2) = collectDataTypes e1 ++ collectDataTypes e2
collectDataTypes (Pi _ e1 (Name _ (Scope e2))) = collectDataTypes e1 ++ collectDataTypes e2
collectDataTypes (Con _ _ as) = as >>= collectDataTypes
collectDataTypes (FunCall _ _) = []
collectDataTypes (FunSyn _ _) = []
collectDataTypes (DataType d as) = d : (as >>= collectDataTypes)
collectDataTypes (Universe _) = []

apps :: Term a -> [Term a] -> Term a
apps e [] = e
apps (Con c n as) es = Con c n (as ++ es)
apps e1 (e2:es) = apps (App e1 e2) es
