module Syntax.Term
    ( Term(..), Type(..)
    , Level(..), level
    , Explicit(..)
    , module Syntax.Scope, module Syntax.Pattern
    , POrd(..), lessOrEqual
    , apps, dropOnePi
    ) where

import Prelude.Extras
import Data.Function
import Data.Traversable hiding (mapM)
import Data.Foldable hiding (msum)
import Control.Applicative
import Control.Monad

import Syntax.Scope
import Syntax.Pattern

data Level = Level Int | NoLevel

instance Eq Level where
    (==) = (==) `on` level

instance Ord Level where
    compare = compare `on` level

instance Show Level where
    show = show . level

instance Enum Level where
    toEnum 0 = NoLevel
    toEnum n = Level n
    fromEnum = level

level :: Level -> Int
level (Level l) = l
level NoLevel = 0

data Term a
    = Var a
    | App (Term a) (Term a)
    | Lam (Scope1 String Term a)
    | Pi (Type a) (Scope String Term a) Level
    | Con Int String [([Pattern (Closed (Scope String Term))], Closed (Scope String Term))] [Term a]
    | FunCall String [([Pattern (Closed (Scope String Term))], Closed (Scope String Term))]
    | FunSyn  String (Term a)
    | Universe Level
    | DataType String Int [Term a]
    | Interval
    | ICon ICon
    | Path Explicit (Maybe (Term a)) [Term a]
    | PCon (Maybe (Term a))
    | At (Term a) (Term a) (Term a) (Term a)
    | Coe [Term a]
    | Iso [Term a]
    | Squeeze [Term a]
data Type a = Type (Term a) Level
data Explicit = Explicit | Implicit

instance Eq a => Eq (Term a) where
    e1 == e2 = go e1 [] e2 []
      where
        go :: Eq a => Term a -> [Term a] -> Term a -> [Term a] -> Bool
        go (Var a) es (Var a') es' = a == a' && es == es'
        go (App a b) es e2 es' = go a (b:es) e2 es'
        go e1 es (App a b) es' = go e1 es a (b:es')
        go (Lam s) es (Lam s') es' = s == s' && es == es'
        go (Lam (Scope1 _ s)) es t es' =
            let (l1,l2) = splitAt (length es' - length es) es'
            in l2 == es && go s [] (fmap Free t) (map (fmap Free) l1 ++ [Var Bound])
        go t es t'@Lam{} es' = go t' es' t es
        go e1@Pi{} es e2@Pi{} es' = pcompare e1 e2 == Just EQ && es == es'
        go (Con c _ _ as) es (Con c' _ _ as') es' = c == c' && as ++ es == as' ++ es'
        go (FunCall n _) es (FunCall n' _) es' = n == n' && es == es'
        go (FunSyn n _) es (FunSyn n' _) es' = n == n' && es == es'
        go (Universe u) es (Universe u') es' = u == u' && es == es'
        go (DataType d _ as) es (DataType d' _ as') es' = d == d' && as ++ es == as' ++ es'
        go Interval es Interval es' = es == es'
        go (ICon c) es (ICon c') es' = c == c' && es == es'
        go (Path Explicit a as) es (Path Explicit a' as') es' = a == a' && as ++ es == as' ++ es'
        go (Path _ _ as) es (Path _ _ as') es' = as ++ es == as' ++ es'
        go (PCon f) es (PCon f') es' = maybe [] return f ++ es == maybe [] return f' ++ es'
        go (PCon e) es e' es' = case maybe [] return e ++ es of
            e1:es1 -> e1 == Lam (Scope1 "" $ At (error "") (error "") (fmap Free e') $ Var Bound) && es1 == es'
            _ -> False
        go e es e'@PCon{} es' = go e' es' e es
        go (At _ _ a b) es (At _ _ a' b') es' = a == a' && b == b' && es == es'
        go (Coe as) es (Coe as') es' = as ++ es == as' ++ es'
        go (Iso as) es (Iso as') es' = as ++ es == as' ++ es'
        go (Squeeze as) es (Squeeze as') es' = as ++ es == as' ++ es'
        go _ _ _ _ = False

instance Eq a => Eq (Type a) where
    Type t _ == Type t' _ = t == t'

instance Eq1 Term where (==#) = (==)

class POrd a where
    pcompare :: a -> a -> Maybe Ordering

instance Eq a => POrd (Term a) where
    pcompare (Pi a (ScopeTerm b) _) (Pi a' b'@Scope{} lvl') =
        contraCovariant (pcompare a a') $ pcompare (fmap Free b) (dropOnePi a' b' lvl')
    pcompare (Pi a b@Scope{} lvl) (Pi a' (ScopeTerm b') _) =
        contraCovariant (pcompare a a') $ pcompare (dropOnePi a b lvl) (fmap Free b')
    pcompare (Pi a b lvl) (Pi a' b' lvl') = contraCovariant (pcompare a a') $ pcompareScopes a b lvl a' b' lvl'
      where
        pcompareScopes :: Eq a => Type a -> Scope String Term a -> Level -> Type a -> Scope String Term a -> Level -> Maybe Ordering
        pcompareScopes _ (ScopeTerm b) _   _  (ScopeTerm b') _    = pcompare b b'
        pcompareScopes _ (ScopeTerm b) _   a'            b'  lvl' = pcompare b (Pi a' b' lvl')
        pcompareScopes a            b  lvl _  (ScopeTerm b') _    = pcompare (Pi a b lvl) b'
        pcompareScopes a (Scope _   b) lvl a' (Scope _   b') lvl' = pcompareScopes (fmap Free a) b lvl (fmap Free a') b' lvl'
    pcompare (Universe u) (Universe u') = Just $ compare (level u) (level u')
    pcompare e1 e2 = if e1 == e2 then Just EQ else Nothing

instance Eq a => POrd (Type a) where
    pcompare (Type t _) (Type t' _) = pcompare t t'

contraCovariant :: Maybe Ordering -> Maybe Ordering -> Maybe Ordering
contraCovariant (Just LT) (Just r) | r == EQ || r == GT = Just GT
contraCovariant (Just EQ) r                             = r
contraCovariant (Just GT) (Just r) | r == LT || r == EQ = Just LT
contraCovariant _ _                                     = Nothing

lessOrEqual :: POrd a => a -> a -> Bool
lessOrEqual a b = case pcompare a b of
    Just r | r == EQ || r == LT -> True
    _                           -> False

instance Functor  Term where fmap    = fmapDefault
instance Foldable Term where foldMap = foldMapDefault

instance Functor  Type where
    fmap f (Type t l) = Type (fmap f t) l

instance Applicative Term where
    pure  = Var
    (<*>) = ap

instance Traversable Term where
    traverse f (Var a)           = Var          <$> f a
    traverse f (App e1 e2)       = App          <$> traverse f e1 <*> traverse f e2
    traverse f (Lam s)           = Lam          <$> traverse f s
    traverse f (At e1 e2 e3 e4)  = At           <$> traverse f e1 <*> traverse f e2 <*> traverse f e3 <*> traverse f e4
    traverse f (Pi (Type e1 lvl1) e2 lvl2) = (\e1' e2' -> Pi (Type e1' lvl1) e2' lvl2) <$> traverse f e1 <*> traverse f e2
    traverse f (Path h me es)    = Path h       <$> traverse (traverse f) me <*> traverse (traverse f) es
    traverse f (PCon e)          = PCon         <$> traverse (traverse f) e
    traverse f (Con c n cs as)   = Con c n cs   <$> traverse (traverse f) as
    traverse f (Coe as)          = Coe          <$> traverse (traverse f) as
    traverse f (Iso as)          = Iso          <$> traverse (traverse f) as
    traverse f (Squeeze as)      = Squeeze      <$> traverse (traverse f) as
    traverse f (FunSyn n e)      = FunSyn n     <$> traverse f e
    traverse f (DataType d e as) = DataType d e <$> traverse (traverse f) as
    traverse _ (FunCall n cs)    = pure (FunCall n cs)
    traverse _ (Universe l)      = pure (Universe l)
    traverse _ Interval          = pure Interval
    traverse _ (ICon c)          = pure (ICon c)

instance Monad Term where
    return                          = Var
    Var a                     >>= k = k a
    App e1 e2                 >>= k = App (e1 >>= k) (e2 >>= k)
    Lam e                     >>= k = Lam (e >>>= k)
    Pi (Type e1 lvl1) e2 lvl2 >>= k = Pi (Type (e1 >>= k) lvl1) (e2 >>>= k) lvl2
    Con c n cs as             >>= k = Con c n cs (map (>>= k) as)
    FunCall n cs              >>= k = FunCall n cs
    FunSyn n e                >>= k = FunSyn n (e >>= k)
    Universe l                >>= _ = Universe l
    DataType d e as           >>= k = DataType d e $ map (>>= k) as
    Interval                  >>= _ = Interval
    ICon c                    >>= _ = ICon c
    Path h me1 es             >>= k = Path h (fmap (>>= k) me1) $ map (>>= k) es
    PCon e                    >>= k = PCon $ fmap (>>= k) e
    At e1 e2 e3 e4            >>= k = At (e1 >>= k) (e2 >>= k) (e3 >>= k) (e4 >>= k)
    Coe es                    >>= k = Coe $ map (>>= k) es
    Iso es                    >>= k = Iso $ map (>>= k) es
    Squeeze es                >>= k = Squeeze $ map (>>= k) es

apps :: Term a -> [Term a] -> Term a
apps e [] = e
apps e1 (e2:es) = apps (App e1 e2) es

dropOnePi :: Type a -> Scope String Term a -> Level -> Term (Scoped a)
dropOnePi _ (ScopeTerm b) _ = fmap Free b
dropOnePi _ (Scope _ (ScopeTerm b)) _ = b
dropOnePi a (Scope _ b) lvl = Pi (fmap Free a) b lvl
