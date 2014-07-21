module Syntax.Term
    ( module Syntax.Parser.Term
    , POrd(..), lessOrEqual
    , apps, collect, dropOnePi
    ) where

import Prelude.Extras
import Data.Function
import Data.Traversable hiding (mapM)
import Data.Foldable as F hiding (msum)
import Control.Applicative
import Control.Monad

import Syntax.Parser.Term

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

instance Eq PIdent where
    PIdent _ s == PIdent _ s' = s == s'

instance Eq a => Eq (Term p a) where
    e1 == e2 = go e1 [] e2 []
      where
        go :: Eq a => Term p a -> [Term p a] -> Term p a -> [Term p a] -> Bool
        go (Var a) es (Var a') es' = a == a' && es == es'
        go (App a b) es e2 es' = go a (b:es) e2 es'
        go e1 es (App a b) es' = go e1 es a (b:es')
        go (Lam _ s) es (Lam _ s') es' = s == s' && es == es'
        go (Lam p (Scope1 _ s)) es t es' =
            let (l1,l2) = splitAt (length es' - length es) es'
            in l2 == es && go s [] (fmap Free t) (map (fmap Free) l1 ++ [Var $ Bound p])
        go t es t'@Lam{} es' = go t' es' t es
        go e1@Pi{} es e2@Pi{} es' = pcompare e1 e2 == Just EQ && es == es'
        go (Con _ c _ _ as) es (Con _ c' _ _ as') es' = c == c' && as ++ es == as' ++ es'
        go (FunCall _ n _) es (FunCall _ n' _) es' = n == n' && es == es'
        go (FunSyn _ n _) es (FunSyn _ n' _) es' = n == n' && es == es'
        go (Universe _ u) es (Universe _ u') es' = u == u' && es == es'
        go (DataType _ d _ as) es (DataType _ d' _ as') es' = d == d' && as ++ es == as' ++ es'
        go (Interval _) es (Interval _) es' = es == es'
        go (ICon _ c) es (ICon _ c') es' = c == c' && es == es'
        go (Path _ Explicit a as) es (Path _ Explicit a' as') es' = a == a' && as ++ es == as' ++ es'
        go (Path _ _ _ as) es (Path _ _ _ as') es' = as ++ es == as' ++ es'
        go (PCon _ f) es (PCon _ f') es' = maybe [] return f ++ es == maybe [] return f' ++ es'
        go (PCon p e) es e' es' = case maybe [] return e ++ es of
            e1:es1 -> e1 == Lam p (Scope1 "" $ At Nothing (fmap Free e') $ Var $ Bound p) && es1 == es'
            _ -> False
        go e es e'@PCon{} es' = go e' es' e es
        go (At _ a b) es (At _ a' b') es' = a == a' && b == b' && es == es'
        go (Coe _ as) es (Coe _ as') es' = as ++ es == as' ++ es'
        go (Iso _ as) es (Iso _ as') es' = as ++ es == as' ++ es'
        go (Squeeze _ as) es (Squeeze _ as') es' = as ++ es == as' ++ es'
        go _ _ _ _ = False

instance Eq a => Eq (Type p a) where
    Type t _ == Type t' _ = t == t'

instance Eq1 (Term p) where (==#) = (==)

class POrd a where
    pcompare :: a -> a -> Maybe Ordering

instance Eq a => POrd (Term p a) where
    pcompare (Pi _ a (ScopeTerm b) _) (Pi p' a' b'@Scope{} lvl') =
        contraCovariant (pcompare a a') $ pcompare (fmap Free b) (unScope1 $ dropOnePi p' a' b' lvl')
    pcompare (Pi p a b@Scope{} lvl) (Pi _ a' (ScopeTerm b') _) =
        contraCovariant (pcompare a a') $ pcompare (unScope1 $ dropOnePi p a b lvl) (fmap Free b')
    pcompare (Pi p a b lvl) (Pi p' a' b' lvl') = contraCovariant (pcompare a a') $ pcompareScopes p a b lvl p' a' b' lvl'
      where
        pcompareScopes :: Eq a => p -> Type p a -> Scope String p (Term p) a -> Level
            -> p -> Type p a -> Scope String p (Term p) a -> Level -> Maybe Ordering
        pcompareScopes _ _ (ScopeTerm b) _   _  _  (ScopeTerm b') _      = pcompare b b'
        pcompareScopes _ _ (ScopeTerm b) _   p' a'            b'  lvl'   = pcompare b (Pi p' a' b' lvl')
        pcompareScopes p a            b  lvl _  _  (ScopeTerm b') _      = pcompare (Pi p a b lvl) b'
        pcompareScopes p a (Scope _   b) lvl p' a' (Scope _   b') lvl'   =
            pcompareScopes p (fmap Free a) b lvl p' (fmap Free a') b' lvl'
    pcompare (Universe _ u) (Universe _ u') = Just $ compare (level u) (level u')
    pcompare e1 e2 = if e1 == e2 then Just EQ else Nothing

instance Eq a => POrd (Type p a) where
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

instance Functor  (Term p) where fmap    = fmapDefault
instance Foldable (Term p) where foldMap = foldMapDefault

instance Functor  (Type p) where
    fmap f (Type t l) = Type (fmap f t) l

instance Applicative (Term p) where
    pure  = Var
    (<*>) = ap

instance Traversable (Term p) where
    traverse f (Var a)              = Var            <$> f a
    traverse f (App e1 e2)          = App            <$> traverse f e1 <*> traverse f e2
    traverse f (Lam p s)            = Lam p          <$> traverse f s
    traverse f (At me12 e3 e4)      =
        At <$> maybe (pure Nothing) (\(e1,e2) -> (\r1 r2 -> Just (r1,r2)) <$>
        traverse f e1 <*> traverse f e2) me12 <*> traverse f e3 <*> traverse f e4
    traverse f (Pi p (Type e1 lvl1) e2 lvl2) =
        (\e1' e2' -> Pi p (Type e1' lvl1) e2' lvl2) <$> traverse f e1 <*> traverse f e2
    traverse f (Path p h me es)     = Path p h       <$> traverse (traverse f) me <*> traverse (traverse f) es
    traverse f (PCon p e)           = PCon p         <$> traverse (traverse f) e
    traverse f (Con p c n cs as)    = Con p c n cs   <$> traverse (traverse f) as
    traverse f (Coe p as)           = Coe p          <$> traverse (traverse f) as
    traverse f (Iso p as)           = Iso p          <$> traverse (traverse f) as
    traverse f (Squeeze p as)       = Squeeze p      <$> traverse (traverse f) as
    traverse f (DataType p d e as)  = DataType p d e <$> traverse (traverse f) as
    traverse _ (FunSyn p n e)       = pure (FunSyn p n e)
    traverse _ (FunCall p n cs)     = pure (FunCall p n cs)
    traverse _ (Universe p l)       = pure (Universe p l)
    traverse _ (Interval p)         = pure (Interval p)
    traverse _ (ICon p c)           = pure (ICon p c)

instance Monad (Term p) where
    return                            = Var
    Var a                       >>= k = k a
    App e1 e2                   >>= k = App (e1 >>= k) (e2 >>= k)
    Lam p e                     >>= k = Lam p (e >>>= k)
    Pi p (Type e1 lvl1) e2 lvl2 >>= k = Pi p (Type (e1 >>= k) lvl1) (e2 >>>= k) lvl2
    Con p c n cs as             >>= k = Con p c n cs (map (>>= k) as)
    FunCall p n cs              >>= k = FunCall p n cs
    FunSyn p n e                >>= _ = FunSyn p n e
    Universe p l                >>= _ = Universe p l
    DataType p d e as           >>= k = DataType p d e $ map (>>= k) as
    Interval p                  >>= _ = Interval p
    ICon p c                    >>= _ = ICon p c
    Path p h me1 es             >>= k = Path p h (fmap (>>= k) me1) $ map (>>= k) es
    PCon p e                    >>= k = PCon p $ fmap (>>= k) e
    At me12 e3 e4               >>= k = At (fmap (\(e1,e2) -> (e1 >>= k, e2 >>= k)) me12) (e3 >>= k) (e4 >>= k)
    Coe p es                    >>= k = Coe p $ map (>>= k) es
    Iso p es                    >>= k = Iso p $ map (>>= k) es
    Squeeze p es                >>= k = Squeeze p $ map (>>= k) es

apps :: Term p a -> [Term p a] -> Term p a
apps e [] = e
apps e1 (e2:es) = apps (App e1 e2) es

collect :: Term p a -> Term p a
collect term = go term []
  where
    go (App e1 e2)          ts  = go e1 (e2:ts)
    go (Con p a b c es)     ts  = Con p a b c       (es ++ ts)
    go (DataType p a b es)  ts  = DataType p a b    (es ++ ts)
    go (Path p a b es)      ts  = Path p a b        (es ++ ts)
    go (Coe p es)           ts  = Coe p             (es ++ ts)
    go (Iso p es)           ts  = Iso p             (es ++ ts)
    go (Squeeze p es)       ts  = Squeeze p         (es ++ ts)
    go _ _ = term

dropOnePi :: p -> Type p a -> Scope String p (Term p) a -> Level -> Scope1 String p (Term p) a
dropOnePi _ _ (ScopeTerm b) _ = Scope1 "_" (fmap Free b)
dropOnePi _ _ (Scope s (ScopeTerm b)) _ = Scope1 s b
dropOnePi p a (Scope s b) lvl = Scope1 s $ Pi p (fmap Free a) b lvl
