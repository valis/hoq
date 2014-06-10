{-# LANGUAGE Rank2Types #-}

module Syntax.Term
    ( Term(..), ClosedTerm
    , Def(..)
    , Level(..), level
    , Pattern(..)
    , module Syntax.Name, module Bound
    , apps
    , ppClosedTerm, ppTerm, ppDef, ppPattern
    ) where

import Prelude.Extras
import Data.Function
import Bound
import Text.PrettyPrint
import Data.Traversable hiding (mapM)
import Data.Foldable hiding (msum)
import Data.Monoid(mappend)
import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.State

import Syntax.Name

data Level = Level Int | NoLevel

instance Eq Level where
    (==) = (==) `on` level

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
    | Universe Level
    deriving Show
type ClosedTerm = forall a. Term a

instance Eq a => Eq (Term a) where
    Var a == Var a' = a == a'
    Lam n == Lam n' = n == n'
    Arr a b == Arr a' b' = a == a' && b == b'
    Pi _ a b == Pi _ a' b' = a == a' && b == b'
    Con c _ a == Con c' _ a' = c == c' && a == a'
    Universe u == Universe u' = u == u'

instance Eq1   Term where (==#) = (==)
instance Show1 Term where showsPrec1 = showsPrec

instance Functor  Term where fmap    = fmapDefault
instance Foldable Term where foldMap = foldMapDefault

instance Applicative Term where
  pure  = Var
  (<*>) = ap

instance Traversable Term where
  traverse f (Var a)               = Var                         <$> f a
  traverse f (App e1 e2)           = app                         <$> traverse f e1 <*> traverse f e2
  traverse f (Lam (Name n e))      = (Lam . Name n)              <$> traverse f e
  traverse f (Arr e1 e2)           = Arr                         <$> traverse f e1 <*> traverse f e2
  traverse f (Pi b e1 (Name n e2)) = (\e1' -> Pi b e1' . Name n) <$> traverse f e1 <*> traverse f e2
  traverse f (Con c n as)          = Con c n                     <$> sequenceA (map (traverse f) as)
  traverse f (Universe l)          = pure (Universe l)

instance Monad Term where
    return = Var
    Var a      >>= k = k a
    App e1 e2  >>= k = App  (e1 >>= k) (e2 >>= k)
    Lam e      >>= k = Lam  (e >>>= k)
    Arr e1 e2  >>= k = Arr  (e1 >>= k) (e2 >>= k)
    Pi b e1 e2 >>= k = Pi b (e1 >>= k) (e2 >>>= k)
    Con c n as >>= k = Con c n $ map (>>= k) as
    Universe l >>= _ = Universe l

data Def f a = Def
    { defType :: f a
    , defTerm :: [Name [Pattern String] Int f a]
    } | Syn
    { defType :: f a
    , synTerm :: f a
    }

instance Bound Def where
    Def ty cases >>>= k = Def (ty >>= k) $ map (\(Name name term) -> Name name (term >>>= k)) cases
    Syn ty term  >>>= k = Syn (ty >>= k) (term >>= k)

data Pattern v = Pattern v [Pattern v]

instance Functor  Pattern where
    fmap f (Pattern v pats) = Pattern (f v) $ map (fmap f) pats

instance Foldable Pattern where
    foldMap f (Pattern v []) = f v
    foldMap f (Pattern _ [pat]) = foldMap f pat
    foldMap f (Pattern v (pat:pats)) = foldMap f pat `mappend` foldMap f (Pattern v pats)

app :: Term a -> Term a -> Term a
app (Con c n as) a = Con c n $ as ++ [a]
app b a = App b a

apps :: Term a -> [Term a] -> Term a
apps e [] = e
apps (Con c n as) es = Con c n (as ++ es)
apps e1 (e2:es) = apps (App e1 e2) es

-- Pretty printers

ppPattern :: Pattern Doc -> Doc
ppPattern (Pattern v pats) = v <+> hsep (map (parens . ppPattern) pats)

ppDef :: String -> Def Term String -> Doc
ppDef n d = text n <+>     colon  <+> ppTerm (defType d)
         $$ text n <+> case d of
            Def _ cases -> vcat $ flip map cases $ \(Name pats term) ->
                           hsep (map (parens . ppPattern . fmap text) pats) <+>
                           equals <+> ppTerm (instantiate (\i -> Var $ toList (Pattern n pats) !! i) term)
            Syn _ term  -> equals <+> ppTerm term

ppClosedTerm :: ClosedTerm -> Doc
ppClosedTerm t = ppTermCtx [] t

ppTerm :: Term String -> Doc
ppTerm t = ppTermCtx (map (\s -> (s,0)) (toList t)) (fmap text t)

ppTermCtx :: [(String,Int)] -> Term Doc -> Doc
ppTermCtx _ (Var d) = d
ppTermCtx _ (Universe l) = text $ "Type" ++ show l
ppTermCtx ctx t@(App e1 e2) = ppTermPrec (prec t) ctx e1 <+> ppTermPrec (prec t + 1) ctx e2
ppTermCtx ctx t@(Arr e1 e2) = ppTermPrec (prec t + 1) ctx e1 <+> arrow <+> ppTermPrec (prec t) ctx e2
ppTermCtx ctx t@(Pi b e n) =
    let (as, t') = ppNamesPrec (prec t) ctx n
    in parens (hsep as <+> colon <+> ppTermCtx ctx e) <+> (if b then arrow else empty) <+> t'
ppTermCtx ctx t@(Lam n) =
    let (as, t') = ppNamesPrec (prec t) ctx n
    in text "\\" <> hsep as <+> arrow <+> t'
ppTermCtx ctx t@(Con _ n as) = text n <+> hsep (map (ppTermPrec (prec t + 1) ctx) as)

ppNamesPrec :: Int -> [(String,Int)] -> Names String Term Doc -> ([Doc], Doc)
ppNamesPrec p ctx n =
    let (as, ctx', t) = instantiateNames ctx (\d -> maybe (text d) $ \i -> text d <> int i) n
    in (as, ppTermPrec p ctx' t)

ppTermPrec :: Int -> [(String,Int)] -> Term Doc -> Doc
ppTermPrec p ctx t = if p > prec t then parens (ppTermCtx ctx t) else ppTermCtx ctx t

arrow :: Doc
arrow = text "->"

prec :: Term a -> Int
prec Var{}      = 10
prec Universe{} = 10
prec App{}      = 9
prec Con{}      = 9
prec Arr{}      = 8
prec Pi{}       = 8
prec Lam{}      = 8
