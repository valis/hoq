{-# LANGUAGE Rank2Types #-}

module Syntax.Term
    ( Term(..), ClosedTerm
    , Level(..), level
    , module Syntax.Name, module Bound
    , apps
    , ppTerm, ppOpenTerm
    ) where

import Prelude.Extras
import Data.Function
import Bound
import Text.PrettyPrint
import Data.Traversable
import Data.Foldable
import Control.Applicative hiding (empty)
import Control.Monad

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
    | Universe Level
    deriving Eq
type ClosedTerm = forall a. Term a

instance Eq1 Term where (==#) = (==)

instance Functor  Term where fmap    = fmapDefault
instance Foldable Term where foldMap = foldMapDefault

instance Applicative Term where
  pure  = Var
  (<*>) = ap

instance Traversable Term where
  traverse f (Var a)               = Var                         <$> f a
  traverse f (App e1 e2)           = App                         <$> traverse f e1 <*> traverse f e2
  traverse f (Lam (Name n e))      = (Lam . Name n)              <$> traverse f e
  traverse f (Arr e1 e2)           = Arr                         <$> traverse f e1 <*> traverse f e2
  traverse f (Pi b e1 (Name n e2)) = (\e1' -> Pi b e1' . Name n) <$> traverse f e1 <*> traverse f e2
  traverse f (Universe l)          = pure (Universe l)

instance Monad Term where
    return = Var
    Var a      >>= k = k a
    App e1 e2  >>= k = App  (e1 >>= k) (e2 >>= k)
    Lam e      >>= k = Lam  (e >>>= k)
    Arr e1 e2  >>= k = Arr  (e1 >>= k) (e2 >>= k)
    Pi b e1 e2 >>= k = Pi b (e1 >>= k) (e2 >>>= k)
    Universe l >>= _ = Universe l

apps :: Term a -> [Term a] -> Term a
apps e [] = e
apps e1 (e2:es) = apps (App e1 e2) es

ppTerm :: ClosedTerm -> Doc
ppTerm t = ppTermCtx [] t

ppOpenTerm :: Term String -> Doc
ppOpenTerm t = ppTermCtx (map (\s -> (s,0)) (toList t)) (fmap text t)

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
prec Arr{}      = 8
prec Pi{}       = 8
prec Lam{}      = 8
