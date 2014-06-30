module Syntax.PrettyPrinter
    ( ppTerm
    ) where

import Text.PrettyPrint
import Data.Foldable

import Syntax.Term
import qualified Syntax.ErrorDoc as E

instance E.Pretty1 Term where
    pretty1 t = ppTermCtx (map (\s -> (s,0)) (toList $ fmap render t)) t

ppTerm :: Term String -> Doc
ppTerm t = ppTermCtx (map (\s -> (s,0)) (toList t)) (fmap text t)

ppTermCtx :: [(String,Int)] -> Term Doc -> Doc
ppTermCtx _ (Var d) = d
ppTermCtx _ (Universe NoLevel) = text "Type"
ppTermCtx _ (Universe l) = text $ "Type" ++ show l
ppTermCtx ctx t@(App e1 e2) = ppTermPrec (prec t) ctx e1 <+> ppTermPrec (prec t + 1) ctx e2
ppTermCtx ctx t@(Arr e1 e2) = ppTermPrec (prec t + 1) ctx e1 <+> arrow <+> ppTermPrec (prec t) ctx e2
ppTermCtx ctx t@(Pi b e n) =
    let (as, t') = ppNamesPrec (prec t) ctx n
    in parens (hsep as <+> colon <+> ppTermCtx ctx e) <+> (if b then arrow else empty) <+> t'
ppTermCtx ctx t@(Lam n) =
    let (as, t') = ppNamesPrec (prec t) ctx n
    in text "\\" <> hsep as <+> arrow <+> t'
ppTermCtx ctx t@(Con _ n as _) = text n <+> hsep (map (ppTermPrec (prec t + 1) ctx) as)
ppTermCtx _ (FunSyn n _) = text n
ppTermCtx _ (FunCall n _) = text n
ppTermCtx ctx t@(DataType d as) = text d <+> hsep (map (ppTermPrec (prec t + 1) ctx) as)
ppTermCtx _ Interval = text "I"
ppTermCtx _ (ICon ILeft) = text "left"
ppTermCtx _ (ICon IRight) = text "right"
ppTermCtx ctx t@(Path es) = text "Path" <+> hsep (map (ppTermPrec (prec t + 1) ctx) es)
ppTermCtx ctx t@(PathImp _ e2 e3) = ppTermPrec (prec t + 1) ctx e2 <+> equals <+> ppTermPrec (prec t + 1) ctx e3
ppTermCtx ctx t@(PCon me) = text "path" <+> maybe empty (ppTermPrec (prec t + 1) ctx) me
ppTermCtx ctx t@(At _ _ e1 e2) = ppTermPrec (prec t) ctx e1 <+> text "@" <+> ppTermPrec (prec t + 1) ctx e2
ppTermCtx ctx t@(Coe es) = text "coe" <+> hsep (map (ppTermPrec (prec t + 1) ctx) es)
ppTermCtx ctx t@(Iso es) = text "iso" <+> hsep (map (ppTermPrec (prec t + 1) ctx) es)
ppTermCtx ctx t@(Squeeze es) = text "squeeze" <+> hsep (map (ppTermPrec (prec t + 1) ctx) es)

ppNamesPrec :: Int -> [(String,Int)] -> Names String Term Doc -> ([Doc], Doc)
ppNamesPrec p ctx n =
    let (as, ctx', t) = instantiateNames ctx (\d -> maybe (text d) $ \i -> text d <> int i) n
    in (as, ppTermPrec p ctx' t)

ppTermPrec :: Int -> [(String,Int)] -> Term Doc -> Doc
ppTermPrec p ctx t = if p > prec t then parens (ppTermCtx ctx t) else ppTermCtx ctx t

arrow :: Doc
arrow = text "->"

prec :: Term a      -> Int
prec Var{}           = 10
prec Universe{}      = 10
prec FunSyn{}        = 10
prec FunCall{}       = 10
prec (Con _ _ [] _)  = 10
prec (DataType _ []) = 10
prec (Path [])       = 10
prec (PCon Nothing)  = 10
prec Interval        = 10
prec ICon{}          = 10
prec (Coe [])        = 10
prec (Iso [])        = 10
prec (Squeeze [])    = 10
prec App{}           = 9
prec Con{}           = 9
prec DataType{}      = 9
prec Path{}          = 9
prec PCon{}          = 9
prec Coe{}           = 9
prec Iso{}           = 9
prec Squeeze{}       = 9
prec At{}            = 8
prec PathImp{}       = 7
prec Arr{}           = 6
prec Pi{}            = 6
prec Lam{}           = 5
