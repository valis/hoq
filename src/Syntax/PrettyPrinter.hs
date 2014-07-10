module Syntax.PrettyPrinter
    ( ppTerm
    , scopeToTerm
    ) where

import Text.PrettyPrint
import Data.Foldable

import Syntax.Term
import qualified Syntax.ErrorDoc as E

instance E.Pretty1 Term where
    pretty1 t = ppTermCtx (toList $ fmap render t) t

ppTerm :: Term String -> Doc
ppTerm t = ppTermCtx (toList t) (fmap text t)

ppTermCtx :: [String] -> Term Doc -> Doc
ppTermCtx _ (Var d) = d
ppTermCtx _ (Universe NoLevel) = text "Type"
ppTermCtx _ (Universe l) = text $ "Type" ++ show l
ppTermCtx ctx t@(App e1 e2) = ppTermPrec (prec t) ctx e1 <+> ppTermPrec (prec t + 1) ctx e2
ppTermCtx ctx t@(Pi (Type a _) b _) =
    let (vs, b') = ppScopePrec (prec t) ctx b
    in (if null vs then ppTermPrec (prec t + 1) ctx a else parens $ hsep vs <+> colon <+> ppTermCtx ctx a) <+> b'
ppTermCtx ctx t@Lam{} = go ctx [] t
  where
    go ctx vars (Lam (Scope1 n s)) =
        let (ctx', n') = renameName n ctx
        in go ctx' (text n' : vars) $ instantiate1 (Var $ text n') s
    go ctx vars t' = text "\\" <> hsep (reverse vars) <+> arrow <+> ppTermPrec (prec t) ctx t'
ppTermCtx ctx t@(Con _ n _ as) = text n <+> ppList ctx t as
ppTermCtx _ (FunSyn n _) = text n
ppTermCtx _ (FunCall n _) = text n
ppTermCtx ctx t@(DataType d _ as) = text d <+> ppList ctx t as
ppTermCtx _ Interval = text "I"
ppTermCtx _ (ICon ILeft) = text "left"
ppTermCtx _ (ICon IRight) = text "right"
ppTermCtx ctx t@(Path Implicit _ [e2,e3]) = ppTermPrec (prec t + 1) ctx e2 <+> equals <+> ppTermPrec (prec t + 1) ctx e3
ppTermCtx ctx t@(Path _ me es) = text "Path" <+> ppList ctx t (maybe (Var $ text "_") id me : es)
ppTermCtx ctx t@(PCon me) = text "path" <+> maybe empty (ppTermPrec (prec t + 1) ctx) me
ppTermCtx ctx t@(At _ _ e1 e2) = ppTermPrec (prec t) ctx e1 <+> text "@" <+> ppTermPrec (prec t + 1) ctx e2
ppTermCtx ctx t@(Coe es) = text "coe" <+> ppList ctx t es
ppTermCtx ctx t@(Iso es) = text "iso" <+> ppList ctx t es
ppTermCtx ctx t@(Squeeze es) = text "squeeze" <+> ppList ctx t es

ppList :: [String] -> Term Doc -> [Term Doc] -> Doc
ppList ctx t ts = hsep $ map (ppTermPrec (prec t + 1) ctx) ts

ppScopePrec :: Int -> [String] -> Scope String Term Doc -> ([Doc], Doc)
ppScopePrec p ctx t =
    let (vars, b, ctx', t') = scopeToTerm ctx text t
    in (map text vars, (if b then arrow else empty) <+> ppTermPrec p ctx' t')

scopeToTerm :: [String] -> (String -> a) -> Scope String Term a -> ([String], Bool, [String], Term a)
scopeToTerm ctx f (ScopeTerm t@(Pi _ ScopeTerm{} _)) = ([], False, ctx, t)
scopeToTerm ctx f (ScopeTerm t) = ([], True, ctx, t)
scopeToTerm ctx f (Scope v s) =
    let (ctx', v') = renameName v ctx
        (vs, b, ctx'', d) = scopeToTerm ctx' f $ instantiateScope (Var $ f v') s
    in  (v' : vs, b, ctx'', d)

ppTermPrec :: Int -> [String] -> Term Doc -> Doc
ppTermPrec p ctx t = if p > prec t then parens (ppTermCtx ctx t) else ppTermCtx ctx t

arrow :: Doc
arrow = text "->"

renameName :: String -> [String] -> ([String], String)
renameName var ctx = if var `Prelude.elem` ctx then renameName (var ++ "'") ctx else (var:ctx,var)

prec :: Term a                 -> Int
prec Var{}                      = 10
prec Universe{}                 = 10
prec FunSyn{}                   = 10
prec FunCall{}                  = 10
prec (Con _ _ _ [])             = 10
prec (DataType _ _ [])          = 10
prec (Path Explicit Nothing []) = 10
prec (PCon Nothing)             = 10
prec Interval                   = 10
prec ICon{}                     = 10
prec (Coe [])                   = 10
prec (Iso [])                   = 10
prec (Squeeze [])               = 10
prec App{}                      = 9
prec Con{}                      = 9
prec DataType{}                 = 9
prec (Path Explicit _ _)        = 9
prec PCon{}                     = 9
prec Coe{}                      = 9
prec Iso{}                      = 9
prec Squeeze{}                  = 9
prec At{}                       = 8
prec (Path Implicit _ _)        = 7
prec Pi{}                       = 6
prec Lam{}                      = 5
