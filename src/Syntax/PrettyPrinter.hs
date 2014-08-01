module Syntax.PrettyPrinter
    ( ppTerm
    ) where

import Text.PrettyPrint
import Data.Bifoldable
import Data.Void

import Syntax
-- import qualified Syntax.ErrorDoc as E

{-
instance E.Pretty1 (Term p) where
    pretty1 t = ppTermCtx (freeVars t) t
-}

freeVars :: Term Syntax a -> [String]
freeVars = biconcatMap (\t -> case t of
    Con _ (PIdent _ s) _    -> [s]
    FunCall (PIdent _ s) _  -> [s]
    FunSyn s _              -> [s]
    DataType s _            -> [s]
    _                       -> []) (const [])

ppTerm :: Term Syntax Void -> Doc
ppTerm t = ppTermCtx (freeVars t) t

ppTermCtx :: [String] -> Term Syntax Void -> Doc
ppTermCtx ctx (Apply s ts) = ppSyntax ctx s ts
ppTermCtx _ _ = error "ppTermCtx"

ppSyntax :: [String] -> Syntax -> [Term Syntax Void] -> Doc
ppSyntax _ (Universe NoLevel) _ = text "Type"
ppSyntax _ (Universe l) _ = text $ "Type" ++ show l
ppSyntax ctx App [t1, t2] = ppTermPrec (prec App) ctx t1 <+> ppTermPrec (prec App + 1) ctx t2
ppSyntax ctx p@(Pi vs _ _) [t1, t2] = (if null vs
    then ppTermPrec (prec p + 1) ctx t1
    else parens $ hsep (map text vs) <+> colon <+> ppTermCtx ctx t1) <+> arrow <+> ppBound (prec p) ctx vs t2
ppSyntax ctx l@(Lam vs) [t] = text "\\" <> hsep (map text vs) <+> arrow <+> ppBound (prec l) ctx vs t
ppSyntax ctx t@(Con _ (PIdent _ n) _) ts = text n <+> ppList ctx t ts
ppSyntax ctx t@(FunSyn n _) ts = text n <+> ppList ctx t ts
ppSyntax ctx t@(FunCall (PIdent _ n) _) ts = text n <+> ppList ctx t ts
ppSyntax ctx t@(DataType d _) ts = text d <+> ppList ctx t ts
ppSyntax _ Interval _ = text "I"
ppSyntax _ (ICon ILeft) _ = text "left"
ppSyntax _ (ICon IRight) _ = text "right"
ppSyntax ctx t@(Path Implicit _) [_,t2,t3] = ppTermPrec (prec t + 1) ctx t2 <+> equals <+> ppTermPrec (prec t + 1) ctx t3
ppSyntax ctx t@(Path Explicit _) ts = text "Path" <+> ppList ctx t ts
ppSyntax ctx t@PCon ts = text "path" <+> ppList ctx t ts
ppSyntax ctx t@At [_,_,t3,t4] = ppTermPrec (prec t) ctx t3 <+> text "@" <+> ppTermPrec (prec t + 1) ctx t4
ppSyntax ctx t@Coe ts = text "coe" <+> ppList ctx t ts
ppSyntax ctx t@Iso ts = text "iso" <+> ppList ctx t ts
ppSyntax ctx t@Squeeze ts = text "squeeze" <+> ppList ctx t ts
ppSyntax ctx t@(Ident n) ts = text n <+> ppList ctx t ts
ppSyntax _ _ _ = error "ppSyntax"

ppList :: [String] -> Syntax -> [Term Syntax Void] -> Doc
ppList ctx t ts = hsep $ map (ppTermPrec (prec t + 1) ctx) ts

ppBound :: Int -> [String] -> [String] -> Term Syntax Void -> Doc
ppBound p ctx (v:vs') (Lambda (Scope1 t)) =
    let (ctx',v') = renameName2 v ctx (freeVars t)
    in ppBound p ctx' vs' $ instantiate1 (Apply (Ident v') []) t
ppBound p ctx _ t = ppTermPrec p ctx t

ppTermPrec :: Int -> [String] -> Term Syntax Void -> Doc
ppTermPrec p ctx t = if p > precTerm t then parens (ppTermCtx ctx t) else ppTermCtx ctx t

arrow :: Doc
arrow = text "->"

renameName :: String -> [String] -> ([String], String)
renameName var ctx = if var `Prelude.elem` ctx then renameName (var ++ "'") ctx else (var:ctx,var)

renameName2 :: String -> [String] -> [String] -> ([String], String)
renameName2 var ctx ctx' = if var `elem` ctx && var `elem` ctx'
    then renameName (var ++ "'") ctx'
    else (var:ctx,var)

prec :: Syntax         -> Int
prec Ident{}            = 10
prec Universe{}         = 10
prec FunSyn{}           = 10
prec FunCall{}          = 10
prec Con{}              = 10
prec DataType{}         = 10
prec (Path Explicit _)  = 10
prec PCon               = 10
prec Interval           = 10
prec ICon{}             = 10
prec Coe                = 10
prec Iso                = 10
prec Squeeze            = 10
prec App                = 9
prec At                 = 8
prec (Path Implicit _)  = 7
prec Pi{}               = 6
prec Lam{}              = 5

precTerm :: Term Syntax a -> Int
precTerm Var{} = 10
precTerm (Apply s _) = prec s
precTerm (Lambda (Scope1 t)) = precTerm t
