{-# LANGUAGE FlexibleInstances #-}

module Syntax.PrettyPrinter
    ( ppTerm
    ) where

import Text.PrettyPrint
import Data.Bifunctor
import Data.Bifoldable
import Data.Void

import Syntax
import qualified Syntax.ErrorDoc as E

instance E.Pretty1 (Term Syntax) where
    pretty1 t = ppTermCtx (freeVars t) t

freeVars :: Term Syntax a -> [String]
freeVars = biconcatMap (\t -> case t of
    Name _ (Ident s)    -> [s]
    _                   -> []) (const [])

ppTerm :: Term Syntax Void -> Doc
ppTerm t = ppTermCtx (freeVars t) (vacuous t)

ppTermCtx :: [String] -> Term Syntax Doc -> Doc
ppTermCtx ctx (Var d ts) = d <+> ppList ctx ts
ppTermCtx ctx (Apply s ts) = ppSyntax ctx s ts
ppTermCtx ctx (Lambda t) = ppTermCtx ctx $ fmap (\v -> case v of
    Bound -> text "(error: Bound)"
    Free d -> d) t

ppSyntax :: [String] -> Syntax -> [Term Syntax Doc] -> Doc
ppSyntax ctx p@(Pi e vs) (t1:t2:ts) =
    let r = (if null vs then ppTermPrec (prec p + 1) ctx t1
            else (if e == Explicit then parens else braces) $ hsep (map text vs) <+> colon <+> ppTermCtx ctx t1)
            <+> arrow <+> ppBound (prec p) ctx vs t2
    in if null ts then r else parens r <+> ppList ctx ts
ppSyntax ctx l@(Lam vs) (t:ts) = bparens (not $ null ts) (text "\\" <> hsep (map text vs) <+> arrow <+> ppBound (prec l) ctx vs t) <+> ppList ctx ts
ppSyntax ctx t@PathImp [_,t2,t3] = ppTermPrec (prec t + 1) ctx t2 <+> equals <+> ppTermPrec (prec t + 1) ctx t3
ppSyntax ctx t@At (_:_:t3:t4:ts) = bparens (not $ null ts)
    (ppTermPrec (prec t) ctx t3 <+> text "@" <+> ppTermPrec (prec t + 1) ctx t4) <+> ppList ctx ts
ppSyntax ctx t@(Name (Infix ft _) n) (t1:t2:ts) =
    bparens (not $ null ts) (ppTermPrec (opFixity InfixL ft $ prec t) ctx t1 <+> text (nameToInfix n)
        <+> ppTermPrec (opFixity InfixR ft $ prec t) ctx t2) <+> ppList ctx ts
ppSyntax ctx (Name _ n) ts = text (nameToPrefix n) <+> ppList ctx ts
ppSyntax ctx (Case pats) (expr:terms) = hang (text "case" <+> ppTermCtx ctx expr <+> text "of") 4 $ vcat $
    map (\(pat,term) -> ppTermCtx ctx (bimap (Name Prefix . snd) text pat) <+> arrow <+>
        ppBound 0 ctx (bifoldMap (const []) return pat) term) (zip pats terms)
ppSyntax ctx Null [t] = ppTermCtx ctx t
ppSyntax _ Null _ = empty
ppSyntax _ Lam{} [] = error "ppSyntax: Lam"
ppSyntax _ Pi{} _ = error "ppSyntax: Pi"
ppSyntax _ PathImp{} _ = error "ppSyntax: PathImp"
ppSyntax _ At _ = error "ppSyntax: At"
ppSyntax _ Case{} [] = error "ppSyntax: Case"

opFixity :: Infix -> Infix -> Int -> Int
opFixity ft ft' p = if ft == ft' then p else p + 1

ppList :: [String] -> [Term Syntax Doc] -> Doc
ppList ctx ts = hsep $ map (ppTermPrec 100 ctx) ts

ppBound :: Int -> [String] -> [String] -> Term Syntax Doc -> Doc
ppBound p ctx (v:vs) (Lambda t) =
    let (ctx',v') = renameName2 v ctx (freeVars t)
    in ppBound p ctx' vs $ instantiate1 (capply $ Name Prefix $ Ident v') t
ppBound p ctx _ t = ppTermPrec p ctx t

ppTermPrec :: Int -> [String] -> Term Syntax Doc -> Doc
ppTermPrec p ctx t = bparens (p > precTerm t) (ppTermCtx ctx t)

bparens :: Bool -> Doc -> Doc
bparens True d = parens d
bparens False d = d

arrow :: Doc
arrow = text "->"

renameName :: String -> [String] -> ([String], String)
renameName var ctx = if var `Prelude.elem` ctx then renameName (var ++ "'") ctx else (var:ctx,var)

renameName2 :: String -> [String] -> [String] -> ([String], String)
renameName2 var ctx ctx' = if var `elem` ctx && var `elem` ctx'
    then renameName (var ++ "'") ctx'
    else (var:ctx,var)

prec :: Syntax             -> Int
prec (Name Prefix _)        = 100
prec (Name (Infix _ p) _)   = p
prec At                     = 80
prec PathImp{}              = 70
prec Pi{}                   = 60
prec Lam{}                  = 50
prec _                      = 0

precTerm :: Term Syntax a -> Int
precTerm Var{} = 100
precTerm (Apply Name{} (_:_)) = 90
precTerm (Apply s _) = prec s
precTerm (Lambda t) = precTerm t
