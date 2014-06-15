{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Syntax.ErrorDoc
    ( EMsg, EDoc
    , Pretty(..), Pretty1(..), epretty
    , enull, (<>), (<+>), ($$)
    , emsg, emsgL, emsgLC
    , erender, erenderWithFilename
    ) where

import qualified Text.PrettyPrint as P

data EMsg f = EMsg (Maybe Int) (Maybe Int) String (EDoc f)
data EDoc f = EDoc P.Doc | ENull | ETerm (f (EDoc f)) | EAbove (EDoc f) (EDoc f) | EBeside (EDoc f) Bool (EDoc f)

class Functor f => Pretty1 f where
    pretty1 :: f P.Doc -> P.Doc

instance Pretty1 f => Show (EDoc f) where
    show = P.render . edocToDoc

class Pretty a f where
    pretty :: a -> EDoc f

instance Pretty P.Doc f where
    pretty = EDoc

instance Pretty String f where
    pretty = etext

instance (Pretty a f, Pretty b f) => Pretty (Either a b) f where
    pretty (Left a)  = pretty a
    pretty (Right b) = pretty b

etext :: String -> EDoc f
etext "" = enull
etext s = EDoc (P.text s)

epretty :: f (EDoc f) -> EDoc f
epretty = ETerm

eprettyDoc :: Functor f => f P.Doc -> EDoc f
eprettyDoc = ETerm . fmap EDoc

eprettyStr :: Functor f => f String -> EDoc f
eprettyStr = ETerm . fmap etext

enull :: EDoc f
enull = ENull

infixl 6 <>, <+>
infixl 5 $$
(<>) :: EDoc f -> EDoc f -> EDoc f
d1 <> d2 = EBeside d1 False d2

(<+>) :: EDoc f -> EDoc f -> EDoc f
d1 <+> d2 = EBeside d1 True d2

($$) :: EDoc f -> EDoc f -> EDoc f
($$) = EAbove

emsg :: String -> EDoc f -> EMsg f
emsg = EMsg Nothing Nothing

emsgL :: Int -> String -> EDoc f -> EMsg f
emsgL l = EMsg (Just l) Nothing

emsgLC :: (Int,Int) -> String -> EDoc f -> EMsg f
emsgLC (l,c) = EMsg (Just l) (Just c)

erender :: Pretty1 f => EMsg f -> String
erender (EMsg l c s d) = P.render (msgToDoc Nothing l c s d)

erenderWithFilename :: Pretty1 f => String -> EMsg f -> String
erenderWithFilename fn (EMsg l c s d) = P.render (msgToDoc (Just fn) l c s d)

msgToDoc :: Pretty1 f => Maybe String -> Maybe Int -> Maybe Int -> String -> EDoc f -> P.Doc
msgToDoc Nothing l c "" d =
    maybe P.empty (\ln -> P.text $ show ln ++ ":") l P.<>
    maybe P.empty (\cn -> P.text $ show cn ++ ":") c P.<+>
    edocToDoc d
msgToDoc fn l c s d = P.hang (
    maybe P.empty (\s -> P.text $ s ++ ":") fn P.<>
    maybe P.empty (\ln -> P.text $ show ln ++ ":") l P.<>
    maybe P.empty (\cn -> P.text $ show cn ++ ":") c P.<+> P.text s) 4 (edocToDoc d)

edocToDoc :: Pretty1 f => EDoc f -> P.Doc
edocToDoc ENull = P.empty
edocToDoc (EDoc d) = d
edocToDoc (EBeside d1 False d2) = edocToDoc d1 P.<> edocToDoc d2
edocToDoc (EBeside d1 True d2) = edocToDoc d1 P.<+> edocToDoc d2
edocToDoc (EAbove d1 d2) = edocToDoc d1 P.$+$ edocToDoc d2
edocToDoc (ETerm e) = pretty1 (fmap edocToDoc e)
