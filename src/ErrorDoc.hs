module ErrorDoc
    ( EMsg, EDoc, EDocM
    , Pretty(..), epretty
    , edoc, enull, (<>), (<+>), ($$)
    , etext, emsg, emsgL, emsgLC
    , erender, erenderWithFilename
    , liftErr2, forE
    ) where

import qualified Text.PrettyPrint as P

data EMsg f = EMsg (Maybe Int) (Maybe Int) String (EDoc f)
data EDoc f = EDoc P.Doc | ENull | ETerm (f (EDoc f)) | EAbove (EDoc f) (EDoc f) | EBeside (EDoc f) Bool (EDoc f)

type EDocM f = Either [EMsg f]

class Functor f => Pretty f where
    pretty :: f P.Doc -> P.Doc

liftErr2 :: (a -> b -> c) -> EDocM f a -> EDocM f b -> EDocM f c
liftErr2 f (Left m1) (Left m2) = Left (m1 ++ m2)
liftErr2 f (Left m) _ = Left m
liftErr2 f _ (Left m) = Left m
liftErr2 f (Right v1) (Right v2) = Right (f v1 v2)

forE :: [a] -> (a -> EDocM f b) -> EDocM f [b]
forE [] _ = Right []
forE (a:as) f = liftErr2 (:) (f a) (forE as f)

epretty :: f (EDoc f) -> EDoc f
epretty = ETerm

eprettyDoc :: Functor f => f P.Doc -> EDoc f
eprettyDoc = ETerm . fmap EDoc

eprettyStr :: Functor f => f String -> EDoc f
eprettyStr = ETerm . fmap etext

edoc :: P.Doc -> EDoc f
edoc = EDoc

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

etext :: String -> EDoc f
etext "" = enull
etext s = EDoc (P.text s)

emsg :: String -> EDoc f -> EMsg f
emsg = EMsg Nothing Nothing

emsgL :: Int -> String -> EDoc f -> EMsg f
emsgL l = EMsg (Just l) Nothing

emsgLC :: (Int,Int) -> String -> EDoc f -> EMsg f
emsgLC (l,c) = EMsg (Just l) (Just c)

erender :: Pretty f => EMsg f -> String
erender (EMsg l c s d) = P.render (msgToDoc Nothing l c s d)

erenderWithFilename :: Pretty f => String -> EMsg f -> String
erenderWithFilename fn (EMsg l c s d) = P.render (msgToDoc (Just fn) l c s d)

msgToDoc :: Pretty f => Maybe String -> Maybe Int -> Maybe Int -> String -> EDoc f -> P.Doc
msgToDoc fn l c s d = P.hang (
    maybe P.empty (\s -> P.text $ s ++ ":") fn P.<>
    maybe P.empty (\ln -> P.text $ show ln ++ ":") l P.<>
    maybe P.empty (\cn -> P.text $ show cn ++ ":") c P.<+> P.text s) 4 (edocToDoc d)

edocToDoc :: Pretty f => EDoc f -> P.Doc
edocToDoc ENull = P.empty
edocToDoc (EDoc d) = d
edocToDoc (EBeside d1 False d2) = edocToDoc d1 P.<> edocToDoc d2
edocToDoc (EBeside d1 True d2) = edocToDoc d1 P.<+> edocToDoc d2
edocToDoc (EAbove d1 d2) = edocToDoc d1 P.$+$ edocToDoc d2
edocToDoc (ETerm e) = pretty (fmap edocToDoc e)

instance Pretty f => Show (EDoc f) where
    show = P.render . edocToDoc
