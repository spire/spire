{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, RankNTypes #-}
module Spire.Surface.PrettyPrinting (prettyPrint) where
import Spire.Surface.Types
import Spire.Surface.Parsing
import Spire.Canonical.Types
import Spire.Expression.Types

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader
import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (Doc)

----------------------------------------------------------------------

prettyPrint :: Display t => t -> String
prettyPrint t = PP.render $ runReader (display t) initialDisplayData

-- Short hands.
d :: Display t => t -> DisplayMonad Doc
d = display

-- Lift standard pretty printing ops to a monad.
sepM , fsepM , hsepM , vcatM :: (Functor m , Monad m) => [m Doc] -> m Doc
sepM  xs = PP.sep  <$> sequence xs
fsepM xs = PP.fsep <$> sequence xs
hsepM xs = PP.hsep <$> sequence xs
vcatM xs = PP.vcat <$> sequence xs
parensM :: Functor m => m Doc -> m Doc
parensM = fmap PP.parens
infixl 6 <+>
(<+>) :: (Monad m) => m Doc -> m Doc -> m Doc
(<+>) = liftM2 (PP.<+>)


-- Would be better to keep around the original names from the
-- 'NomBound's and reuse them here ...
var :: Bound t -> DisplayMonad Doc
var (Bound (id , _)) = do
  k <- asks numEnclosingBinders
  d $ id ++ show k

binding :: (Precedence t', Precedence t, Display t) => t' -> Ident -> t -> DisplayMonad Doc
binding outside id tp | id == wildcard  = wrapNonAssoc outside tp
binding outside id tp = parensM . hsepM $ [d id , d ":" , d tp]

----------------------------------------------------------------------

instance Display Syntax where
  display s = case s of
    STT -> d "tt"
    STrue -> d "true"
    SFalse -> d "false"
    SPair x y -> sepM [w x , d "," , d y]
    SLam (Bound (id , body)) -> fsepM [d "\\" <+> d id <+> d "->" , d body]
    SUnit -> d "Unit"
    SBool -> d "Bool"
    SString -> d "String"
    SDesc -> d "Desc"
    SType -> d "Type"

    SDUnit -> d "Done"
    SDRec -> d "Rec"
    SDSum x y -> sepM [w x , d "|" , d y]
    SDPi x y -> sepM [w x , d "=>" , d y]
    SDSg x y -> sepM [w x , d "#" , d y]

    SPi tp1 (Bound (id, tp2)) ->
      sepM [binding s id tp1 <+> d "->" , d tp2]
    SSg tp1 (Bound (id, tp2)) ->
      sepM [binding s id tp1 <+> d "*", d tp2]
    SVar id -> d id
    SQuotes str -> d . show $ str
    SStrAppend s1 s2 -> sepM [w s1 , d "++" , d s2]
    SStrEq s1 s2 -> sepM [d s1 , d "==" , d s2]
    SIf c t f -> sepM [d "if" <+> d c , d "then" <+> d t , d "else" <+> d f]
    SCaseBool (Bound (id, m)) t f b ->
      d "caseBool" <+> sepM
           [ parensM $ d "\\" <+> d id <+> d "->" <+> d m
           , w t , w f , w b]
    SProj1 xy -> d "proj1" <+> w xy
    SProj2 xy -> d "proj2" <+> w xy
    SApp f x -> sepM [d f , w x] -- ???: how to format chained application?
    SAnn x tp -> parensM $ d x <+> d ":" <+> d tp
    where
      d , w :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' s
      w = wrapNonAssoc s

----------------------------------------------------------------------

instance Display Check where
  display c = case c of
    CPair x y -> sepM [w x , d "," , d y]
    CLam (Bound (id , body)) -> sepM [d "\\" , d id , d "->" , d body]
    Infer i -> d i
    where
      d , w :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' c
      w = wrapNonAssoc c

instance Display Infer where
  display i = case i of
    ITT -> d "tt"
    ITrue -> d "true"
    IFalse -> d "false"
    ILamAnn tp (Bound (id , body)) ->
      sepM [d "\\" , d id , d "->" , d body , d ":" , d tp]
    IUnit -> d "Unit"
    IBool -> d "Bool"
    IString -> d "String"
    IDesc -> d "Desc"
    IProg -> d "Prog" -- NC: ??? Don't see this parsed anywhere.
    IType -> d "Type"

    IDUnit -> d "Done"
    IDRec -> d "Rec"
    IDSum x y -> sepM [w x , d "|" , d y]
    IDPi x y -> sepM [w x , d "=>" , d y]
    IDSg x y -> sepM [w x , d "#" , d y]

    IPi tp1 (Bound (id, tp2)) ->
      sepM [binding i id tp1 , d "->" , d tp2]
    ISg tp1 (Bound (id, tp2)) ->
      sepM [binding i id tp1 , d "*", d tp2]
    IDefs defs -> vcatM . map d $ defs

    IVar id -> d id
    IQuotes str -> d . show $ str
    IStrAppend s1 s2 -> sepM [w s1 , d "++" , d s2]
    IStrEq s1 s2 -> sepM [d s1 , d "==" , d s2]
    IIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    ICaseBool (Bound (id, m)) t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [d "\\" , d id , d "->" , d m]
           , w t , w f , w b ]
    IProj1 xy -> sepM [d "proj1" , w xy]
    IProj2 xy -> sepM [d "proj2" , w xy]
    IApp f x -> sepM [d f , w x]
    IAnn x tp -> parensM . sepM $ [d x , d ":" , d tp]
    where
      d , w :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' i
      w = wrapNonAssoc i

----------------------------------------------------------------------

instance Display Val where
  display v = case v of
    VUnit -> d "Unit"
    VBool -> d "Bool"
    VString -> d "String"
    VDesc -> d "Desc"
    VProg -> d "Prog"
    VType -> d "Type"
    VPi tp1 tp2 ->
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "->" , d tp2]
    VSg tp1 tp2 ->
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "*", d tp2]
    VTT -> d "tt"
    VTrue -> d "True"
    VFalse -> d "False"

    VDUnit -> d "Done"
    VDRec -> d "Rec"
    VDSum x y -> sepM [w x , d "|" , d y]
    VDPi x y ->
      sepM [parensM . sepM $ [var y , d ":" , d x] , d "=>", d y]
    VDSg x y ->
      sepM [parensM . sepM $ [var y , d ":" , d x] , d "#", d y]

    VQuotes str -> d . show $ str
    -- ???: what's the right way to display type-annotated pairs?
    VPair tx ty x y -> sepM [ parensM . sepM $ [d x , d "," , d y]
                            , d ":" , d (VSg tx ty) ]
    VLam tp body ->
      sepM [d "\\" , var body , d ":" , d tp , d "->" , d body]
    VDefs defs -> vcatM . map d $ defs
    Neut n -> d n
    where
      d , w :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' v
      w = wrapNonAssoc v

instance Display Neut where
  display n = case n of
    NVar (NomVar (id , v)) -> do
      k <- asks numEnclosingBinders
      -- XXX: the 'id' here should already be determined by the
      -- binding site of this var.  So, we could perform a sanity
      -- check here, if the list of binders were in the state.
      d $ id ++ show (k - v)
    NStrAppendL s1 s2 -> sepM [w s1 , d "++" , d s2]
    NStrAppendR s1 s2 -> sepM [w s1 , d "++" , d s2]
    NStrEqL s1 s2 -> sepM [d s1 , d "==" , d s2]
    NStrEqR s1 s2 -> sepM [d s1 , d "==" , d s2]
    NIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    NCaseBool m t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [d "\\" , var m , d "->" , d m]
           , w t , w f , w b ]
    NProj1 xy -> sepM [d "proj1" , w xy]
    NProj2 xy -> sepM [d "proj2" , w xy]
    NApp f x -> sepM [d f , w x]
    where
      d , w :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' n
      w = wrapNonAssoc n

----------------------------------------------------------------------

instance Precedence Syntax where
  level s = case s of
    SPair x y                       -> pairLevel
    SLam (Bound (id , body))        -> lamLevel
    SPi tp1 (Bound (id, tp2))       -> piLevel
    SSg tp1 (Bound (id, tp2))       -> sgLevel
    SStrAppend s1 s2                -> strAppendLevel
    SStrEq s1 s2                    -> strEqLevel
    SIf c t f                       -> ifLevel
    SCaseBool (Bound (id, m)) t f b -> caseBoolLevel
    SProj1 xy                       -> projLevel
    SProj2 xy                       -> projLevel
    SApp f x                        -> appLevel
    SAnn x tp                       -> annLevel
    SDSum x y                       -> dSumLevel
    SDPi x y                        -> dPiLevel
    SDSg x y                        -> dSgLevel
    _                               -> atomicLevel
  assoc s = case s of
    SPi tp1 (Bound (id, tp2))       -> piAssoc
    SSg tp1 (Bound (id, tp2))       -> sgAssoc
    SStrAppend s1 s2                -> strAppendAssoc
    SApp f x                        -> appAssoc
    SDSum x y                       -> dSumAssoc
    SDPi x y                        -> piAssoc
    SDSg x y                        -> sgAssoc
    _                               -> AssocNone

----------------------------------------------------------------------

instance Precedence Check where
  level c = case c of
    CPair x y                -> pairLevel
    CLam (Bound (id , body)) -> lamLevel
    Infer i                  -> level i
  assoc c = case c of
    CPair x y                -> pairAssoc
    Infer i                  -> assoc i
    _                        -> AssocNone

instance Precedence Infer where
  level i = case i of
    ILamAnn tp (Bound (id , body))  -> lamLevel
    IPi tp1 (Bound (id, tp2))       -> piLevel
    ISg tp1 (Bound (id, tp2))       -> sgLevel
    IDefs defs                      -> defsLevel
    IStrAppend s1 s2                -> strAppendLevel
    IStrEq s1 s2                    -> strEqLevel
    IIf c t f                       -> ifLevel
    ICaseBool (Bound (id, m)) t f b -> caseBoolLevel
    IProj1 xy                       -> projLevel
    IProj2 xy                       -> projLevel
    IApp f x                        -> appLevel
    IAnn x tp                       -> annLevel
    IDSum x y                       -> dSumLevel
    IDPi x y                        -> dPiLevel
    IDSg x y                        -> dSgLevel
    _                               -> atomicLevel
  assoc i = case i of
    IPi tp1 (Bound (id, tp2))       -> piAssoc
    ISg tp1 (Bound (id, tp2))       -> sgAssoc
    IStrAppend s1 s2                -> strAppendAssoc
    IApp f x                        -> appAssoc
    IDSum x y                       -> dSumAssoc
    IDPi x y                        -> piAssoc
    IDSg x y                        -> sgAssoc
    _                               -> AssocNone

----------------------------------------------------------------------

instance Precedence Val where
  level v = case v of
    VPi tp1 tp2     -> piLevel
    VSg tp1 tp2     -> sgLevel
    VPair tx ty x y -> pairLevel
    VLam tp body    -> lamLevel
    VDefs defs      -> defsLevel
    Neut n          -> level n
    VDSum x y       -> dSumLevel
    VDPi x y        -> dPiLevel
    VDSg x y        -> dSgLevel
    _               -> atomicLevel
  assoc v = case v of
    VPi tp1 tp2     -> piAssoc
    VSg tp1 tp2     -> sgAssoc
    VPair tx ty x y -> pairAssoc
    Neut n          -> assoc n
    VDSum x y       -> dSumAssoc
    VDPi x y        -> piAssoc
    VDSg x y        -> sgAssoc
    _               -> AssocNone

instance Precedence Neut where
  level n = case n of
    NStrAppendL s1 s2 -> strAppendLevel
    NStrAppendR s1 s2 -> strAppendLevel
    NStrEqL s1 s2     -> strEqLevel
    NStrEqR s1 s2     -> strEqLevel
    NIf c t f         -> ifLevel
    NCaseBool m t f b -> caseBoolLevel
    NProj1 xy         -> projLevel
    NProj2 xy         -> projLevel
    NApp f x          -> appLevel
    _                 -> atomicLevel
  assoc n = case n of
    NStrAppendL s1 s2 -> strAppendAssoc
    NStrAppendR s1 s2 -> strAppendAssoc
    NApp f x          -> appAssoc
    _                 -> AssocNone

----------------------------------------------------------------------

instance Display String where
  display = return . PP.text

instance Precedence String where
  level _ = atomicLevel
  assoc _ = AssocNone

instance Precedence Def where
  level _ = defLevel
  assoc _ = AssocNone

instance Precedence VDef where
  level _ = defLevel
  assoc _ = AssocNone

instance Display Def where
  display (id , tm , tp) =
    vcatM [sepM [d id , d ":" , d tp] , sepM [d id , d "=" , d tm]]

instance Display t => Display (Bound t) where
  display (Bound (_ , x)) = local incNumEnclosingBinders $ display x

instance Display VDef where
  display (v , tp) = sepM [d v , d ":" , d tp]

instance Precedence t => Precedence (Bound t) where
  level (Bound (_ , x)) = level x
  assoc (Bound (_ , x)) = assoc x

----------------------------------------------------------------------

incNumEnclosingBinders :: DisplayData -> DisplayData
-- XXX: could store list of 'Bound's, instead of the length of this
-- list, which would allow us to only uniquify (by appending a number)
-- when necessary.
incNumEnclosingBinders d@(DisplayData { numEnclosingBinders = k }) =
  d { numEnclosingBinders = k + 1 }

----------------------------------------------------------------------

-- The 'Reader' data of the 'DisplayMonad'.  E.g., the "flags" Tim
-- mentioned would go in here.
data DisplayData =
  DisplayData { numEnclosingBinders :: Int }
initialDisplayData :: DisplayData
initialDisplayData = DisplayData { numEnclosingBinders = 0 }

type DisplayMonad t = Reader DisplayData t

-- Convert 't' to 'Doc', using 'DisplayData'.
class Display t where
  display :: t -> DisplayMonad Doc

-- Same as 'Text.Parsec.Expr.Assoc', except with 'Eq' :P
data Assoc = AssocLeft | AssocRight | AssocNone deriving Eq

-- The precedence level is the tightness of binding: larger levels
-- mean tighter binding.
class Precedence t where
  level :: t -> Float
  assoc :: t -> Assoc

-- Precedence levels and infix op associativities.
--
-- Compare with table in used in Spire.Surface.Parsing.
atomicLevel    = -1
appLevel       = 0
appAssoc       = AssocLeft
projLevel      = 0
strAppendLevel = 1
strAppendAssoc = AssocRight
strEqLevel     = 2
pairLevel      = 3
pairAssoc      = AssocRight
sgLevel        = 4
sgAssoc        = AssocRight
piLevel        = 5
piAssoc        = AssocRight
dPiLevel       = 5 + 1/3
dSgLevel       = 5 + 1/3
dSumLevel      = 5 + 2/3
dSumAssoc      = AssocRight
ifLevel        = 6
caseBoolLevel  = 6
lamLevel       = 7
annLevel       = 8
defsLevel      = 9
defLevel       = 10

-- For non-infix operators, use 'wrap'' to wrap optionally recursive
-- displays as needed.
--
-- For infix operators, use 'wrap'' to optionally wrap recursive
-- displays in positions consistent with association, and use
-- 'wrapNonAssoc' to optionally wrap recursive displays in positions
-- inconsistent with association.
--
-- For example, for a left associative application 'App', the
-- 'display' case could be written:
--
--   display s@(App f x) =
--     sepM [ wrap' s f (display f) , wrapNonAssoc s x (display x) ]
wrap' , wrapNonAssoc :: (Display t2, Precedence t1 , Precedence t2) =>
                            t1 -> t2 -> DisplayMonad Doc
wrap' outside inside =
  if level outside  < level inside ||
     level outside == level inside && assoc outside /= assoc inside
  then parensM . display $ inside
  else display inside

wrapNonAssoc outside inside =
  if level outside <= level inside
  then parensM . display $ inside
  else display inside

----------------------------------------------------------------------