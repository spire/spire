{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, RankNTypes #-}
module Spire.Surface.PrettyPrinting (prettyPrint , prettyPrintError) where
import Spire.Canonical.Embedding
import Spire.Canonical.Types
import Spire.Expression.Embedding
import Spire.Expression.Types
import Spire.Surface.Types

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader
import qualified Text.PrettyPrint.Leijen as WL
import Text.PrettyPrint.Leijen (Doc)

----------------------------------------------------------------------

prettyPrint :: Display t => t -> String
prettyPrint t = render $ runReader (display t) initialDisplayData
  where
  render = show
  {-
  -- To adjust the printing parameters:
  render x = WL.displayS (WL.renderPretty ribbon columns x) ""
  columns = 80
  ribbon = 0.3
  -}

prettyPrintError :: (Show t , Display t) => t -> String
prettyPrintError a  = prettyPrint a ++ "\t(" ++ show a ++ ")"

----------------------------------------------------------------------

-- Lift standard pretty printing ops to a monad.
sepM , fsepM , hsepM , vcatM , listM :: (Functor m , Monad m) =>
                                        [m Doc] -> m Doc
sepM  xs = WL.sep <$> sequence xs
fsepM xs = WL.fillSep <$> sequence xs
hsepM xs = WL.hsep <$> sequence xs
vcatM xs = WL.vcat <$> sequence xs
listM xs = WL.list <$> sequence xs

nestM , indentM :: Functor m => Int -> m Doc -> m Doc
nestM n = fmap $ WL.nest n
indentM n = fmap $ WL.indent n

parensM , groupM , alignM :: Functor m => m Doc -> m Doc
parensM = fmap WL.parens
groupM = fmap WL.group
alignM = fmap WL.align

infixr 5 </> , <$$> , <$+$>
infixr 6 <> , <+>
(<>) , (<+>) , (</>) , (<$$>) , (<$+$>) ::
  Monad m => m Doc -> m Doc -> m Doc
(<>) = liftM2 (WL.<>)
(<+>) = liftM2 (WL.<+>)
(</>) = liftM2 (WL.</>)
(<$$>) = liftM2 (WL.<$$>)
(<$+$>) = liftM2 (WL.<$>)

----------------------------------------------------------------------

binding :: (Precedence t', Precedence t, Display t) =>
           t' -> Ident -> t -> DisplayMonad Doc
binding outside id tp | id == wildcard  = wrapNonAssoc outside tp
binding outside id tp = parensM . hsepM $ [d id , d ":" , d tp]

----------------------------------------------------------------------
-- Short hands.

d :: Display t => t -> DisplayMonad Doc
d = display
w , ww :: (Precedence o , Precedence i, Display i) =>
          o -> i -> DisplayMonad Doc
w = wrap'         -- Mnemonic: (w)rapped display
ww = wrapNonAssoc -- Mnemonic: (w)rapped (w)rapped display
                  -- (i.e. more wrapped :P)

----------------------------------------------------------------------
-- Syntactic-category agnostic printers.
--
-- The idea was to write all the pretty printers using these
-- ... except now all but one printer is defined by embedding.

-- Constructors with no arguments have printers with no arguments.
dTT = d "tt"
dTrue = d "true"
dFalse = d "false"
dUnit = d "Unit"
dBool = d "Bool"
dString = d "String"
dDesc = d "Desc"
dType = d "Type"
dDUnit = d "Done"
dDRec = d "Rec"

-- Constructors with arguments pass *themselves* and their args to
-- their printers.
dDSum o x y = alignM $ ww o x <+> d "|" </> w o y
dDPi o x y = fsepM [ ww o x <+> d "=>" , w o y ]
dDSg o x y = ww o x <+> d "#" <+> w o y
dPair o x y = ww o x <+> d "," <+> w o y
dLam o (Bound (id , body)) =
  fsepM [ d "\\" <+> w o id <+> d "->" , w o body ]
dPi o tp1 (Bound (id, tp2)) =
  fsepM [ binding o id tp1 <+> d "->" , w o tp2 ]
dSg o tp1 (Bound (id, tp2)) =
  binding o id tp1 <+> d "*" <+> d tp2
dQuotes o str = d . show $ str
dStrAppend o s1 s2 = alignM $ ww o s1 <+> d "++" </> w o s2
dStrEq o s1 s2 = w o s1 <+> d "==" <+> w o s2
dIf o c t f = alignM . sepM $ [ d "if" <+> w o c
                              , d "then" <+> w o t
                              , d "else" <+> w o f ]
dCaseBool o bnd t f bool =
  d "caseBool" <+> (alignM . sepM)
      [ parensM $ dLam o bnd
      , ww o t , ww o f , ww o bool ]
dProj1 o xy = d "proj1" <+> ww o xy
dProj2 o xy = d "proj2" <+> ww o xy
dFix o x = d "Fix" <+> ww o x
dIn o x = d "<" <+> d x <+> d ">"
dApp o f x = alignM $ w o f </> ww o x
dAnn o x tp = parensM . alignM . sepM $ [ d x , d ":" <+> d tp ]

----------------------------------------------------------------------

instance Display Syntax where
  display s = case s of
    STT -> dTT
    STrue -> dTrue
    SFalse -> dFalse
    SPair x y -> dPair s x y
    SLam b -> dLam s b
    SUnit -> dUnit
    SBool -> dBool
    SString -> dString
    SDesc -> dDesc
    SType -> dType

    SDUnit -> dDUnit
    SDRec -> dDRec
    SDSum x y -> dDSum s x y
    SDPi x y -> dDPi s x y
    SDSg x y -> dDSg s x y

    SPi tp1 b -> dPi s tp1 b
    SSg tp1 b -> dSg s tp1 b
    SVar id -> d id
    SQuotes str -> dQuotes s str
    SStrAppend s1 s2 -> dStrAppend s s1 s2
    SStrEq s1 s2 -> dStrEq s s1 s2
    SIf c t f -> dIf s c t f
    SCaseBool bnd t f bool -> dCaseBool s bnd t f bool
    SProj1 xy -> dProj1 s xy
    SProj2 xy -> dProj2 s xy
    SFix x -> dFix s x
    SIn x -> dIn s x
    SApp f x -> dApp s f x
    SAnn x tp -> dAnn s x tp

instance Display Statement where
  display (SDef f e t) =
    (groupM . nestM 2) (d f <+> d ":" <$+$> d t) <$$>
    (groupM . nestM 2) (d f <+> d "=" <$+$> d e)

instance Display Statements where
  display defs =  WL.vcat . WL.punctuate WL.line <$> mapM d defs

----------------------------------------------------------------------

instance Display Defs where
  display = d . map embedD

instance Display Check where
  display = d . embedC

instance Display Infer where
  display = d . embedI

instance Display Ctx where
  display ctx = listM [ parensM $ d x <+> d "," <+> d t
                      | (x , t) <- ctx ]

----------------------------------------------------------------------

instance Display Val where
  display v = case embedV v of
    Left error -> d (show v) <+> parensM (d error)
    Right i    -> d . embedI $ i

instance Display Neut where
  display n = case embedN n of
    Left error -> d (show n) <+> parensM (d error)
    Right i    -> d . embedI $ i

----------------------------------------------------------------------

instance Precedence Syntax where
  level s = case s of
    SPair x y                       -> pairLevel
    SLam (Bound (id , body))        -> lamLevel
    SPi tp1 (Bound (id, tp2))       -> piLevel
    SSg tp1 (Bound (id, tp2))       -> sgLevel
    SFix d                          -> fixLevel
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
    SIn x                           -> inLevel
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

instance Display String where
  display = return . WL.string

instance Precedence String where
  level _ = atomicLevel
  assoc _ = AssocNone

instance Display t => Display (Bound t) where
  display (Bound (_ , x)) = d x

instance Precedence t => Precedence (Bound t) where
  level (Bound (_ , x)) = level x
  assoc (Bound (_ , x)) = assoc x

----------------------------------------------------------------------

-- The 'Reader' data of the 'DisplayMonad'.  E.g., the "flags" Tim
-- mentioned would go in here.
data DisplayData = DisplayData {}
initialDisplayData :: DisplayData
initialDisplayData = DisplayData {}

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
annLevel       = atomicLevel
appLevel       = 0
appAssoc       = AssocLeft
projLevel      = 0
fixLevel       = 0
inLevel        = 0
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