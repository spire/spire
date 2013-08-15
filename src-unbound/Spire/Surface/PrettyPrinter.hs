{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, RankNTypes #-}
module Spire.Surface.PrettyPrinter (prettyPrint , prettyPrintError) where
-- import Spire.Canonical.Embedding
-- import Spire.Canonical.Types
-- import Spire.Expression.Embedding
-- import Spire.Expression.Types
import Spire.Surface.Types

import Control.Applicative ((<$>) , (<*>))
import Control.Monad.Reader
import qualified Text.PrettyPrint.Leijen as PP
import Text.PrettyPrint.Leijen (Doc)
import Unbound.LocallyNameless
import Spire.Canonical.Types (Nom , isWildcard)

----------------------------------------------------------------------

prettyPrint :: Display t => t -> String
prettyPrint t = render $ runFreshM $ runReaderT (display t) emptyDisplayR
  where
  render = show
  {-
  -- To adjust the printing parameters:
  render x = PP.displayS (PP.renderPretty ribbon columns x) ""
  columns = 80
  ribbon = 0.3
  -}

prettyPrintError :: (Show t , Display t) => t -> String
prettyPrintError a  = prettyPrint a ++ "    (RAW: " ++ show a ++ ")"

----------------------------------------------------------------------

-- Lift standard pretty printing ops to a monad.
sepM , fsepM , hsepM , vcatM , listM :: (Functor m , Monad m) =>
                                        [m Doc] -> m Doc
sepM  xs = PP.sep     <$> sequence xs
fsepM xs = PP.fillSep <$> sequence xs
hsepM xs = PP.hsep    <$> sequence xs
vcatM xs = PP.vcat    <$> sequence xs
listM xs = PP.list    <$> sequence xs

nestM , indentM :: Functor m => Int -> m Doc -> m Doc
nestM   n = fmap $ PP.nest n
indentM n = fmap $ PP.indent n

parensM , groupM , alignM :: Functor m => m Doc -> m Doc
parensM = fmap PP.parens
groupM  = fmap PP.group
alignM  = fmap PP.align

infixr 5 </> , <$$> , <$+$>
infixr 6 <> , <+>
(<>) , (<+>) , (</>) , (<$$>) , (<$+$>) ::
  Monad m => m Doc -> m Doc -> m Doc
(<>) = liftM2 (PP.<>)
(<+>) = liftM2 (PP.<+>)
(</>) = liftM2 (PP.</>)
(<$$>) = liftM2 (PP.<$$>)
(<$+$>) = liftM2 (PP.<$>)

dt :: String -> DisplayM Doc
dt = return . PP.text

----------------------------------------------------------------------

binding :: (Precedence t', Precedence t, Display t) =>
           t' -> Nom -> t -> DisplayM Doc
binding outside nm tp | isWildcard nm = wrapNonAssoc outside tp
binding outside nm tp = parensM . hsepM $ [d nm , dt ":" , d tp]

----------------------------------------------------------------------
-- Short hands.

d :: Display t => t -> DisplayM Doc
d = display

w , ww :: (Precedence o , Precedence i, Display i) =>
          o -> i -> DisplayM Doc
w  = wrap         -- Mnemonic: (w)rapped display
ww = wrapNonAssoc -- Mnemonic: (w)rapped (w)rapped display
                  -- (i.e. more wrapped :P)

----------------------------------------------------------------------
-- Syntactic-category agnostic printers.
--
-- The idea was to write all the pretty printers using these
-- ... except now all but one printer is defined by embedding.

-- Constructors with no arguments have printers with no arguments.
dTT    = dt "tt"
dTrue  = dt "true"
dFalse = dt "false"
dUnit  = dt "Unit"
dBool  = dt "Bool"
dType  = dt "Type"

-- Constructors with arguments pass *themselves* and their args to
-- their printers.
dPair o x y = ww o x <+> dt "," <+> w o y
dLam o bnd_b = do
  (nm , b) <- unbind bnd_b
  fsepM [ dt "\\" <+> w o nm <+> dt "->" , w o b ]
dPi o _A bnd_B = do
  (nm , _B) <- unbind bnd_B
  fsepM [ binding o nm _A <+> dt "->" , w o _B ]
dSg o _A bnd_B = do
  (nm , _B) <- unbind bnd_B
  binding o nm _A <+> dt "*" <+> d _B
dIf o c t f = alignM . sepM $ [ dt "if" <+> w o c
                              , dt "then" <+> w o t
                              , dt "else" <+> w o f ]
dProj1 o ab = dt "proj1" <+> ww o ab
dProj2 o ab = dt "proj2" <+> ww o ab
dApp o f a = alignM $ w o f </> ww o a
dAnn o a _A = parensM . alignM . sepM $ [ d a , dt ":" <+> d _A ]

----------------------------------------------------------------------

instance Display Syntax where
  display s = case s of
    STT -> dTT
    STrue -> dTrue
    SFalse -> dFalse

    SUnit -> dUnit
    SBool -> dBool
    SType -> dType

    SPair a b -> dPair s a b
    SLam b    -> dLam s b

    SPi _A _B -> dPi s _A _B
    SSg _A _B -> dSg s _A _B

    SVar nm   -> d nm
    SIf c t f -> dIf s c t f
    SProj1 ab -> dProj1 s ab
    SProj2 ab -> dProj2 s ab
    SApp f a  -> dApp s f a
    SAnn a _A -> dAnn s a _A

instance Display SDef where
  display (SDef nm a _A) =
    (groupM . nestM 2) (d nm <+> dt ":" <$+$> d _A) <$$>
    (groupM . nestM 2) (d nm <+> dt "=" <$+$> d a)

instance Display SProg where
  display defs =  PP.vcat . PP.punctuate PP.line <$> mapM d defs

instance Display Nom where
  display = dt . name2String

----------------------------------------------------------------------

-- instance Display Defs where
--   display = d . map embedD

-- instance Display Check where
--   display = d . embedC

-- instance Display Infer where
--   display = d . embedI

----------------------------------------------------------------------

-- instance Display Val where
--   display = d . embedI . embedV

-- instance Display Neut where
--   display = d . embedI . embedN

----------------------------------------------------------------------

instance Precedence Syntax where
  level s = case s of
    SPair _ _   -> pairLevel
    SLam _      -> lamLevel
    SPi _ _     -> piLevel
    SSg _ _     -> sgLevel
    SIf _ _ _   -> ifLevel
    SProj1 _    -> projLevel
    SProj2 _    -> projLevel
    SApp _ _    -> appLevel
    SAnn _ _    -> annLevel
    _           -> atomicLevel
  assoc s = case s of
    SPi   _ _ -> piAssoc
    SSg   _ _ -> sgAssoc
    SApp  _ _ -> appAssoc
    SPair _ _ -> pairAssoc
    _         -> AssocNone

----------------------------------------------------------------------

instance Precedence Nom where
  level _ = atomicLevel
  assoc _ = AssocNone

----------------------------------------------------------------------

-- The 'Reader' data of the 'DisplayM'.  E.g., the "flags" Tim
-- mentioned would go in here.
data DisplayR = DisplayR {}
emptyDisplayR :: DisplayR
emptyDisplayR = DisplayR {}

type DisplayM = ReaderT DisplayR FreshM

-- Convert 't' to 'Doc', using 'DisplayR'.
class Display t where
  display :: t -> DisplayM Doc

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
pairLevel      = 3
pairAssoc      = AssocRight
sgLevel        = 4
sgAssoc        = AssocRight
piLevel        = 5
piAssoc        = AssocRight
ifLevel        = 6
lamLevel       = 7
defsLevel      = 9
defLevel       = 10

-- For non-infix operators, use 'wrap' to wrap optionally recursive
-- displays as needed.
--
-- For infix operators, use 'wrap' to optionally wrap recursive
-- displays in positions consistent with association, and use
-- 'wrapNonAssoc' to optionally wrap recursive displays in positions
-- inconsistent with association.
--
-- For example, for a left associative application 'App', the
-- 'display' case could be written:
--
--   display s@(App f x) =
--     sepM [ wrap s f (display f) , wrapNonAssoc s x (display x) ]
wrap , wrapNonAssoc :: (Display t2, Precedence t1 , Precedence t2) =>
                            t1 -> t2 -> DisplayM Doc
wrap outside inside =
  if level outside  < level inside ||
     level outside == level inside && assoc outside /= assoc inside
  then parensM . display $ inside
  else display inside

wrapNonAssoc outside inside =
  if level outside <= level inside
  then parensM . display $ inside
  else display inside

----------------------------------------------------------------------