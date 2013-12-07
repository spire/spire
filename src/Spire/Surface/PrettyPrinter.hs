{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , ScopedTypeVariables
           , RankNTypes
           #-}
module Spire.Surface.PrettyPrinter (prettyPrint , prettyPrintError) where
import Spire.Canonical.Embedder
import Spire.Canonical.Types
import Spire.Expression.Embedder
import Spire.Expression.Types
import Spire.Surface.Types

import Common.PrettyPrint (pp)
import PatternUnify.Context (Entry)

import Control.Applicative ((<$>))
import Control.Monad.Reader
import qualified Text.PrettyPrint.Leijen as PP
import Text.PrettyPrint.Leijen (Doc)
import Unbound.LocallyNameless hiding ( Spine )

----------------------------------------------------------------------

prettyPrint :: Display t => t -> String
prettyPrint t = render $ runFreshM $ runReaderT (display t) emptyDisplayR
  where
  -- To adjust the printing parameters:
  render x = PP.displayS (PP.renderPretty ribbon columns x) ""
  columns = 80
  ribbon = 1.0

-- The raw data is printed in color to make it easier to ignore :P
prettyPrintError :: (Show t , Display t) => t -> String
prettyPrintError a  = prettyPrint a ++ "\x1b[35m(" ++ show a ++ ")\x1b[0m"

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
binding _       nm tp = parensM . hsepM $ [pushName nm (d nm) , dt ":" , d tp]

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
dZero  = dt "zero"
dUnit  = dt "Unit"
dBool  = dt "Bool"
dNat   = dt "Nat"
dType  = dt "Type"
dWildCard = dt wildcard

-- Constructors with arguments pass *themselves* and their args to
-- their printers.
dPair o x y = ww o x <+> dt "," <+> w o y
dLam o bnd_b = do
  (nm , b) <- unbind bnd_b
  fsepM [ dt "\\" <+> pushName nm (d nm) <+> dt "->" , pushName nm (w o b) ]
dPi o _A bnd_B = do
  (nm , _B) <- unbind bnd_B
  fsepM [ binding o nm _A <+> dt "->" , pushName nm (w o _B) ]
dSg o _A bnd_B = do
  (nm , _B) <- unbind bnd_B
  binding o nm _A <+> dt "*" <+> pushName nm (d _B)
dIf o c t f = alignM . sepM $ [ dt "if" <+> w o c
                              , dt "then" <+> w o t
                              , dt "else" <+> w o f ]
dProj1 o ab = dt "proj1" <+> ww o ab
dProj2 o ab = dt "proj2" <+> ww o ab
dSuc   o n  = dt "suc"   <+> ww o n
dApp o f a = alignM $ w o f </> ww o a
dAnn _ a _A = parensM . alignM . sepM $ [ d a , dt ":" <+> d _A ]

dCaseBool o bnd t f bool =
  dt "caseBool" <+> (alignM . sepM)
    [ parensM $ dLam o bnd
      , ww o t , ww o f , ww o bool ]

----------------------------------------------------------------------

instance Display Syntax where
  display s = case s of
    STT    -> dTT
    STrue  -> dTrue
    SFalse -> dFalse
    SZero  -> dZero

    SUnit -> dUnit
    SBool -> dBool
    SNat  -> dNat
    SType -> dType

    SSuc n    -> dSuc s n
    SPair a b -> dPair s a b
    SLam b    -> dLam s b

    SPi _A _B -> dPi s _A _B
    SSg _A _B -> dSg s _A _B

    SVar nm   -> d nm
    SWildCard -> dWildCard
    SIf c t f -> dIf s c t f
    SProj1 ab -> dProj1 s ab
    SProj2 ab -> dProj2 s ab
    SApp f a  -> dApp s f a
    SAnn a _A -> dAnn s a _A
    SCaseBool bnd t f bool -> dCaseBool s bnd t f bool
    SCaseNat _ _ _ _ -> error "caseNat not supported"

instance Display SDef where
  display (SDef nm a _A) =
    (groupM . nestM 2) (d nm <+> dt ":" <$+$> d _A) <$$>
    (groupM . nestM 2) (d nm <+> dt "=" <$+$> d a)

instance Display SProg where
  display defs =  PP.vcat . PP.punctuate PP.line <$> mapM d defs

instance Display Nom where
  -- It's incorrect to use 'name2String' here, since it allows
  -- shadowing, but using 'show' is really ugly, since it prints many
  -- unnecessary freshenings.
  --
  -- The approach we take is to only freshen a name 'x' if there is
  -- another name 'y' in scope for the binding sight of 'x' s.t. 'x'
  -- and 'y' have the same string part (a 'Name' is essentially a
  -- '(String , Int)' pair, with the int used for freshening).
  --
  -- For example, the function
  --
  --   \ x . \ x . x
  --
  -- will print as
  --
  --   \ x . \ x$<n> . x$<n> .
  --
  -- A much fancier printer could detect that this example need not be
  -- freshened, but we're taking a simple approach here.
  display nm = do
    nms <- asks names
        -- Here 'nms'' is the names in scope for the binding of 'nm'.
        -- The 'nms' is a stack of bindings, so all the bindings after
        -- 'nm' correspond to bindings in scope for 'nm's binding.
        --
        -- Metavars are always freshened.
    let nms'   = drop 1 . dropWhile (/= nm) $ nms
        suffix = if name2String nm `elem` map name2String nms'
                    || isMV nm
                 then "$" ++ show (name2Integer nm)
                 else ""
    dt $ name2String nm ++ suffix

----------------------------------------------------------------------

instance Display CProg where
  display = d . runFreshM . mapM embedCDef

instance Display VProg where
  display = d . runFreshM . mapM (embedCDef <=< embedVDef)

instance Display Check where
  display = d . runFreshM . embedC

instance Display Infer where
  display = d . runFreshM . embedI

----------------------------------------------------------------------

instance Display Value where
  display = d . runFreshM . (embedC <=< embedV)

instance Display (Nom , Spine) where
  display (nm , fs) = d . runFreshM $ (embedI =<< embedN nm fs)

instance Display Tel where
  display = listM . map (uncurry $ dAnn undefined) . tel2List

----------------------------------------------------------------------

instance Display UnifierCtx where
  display = listM . map (dt . pp)

instance Display Entry where
  display = dt . pp

----------------------------------------------------------------------

instance Precedence Syntax where
  level s = case s of
    SPair _ _         -> pairLevel
    SLam _            -> lamLevel
    SPi _ _           -> piLevel
    SSg _ _           -> sgLevel
    SIf _ _ _         -> ifLevel
    SProj1 _          -> projLevel
    SProj2 _          -> projLevel
    SSuc _            -> sucLevel
    SApp _ _          -> appLevel
    SAnn _ _          -> annLevel
    SCaseBool _ _ _ _ -> caseBoolLevel
    SCaseNat  _ _ _ _ -> caseNatLevel

    STT               -> atomicLevel
    STrue             -> atomicLevel
    SFalse            -> atomicLevel
    SZero             -> atomicLevel
    SUnit             -> atomicLevel
    SBool             -> atomicLevel
    SNat              -> atomicLevel
    SType             -> atomicLevel
    SWildCard         -> atomicLevel
    SVar _            -> atomicLevel

  assoc s = case s of
    SPi   _ _         -> piAssoc
    SSg   _ _         -> sgAssoc
    SApp  _ _         -> appAssoc
    SPair _ _         -> pairAssoc

    SLam _            -> AssocNone
    SIf _ _ _         -> AssocNone
    SProj1 _          -> AssocNone
    SProj2 _          -> AssocNone
    SSuc _            -> AssocNone
    SAnn _ _          -> AssocNone
    SCaseBool _ _ _ _ -> AssocNone
    SCaseNat  _ _ _ _ -> AssocNone
    STT               -> AssocNone
    STrue             -> AssocNone
    SFalse            -> AssocNone
    SZero             -> AssocNone
    SUnit             -> AssocNone
    SBool             -> AssocNone
    SNat              -> AssocNone
    SType             -> AssocNone
    SWildCard         -> AssocNone
    SVar _            -> AssocNone

----------------------------------------------------------------------

instance Precedence Nom where
  level _ = atomicLevel
  assoc _ = AssocNone

----------------------------------------------------------------------

-- The 'Reader' data of the 'DisplayM'.  E.g., the "flags" Tim
-- mentioned would go in here.
data DisplayR = DisplayR { names :: [Nom] }
emptyDisplayR :: DisplayR
emptyDisplayR = DisplayR { names = [] }

pushName :: Nom -> DisplayM a -> DisplayM a
pushName nm = local (\d -> d { names = nm : names d })

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
sucLevel       = projLevel
fixLevel       = 0
inLevel        = 0
pairLevel      = 3
pairAssoc      = AssocRight
sgLevel        = 4
sgAssoc        = AssocRight
piLevel        = 5
piAssoc        = AssocRight
ifLevel        = 6
caseBoolLevel  = 6
caseNatLevel   = caseBoolLevel
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