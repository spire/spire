{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, RankNTypes #-}
module Spire.Surface.PrettyPrinting (prettyPrint) where
import Spire.Surface.Types
import Spire.Surface.Parsing
import Spire.Canonical.Types
import Spire.Expression.Types

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader
import Text.PrettyPrint as PP

----------------------------------------------------------------------

prettyPrint :: Display t => t -> String
prettyPrint t = render $ runReader (display t) initialDisplayData

-- Short hands.
d :: Display t => t -> DisplayMonad Doc
d = display

-- Lift standard pretty printing ops to a monad.
--
-- Might be more legible below to lift '(<+>)' and use it infix
-- instead of 'sepM' and lists.
sepM :: (Functor m , Monad m) => [m Doc] -> m Doc
sepM xs = PP.sep <$> sequence xs
vcatM :: (Functor m , Monad m) => [m Doc] -> m Doc
vcatM xs = PP.vcat <$> sequence xs
parensM :: Functor m => m Doc -> m Doc
parensM = fmap PP.parens

-- Would be better to keep around the original names from the
-- 'NomBound's and reuse them here ...
var :: Bound t -> DisplayMonad Doc
var (Bound (id , _)) = do
  k <- asks numEnclosingBinders
  d $ id ++ show k

binding :: (Precedence t', Precedence t, Display t) => t' -> Ident -> t -> DisplayMonad Doc
binding outside id tp | id == wildcard  = wrapNonAssoc outside tp
binding outside id tp = parensM . sepM $ [d id , d ":" , d tp]

----------------------------------------------------------------------

instance Display Syntax where
  display s = case s of
    STT -> d "tt"
    STrue -> d "true"
    SFalse -> d "false"
    SPair x y -> parensM . sepM $ [d x , d "," , d y]
    SLam (Bound (id , body)) -> sepM [d "\\" , d id , d "->" , d body]
    SUnit -> d "Unit"
    SBool -> d "Bool"
    SString -> d "String"
    SType -> d "Type"
    SPi tp1 (Bound (id, tp2)) ->
      sepM [binding s id tp1 , d "->" , d tp2]
    SSg tp1 (Bound (id, tp2)) ->
      sepM [binding s id tp1 , d "*", d tp2]
    SVar id -> d id
    SQuotes str -> d . show $ str
    SStrAppend s1 s2 -> sepM [w s1 , d "++" , d s2]
    SStrEq s1 s2 -> sepM [d s1 , d "==" , d s2]
    SIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    SCaseBool (Bound (id, m)) t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [d id , d "in" , d m]
           , w b , w t , w f ]
    SProj1 xy -> sepM [d "proj1" , w xy]
    SProj2 xy -> sepM [d "proj2" , w xy]
    SApp f x -> sepM [d f , w x]
    SAnn x tp -> parensM . sepM $ [d x , d ":" , d tp]
    where
      d , w :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' s
      w = wrapNonAssoc s

----------------------------------------------------------------------

instance Display Check where
  display c = case c of
    CPair x y -> parensM . sepM $ [d x , d "," , d y]
    CLam (Bound (id , body)) -> sepM [d "\\" , d id , d "->" , d body]
    Infer i -> d i
    where
      d :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' c

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
    IProg -> d "Prog" -- NC: ??? Don't see this parsed anywhere.
    IType -> d "Type"
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
           , parensM . sepM $ [d id , d "in" , d m]
           , w b , w t , w f ]
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
    VProg -> d "Prog"
    VType -> d "Type"
    VPi tp1 tp2 ->
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "->" , d tp2]
    VSg tp1 tp2 ->
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "*", d tp2]
    VTT -> d "tt"
    VTrue -> d "True"
    VFalse -> d "False"
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
           , parensM . sepM $ [var m , d "in" , d m]
           , w b , w t , w f ]
    NProj1 xy -> sepM [d "proj1" , w xy]
    NProj2 xy -> sepM [d "proj2" , w xy]
    NApp f x -> sepM [d f , w x]
    where
      d , w :: (Precedence t, Display t) => t -> DisplayMonad Doc
      d = wrap' n
      w = wrapNonAssoc n

----------------------------------------------------------------------

instance Wrap Syntax where
  wrapped s = case s of
    STT -> False
    STrue -> False
    SFalse -> False
    SQuotes str -> False
    SPair x y -> False
    SLam (Bound (id , body)) -> False
    SUnit -> False
    SBool -> False
    SString -> False
    SType -> False
    SPi tp1 (Bound (id, tp2)) -> False
    SSg tp1 (Bound (id, tp2)) -> False
    SVar id -> False
    SStrAppend s1 s2 -> True
    SStrEq s1 s2 -> True
    SIf c t f -> True
    SCaseBool (Bound (id, m)) t f b -> True
    SProj1 xy -> True
    SProj2 xy -> True
    SApp f x -> True
    SAnn x tp -> False

----------------------------------------------------------------------

instance Wrap Check where
  wrapped c = case c of
    CPair x y -> False
    CLam (Bound (id , body)) -> False
    Infer i -> wrapped i

instance Wrap Infer where
  wrapped i = case i of
    ITT -> False
    ITrue -> False
    IFalse -> False
    IQuotes str -> False
    ILamAnn tp (Bound (id , body)) -> False
    IUnit -> False
    IBool -> False
    IString -> False
    IProg -> False
    IType -> False
    IPi tp1 (Bound (id, tp2)) -> False
    ISg tp1 (Bound (id, tp2)) -> False
    IDefs defs -> False
    IVar id -> False
    IStrAppend s1 s2 -> True
    IStrEq s1 s2 -> True
    IIf c t f -> True
    ICaseBool (Bound (id, m)) t f b -> True
    IProj1 xy -> True
    IProj2 xy -> True
    IApp f x -> True
    IAnn x tp -> False

----------------------------------------------------------------------

instance Wrap Val where
  wrapped v = case v of
    VUnit -> False
    VBool -> False
    VString -> False
    VProg -> False
    VType -> False
    VPi tp1 tp2 -> False
    VSg tp1 tp2 -> False
    VTT -> False
    VTrue -> False
    VFalse -> False
    VQuotes str -> False
    VPair tx ty x y -> False
    VLam tp body -> False
    VDefs defs -> False
    Neut n -> wrapped n

instance Wrap Neut where
  wrapped n = case n of
    NVar v -> False
    NStrAppendL s1 s2 -> True
    NStrAppendR s1 s2 -> True
    NStrEqL s1 s2 -> True
    NStrEqR s1 s2 -> True
    NIf c t f -> True
    NCaseBool m t f b -> True
    NProj1 xy -> True
    NProj2 xy -> True
    NApp f x -> True

----------------------------------------------------------------------

instance Display String where
  display = return . text

instance Display Def where
  display (id , tm , tp) =
    vcatM [sepM [d id , d ":" , d tp] , sepM [d id , d "=" , d tm]]

instance Display t => Display (Bound t) where
  display (Bound (_ , x)) = local incNumEnclosingBinders $ display x

instance Display VDef where
  display (v , tp) = sepM [d v , d ":" , d tp]

instance Wrap t => Wrap (Bound t) where
  wrapped (Bound (_ , x)) = wrapped x

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
  assoc _ = AssocNone

-- XXX: remove this and add a precedence table
instance Precedence t where
  level _ = 0

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

class Display t => Wrap t where
  wrap :: t -> DisplayMonad Doc
  wrap x = (if wrapped x then parensM else id) $ display x
  -- Returns 'True' iff argument should be wrapped in parens when
  -- appearing as a subexpression.
  wrapped :: t -> Bool

----------------------------------------------------------------------