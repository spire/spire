{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, ScopedTypeVariables, RankNTypes #-}
module Spire.Surface.PrettyPrinting (prettyPrint) where
import Spire.Canonical.Types
import Spire.Expression.Types

import Control.Applicative ((<$>), (<*>))
import Control.Monad.Reader
import Text.PrettyPrint as PP

prettyPrint :: Display t => t -> String
prettyPrint t = render $ runReader (display t) initialDisplayData

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

class Display t => Wrap t where
  wrap :: t -> DisplayMonad Doc
  wrap x = (if wrapped x then parensM else id) $ display x
  -- Returns 'True' iff argument should be wrapped in parens when
  -- appearing as a subexpression.
  wrapped :: t -> Bool

-- Short hands.
d :: Display t => t -> DisplayMonad Doc
d = display
w :: Wrap t => t -> DisplayMonad Doc
w = wrap

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

instance Display String where
  display = return . text

instance Display Check where
  display c = case c of
    CPair x y -> parensM . sepM $ [d x , d "," , d y]
    CLam (Bound (id , body)) -> sepM [d "\\" , d id , d "->" , d body]
    Infer i -> d i

instance Display Infer where
  display i = case i of
    ITT -> d "tt"
    ITrue -> d "True"
    IFalse -> d "False"
    ILamAnn tp (Bound (id , body)) ->
      sepM [d "\\" , d id , d "->" , d body , d ":" , d tp]
    IUnit -> d "Unit"
    IBool -> d "Bool"
    IProg -> d "Prog" -- NC: ??? Don't see this parsed anywhere.
    IType -> d "Type"
    IPi tp1 (Bound (id, tp2)) ->
      sepM [parensM . sepM $ [d id , d ":" , d tp1] , d "->" , w tp2]
    ISg tp1 (Bound (id, tp2)) ->
      sepM [parensM . sepM $ [d id , d ":" , d tp1] , d "*", w tp2]
    IDefs defs -> vcatM . map d $ defs
    IVar id -> d id
    IIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    ICaseBool (Bound (id, m)) t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [d id , d "in" , d m]
           , w t , w f , w b ]
    IProj1 xy -> sepM [d "proj1" , w xy]
    IProj2 xy -> sepM [d "proj2" , w xy]
    IApp f x -> sepM [d f , d "$" , w x]
    IAnn x tp -> parensM . sepM $ [d x , d ":" , d tp]

instance Display Def where
  display (id , tm , tp) =
    vcatM [sepM [d id , d ":" , d tp] , sepM [d id , d "=" , d tm]]

instance Display t => Display (Bound t) where
  display (Bound (_ , x)) = local incNumEnclosingBinders $ display x
incNumEnclosingBinders :: DisplayData -> DisplayData
-- XXX: could store list of 'Bound's, instead of the length of this
-- list, which would allow us to only uniquify (by appending a number)
-- when necessary.

incNumEnclosingBinders d@(DisplayData { numEnclosingBinders = k }) =
  d { numEnclosingBinders = k + 1 }

-- Would be better to keep around the original names from the
-- 'NomBound's and reuse them here ...
var :: Bound t -> DisplayMonad Doc
var (Bound (id , _)) = do
  k <- asks numEnclosingBinders
  d $ id ++ show k

instance Display Val where
  display v = case v of
    VUnit -> d "Unit"
    VBool -> d "Bool"
    VProg -> d "Prog"
    VType -> d "Type"
    VPi tp1 tp2 ->
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "->" , w tp2]
    VSg tp1 tp2 ->
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "*", w tp2]
    VTT -> d "tt"
    VTrue -> d "True"
    VFalse -> d "False"
    -- ???: what's the right way to display type-annotated pairs?
    VPair tx ty x y -> sepM [ parensM . sepM $ [d x , d "," , d y]
                            , d ":" , d (VSg tx ty) ]
    VLam tp body ->
      sepM [d "\\" , var body , d ":" , d tp , d "->" , d body]
    VDefs defs -> vcatM . map d $ defs
    Neut n -> d n

instance Display Neut where
  display n = case n of
    NVar (NomVar (id , v)) -> do
      k <- asks numEnclosingBinders
      -- XXX: the 'id' here should already be determined by the
      -- binding site of this var.  So, we could perform a sanity
      -- check here, if the list of binders were in the state.
      d $ id ++ show (k - v)
    NIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    NCaseBool m t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [var m , d "in" , d m]
           , w t , w f , w b ]
    NProj1 xy -> sepM [d "proj1" , w xy]
    NProj2 xy -> sepM [d "proj2" , w xy]
    NApp f x -> sepM [d f , d "$" , w x]

instance Display VDef where
  display (v , tp) = sepM [d v , d ":" , d tp]

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
    ILamAnn tp (Bound (id , body)) -> False
    IUnit -> False
    IBool -> False
    IProg -> False
    IType -> False
    IPi tp1 (Bound (id, tp2)) -> False
    ISg tp1 (Bound (id, tp2)) -> False
    IDefs defs -> False
    IVar id -> False
    IIf c t f -> True
    ICaseBool (Bound (id, m)) t f b -> True
    IProj1 xy -> True
    IProj2 xy -> True
    IApp f x -> True
    IAnn x tp -> False

instance Wrap t => Wrap (Bound t) where
  wrapped (Bound (_ , x)) = wrapped x

instance Wrap Val where
  wrapped v = case v of
    VUnit -> False
    VBool -> False
    VProg -> False
    VType -> False
    VPi tp1 tp2 -> False
    VSg tp1 tp2 -> False
    VTT -> False
    VTrue -> False
    VFalse -> False
    VPair tx ty x y -> False
    VLam tp body -> False
    VDefs defs -> False
    Neut n -> wrapped n

instance Wrap Neut where
  wrapped n = case n of
    NVar v -> False
    NIf c t f -> True
    NCaseBool m t f b -> True
    NProj1 xy -> True
    NProj2 xy -> True
    NApp f x -> True
