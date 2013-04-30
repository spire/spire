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

-- Would be better to keep around the original names from the
-- 'NomBound's and reuse them here ...
var :: Bound t -> DisplayMonad Doc
var (Bound (id , _)) = do
  k <- asks numEnclosingBinders
  d $ id ++ show k

binding :: Display t => Ident -> t -> DisplayMonad Doc
binding id tp | id == wildcard  = d tp
binding id tp = parensM . sepM $ [d id , d ":" , d tp]

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
    SDesc -> d "Desc"
    SType -> d "Type"

    SDUnit -> d "Done"
    SDRec -> d "Rec"
    SDSum x y -> sepM [w x , d "|" , d y]
    SDProd x y -> sepM [w x , d "#" , d y]
    SDPi x y -> error "TODO"
    SDSg x y -> error "TODO"

    SPi tp1 (Bound (id, tp2)) ->
      sepM [binding id tp1 , d "->" , w tp2]
    SSg tp1 (Bound (id, tp2)) ->
      sepM [binding id tp1 , d "*", w tp2]
    SVar id -> d id
    SQuotes str -> d . show $ str
    SStrAppend s1 s2 -> sepM [w s1 , d "++" , d s2]
    SStrEq s1 s2 -> sepM [w s1 , d "==" , d s2]
    SIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    SCaseBool (Bound (id, m)) t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [d id , d "in" , d m]
           , w b , w t , w f ]
    SProj1 xy -> sepM [d "proj1" , w xy]
    SProj2 xy -> sepM [d "proj2" , w xy]
    SApp f x -> sepM [w f , d x]
    SAnn x tp -> parensM . sepM $ [d x , d ":" , d tp]

----------------------------------------------------------------------

instance Display Check where
  display c = case c of
    CPair x y -> parensM . sepM $ [d x , d "," , d y]
    CLam (Bound (id , body)) -> sepM [d "\\" , d id , d "->" , d body]
    Infer i -> d i

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
    IDProd x y -> sepM [w x , d "#" , d y]
    IDPi x y -> error "TODO"
    IDSg x y -> error "TODO"

    IPi tp1 (Bound (id, tp2)) ->
      sepM [binding id tp1 , d "->" , w tp2]
    ISg tp1 (Bound (id, tp2)) ->
      sepM [binding id tp1 , d "*", w tp2]
    IDefs defs -> vcatM . map d $ defs

    IVar id -> d id
    IQuotes str -> d . show $ str
    IStrAppend s1 s2 -> sepM [w s1 , d "++" , d s2]
    IStrEq s1 s2 -> sepM [w s1 , d "==" , d s2]
    IIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    ICaseBool (Bound (id, m)) t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [d id , d "in" , d m]
           , w b , w t , w f ]
    IProj1 xy -> sepM [d "proj1" , w xy]
    IProj2 xy -> sepM [d "proj2" , w xy]
    IApp f x -> sepM [w f , d x]
    IAnn x tp -> parensM . sepM $ [d x , d ":" , d tp]

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
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "->" , w tp2]
    VSg tp1 tp2 ->
      sepM [parensM . sepM $ [var tp2 , d ":" , d tp1] , d "*", w tp2]
    VTT -> d "tt"
    VTrue -> d "True"
    VFalse -> d "False"

    VDUnit -> d "Done"
    VDRec -> d "Rec"
    VDSum x y -> sepM [w x , d "|" , d y]
    VDProd x y -> sepM [w x , d "#" , d y]
    VDPi x y -> error "TODO"
    VDSg x y -> error "TODO"

    VQuotes str -> d . show $ str
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
    NStrAppendL s1 s2 -> sepM [w s1 , d "++" , d s2]
    NStrAppendR s1 s2 -> sepM [w s1 , d "++" , d s2]
    NStrEqL s1 s2 -> sepM [w s1 , d "==" , d s2]
    NStrEqR s1 s2 -> sepM [w s1 , d "==" , d s2]
    NIf c t f -> sepM [d "if" , d c , d "then" , d t , d "else" , d f]
    NCaseBool m t f b ->
      sepM [ d "caseBool"
           , parensM . sepM $ [var m , d "in" , d m]
           , w b , w t , w f ]
    NProj1 xy -> sepM [d "proj1" , w xy]
    NProj2 xy -> sepM [d "proj2" , w xy]
    NApp f x -> sepM [d f , w x]

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
    SDesc -> False
    SType -> False

    SDUnit -> False
    SDRec -> False
    SDSum x y -> False
    SDProd x y -> False
    SDPi x y -> False
    SDSg x y -> False

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
    IDesc -> False
    IProg -> False
    IType -> False

    IDUnit -> False
    IDRec -> False
    IDSum x y -> False
    IDProd x y -> False
    IDPi x y -> False
    IDSg x y -> False    

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
    VDesc -> False
    VProg -> False
    VType -> False
    VPi tp1 tp2 -> False
    VSg tp1 tp2 -> False
    VTT -> False
    VTrue -> False
    VFalse -> False

    VDUnit -> False
    VDRec -> False
    VDSum x y -> False
    VDProd x y -> False
    VDPi x y -> False
    VDSg x y -> False

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

class Display t => Wrap t where
  wrap :: t -> DisplayMonad Doc
  wrap x = (if wrapped x then parensM else id) $ display x
  -- Returns 'True' iff argument should be wrapped in parens when
  -- appearing as a subexpression.
  wrapped :: t -> Bool

----------------------------------------------------------------------