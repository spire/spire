module Spire.Canonical.Types where
import Control.Monad.Error

----------------------------------------------------------------------

data Val =
    VUnit | VBool | VString | VProg | VType
  | VPi Type (Bound Type)
  | VSg Type (Bound Type)

  | VTT | VTrue | VFalse
  | VQuotes StrLit
  | VPair Type (Bound Type) Val Val
  | VLam Type (Bound Val)
  | VDefs [VDef]
  | Neut Neut
  deriving ( Eq, Show, Read )

data Neut =
    NVar NomVar
  | NStrAppendL Neut Val
  | NStrAppendR Val Neut
  | NStrEqL Neut Val
  | NStrEqR Val Neut
  | NIf Neut Val Val
  | NCaseBool (Bound Type) Val Val Neut
  | NProj1 Neut
  | NProj2 Neut
  | NApp Neut Val
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------

type Ident = String
newtype Bound a = Bound (Ident , a)
  deriving ( Show, Read )

instance Eq a => Eq (Bound a) where
  Bound (_ , x) == Bound (_ , y) = x == y

----------------------------------------------------------------------

type Var = Int
newtype NomVar = NomVar (Ident , Var)
  deriving ( Show, Read )

instance Eq NomVar where
  NomVar (_ , i) == NomVar (_ , j) = i == j

----------------------------------------------------------------------

type Type = Val
type VDef = (Val , Type)
type Result a = Either String a
type VCtx = [Type]
type StrLit = String

----------------------------------------------------------------------
