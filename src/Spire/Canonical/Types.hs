module Spire.Canonical.Types where
import Control.Monad.Error

----------------------------------------------------------------------

newtype Bound a = Bound a
  deriving ( Eq, Show, Read )

type Var = Int
type Type = Val
type VDef = (Val , Type)
type Result a = Either String a
type VCtx = [Type]

data Val =
    VUnit | VBool | VProg | VType
  | VPi Type (Bound Type)
  | VSg Type (Bound Type)

  | VTT | VTrue | VFalse
  | VPair Val Val
  | VLam Type (Bound Val)      -- Abstracted over Neut (NVar 0)
  | VDefs [VDef]
  | Neut Neut
  deriving ( Eq, Show, Read )

data Neut =
    NVar Var
  | NIf Neut Val Val
  | NCaseBool (Bound Type) Val Val Neut
  | NProj1 Neut
  | NProj2 Neut
  | NApp Neut Val
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------
