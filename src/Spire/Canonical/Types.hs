{-# LANGUAGE DeriveDataTypeable #-}
module Spire.Canonical.Types where
import Data.Generics

----------------------------------------------------------------------

data Val =
    VUnit | VBool | VString | VDesc | VProg | VType
  | VPi Type (Bound Type)
  | VSg Type (Bound Type)
  | VFix Desc

  | VTT | VTrue | VFalse
  | VQuotes StrLit
  | VPair Type (Bound Type) Val Val
  | VLam Type (Bound Val)

  | VDUnit | VDRec
  | VDSum Desc Desc
  | VDPi Type (Bound Desc)
  | VDSg Type (Bound Desc)
  | VIn Desc Val

  | VDefs [VDef]
  | Neut Neut
  deriving ( Eq, Show, Read, Data, Typeable )

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
  | NDInterp Neut Val
  deriving ( Eq, Show, Read, Data, Typeable )

----------------------------------------------------------------------

vSum :: Type -> Type -> Type
vSum aT bT = VSg VBool (Bound (internalId , Neut cT)) where
  cT = NIf (NVar (NomVar (internalId , 0))) aT bT

----------------------------------------------------------------------

type Ident = String
wildcard = "_"
internalId = "_x"

newtype Bound a = Bound (Ident , a)
  deriving ( Show, Read, Data, Typeable )

instance Eq a => Eq (Bound a) where
  Bound (_ , x) == Bound (_ , y) = x == y

----------------------------------------------------------------------

type Var = Int
newtype NomVar = NomVar (Ident , Var)
  deriving ( Show, Read, Data, Typeable )

instance Eq NomVar where
  NomVar (_ , i) == NomVar (_ , j) = i == j

----------------------------------------------------------------------

type Type = Val
type Desc = Val
type VDef = (Val , Type)
type Result = Either String
type VCtx = [Type]
type StrLit = String

----------------------------------------------------------------------
