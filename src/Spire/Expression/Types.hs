module Spire.Expression.Types where
import Spire.Canonical.Types

----------------------------------------------------------------------

type Ident = String
type NomBound a = Bound (Ident , a)
type Ctx = [(Ident , Type)]
type Def = (Ident , Check , Check)

data Check =
    CPair Check Check
  | CLam (NomBound Check)
  | Infer Infer
  deriving ( Eq, Show, Read )

data Infer =
    ITT | ITrue | IFalse
  | ILamAnn Check (NomBound Infer)
  | IUnit | IBool | IProg | IType
  | IPi Check (NomBound Check)
  | ISg Check (NomBound Check)
  | IDefs [Def]
  | IVar Ident
  | IIf Check Infer Infer
  | ICaseBool (NomBound Check) Check Check Check
  | IProj1 Infer
  | IProj2 Infer
  | IApp Infer Check
  | IAnn Check Check
  deriving ( Eq, Show, Read )

----------------------------------------------------------------------