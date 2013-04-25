module Spire.Expression.Types where
import Spire.Canonical.Types

----------------------------------------------------------------------

data Check =
    CPair Check Check
  | CLam (Bound Check)
  | Infer Infer
  deriving ( Show, Read )

data Infer =
    ITT | ITrue | IFalse
  | IQuotes StrLit
  | ILamAnn Check (Bound Infer)
  | IUnit | IBool | IString | IProg | IType
  | IPi Check (Bound Check)
  | ISg Check (Bound Check)
  | IDefs [Def]
  | IVar Ident
  | IStrAppend Check Check
  | IStrEq Check Check
  | IIf Check Infer Infer
  | ICaseBool (Bound Check) Check Check Check
  | IProj1 Infer
  | IProj2 Infer
  | IApp Infer Check
  | IAnn Check Check
  deriving ( Show, Read )

----------------------------------------------------------------------

type Ctx = [(Ident , Type)]
type Def = (Ident , Check , Check)

----------------------------------------------------------------------