module Spire.Expression.Types where
import Spire.Canonical.Types

----------------------------------------------------------------------

data Check =
    CLam (Bound Check)
  | CPair Check Check
  | CIn Check
  | Infer Infer
  deriving ( Show, Read )

data Infer =
    ITT | ITrue | IFalse
  | IQuotes StrLit
  | ILamAnn Check (Bound Infer)
  | IUnit | IBool | IString | IDesc | IProg | IType
  | IPi Check (Bound Check)
  | ISg Check (Bound Check)
  | IFix Check

  | IDUnit | IDRec
  | IDSum Check Check
  | IDPi Check (Bound Check)
  | IDSg Check (Bound Check)

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
  | IDInterp Check Check
  deriving ( Show, Read )

----------------------------------------------------------------------

type Ctx = [(Ident , Type)]
type Def = (Ident , Check , Check)
type Defs = [Def]

----------------------------------------------------------------------