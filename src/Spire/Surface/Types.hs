module Spire.Surface.Types where
import Spire.Canonical.Types

----------------------------------------------------------------------

data Statement =
 SDef Ident Syntax Syntax
 deriving ( Show , Read )

type Statements = [Statement]

data Syntax =
    STT | STrue | SFalse
  | SQuotes StrLit
  | SPair Syntax Syntax
  | SLam (Bound Syntax)
  | SUnit | SBool | SString | SDesc | SType
  | SPi Syntax (Bound Syntax)
  | SSg Syntax (Bound Syntax)

  | SDUnit | SDRec
  | SDSum Syntax Syntax
  | SDPi Syntax (Bound Syntax)
  | SDSg Syntax (Bound Syntax)

  | SVar Ident
  | SStrAppend Syntax Syntax
  | SStrEq Syntax Syntax
  | SIf Syntax Syntax Syntax
  | SCaseBool (Bound Syntax) Syntax Syntax Syntax
  | SProj1 Syntax
  | SProj2 Syntax
  | SApp Syntax Syntax
  | SAnn Syntax Syntax
 deriving ( Show , Read )

----------------------------------------------------------------------