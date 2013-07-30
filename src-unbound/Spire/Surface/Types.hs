module Spire.Surface.Types where

----------------------------------------------------------------------

data Syntax =
    STT
  | SPair Syntax Syntax
  | SLam (Bound Syntax)
  | SUnit | SBool | SType
  | SPi Syntax (Bound Syntax)
  | SSg Syntax (Bound Syntax)

  | SVar Ident
  | SProj1 Syntax
  | SProj2 Syntax
  | SApp Syntax Syntax
  | SAnn Syntax Syntax
 deriving (Show , Read)

----------------------------------------------------------------------

type Ident = String
data Bound a = Bound String a
  deriving (Show , Read)

wildcard = "_"

----------------------------------------------------------------------