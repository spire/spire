module Spire.Canonical.InitialEnv ( _Branches , initEnv , initSpireR ) where
import Control.Applicative
import Data.Monoid (mempty)
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types
import Spire.Surface.PrettyPrinter
import qualified Spire.Canonical.Builtins as B

----------------------------------------------------------------------

initSpireR = emptySpireR { env = initEnv }

initEnv :: Env
initEnv = 
  [ def B.tt VTT VUnit
  , def B.true VTrue VBool
  , def B.false VFalse VBool
  , def B._Unit VUnit VType
  , def B._Bool VBool VType
  , def B._String VString VType
  , def B._Enum VEnum VType
  , def B._Type VType VType
  , def B.nil VNil VEnum
  , def B.cons (vEta2 VCons "x" "xs") (vArr VString (VEnum `vArr` VEnum))
  , def B._Desc (vEta VDesc "I" ) (VType `vArr` VType)
  , def B._Tag (vEta VTag "E") (VEnum `vArr` VType)
  , def B.elimBool elimBool _ElimBool
  , def B.elimEnum elimEnum _ElimEnum
  , def B.elimDesc elimDesc _ElimDesc
  , def B._Branches _Branches __Branches
  , def B._case _case _Case
  , def B._Func _Func __Func
  , def B._Hyps _Hyps __Hyps
  , def B.prove prove _Prove
  , def B._Fix _Fix __Fix
  ]

_ElimBool :: Type
_ElimBool =
  vPi "P" (VBool `vArr` VType) $
  vArr (vApp "P" VTrue) $
  vArr (vApp "P" VFalse) $
  vPi "b" VBool $
  vApp "P" (var "b")

elimBool :: Value
elimBool =
  vLam "P" $
  vLam "pt" $
  vLam "pf" $
  vLam "b" $
  vElimBool "P" "pt" "pf" "b"

_ElimEnum :: Type
_ElimEnum =
  vPi "P" (VEnum `vArr` VType) $
  vArr (vApp "P" VNil) $
  vArr (vPi "x" VString $ vPi "xs" VEnum $ vArr (vApp "P" (var "xs")) $ vApp "P" (VCons (var "x") (var "xs"))) $
  vPi "E" VEnum $
  vApp "P" (var "E")

elimEnum :: Value
elimEnum =
  vLam "P" $
  vLam "pnil" $
  vLam "pcons" $
  vLam "xs" $
  vElimEnum "P" "pnil" "pcons" "xs"

_ElimDesc :: Type
_ElimDesc =
  vPi "I" VType $
  vPi "P" (VDesc (var "I") `vArr` VType) $
  vPi "pend" (vPi "i" (var "I") $ vApp "P" (VEnd (var "i"))) $
  vPi "prec" (vPi "i" (var "I") $ vPi "D" (VDesc (var "I")) $ vApp "P" (var "D") `vArr` vApp "P" (VRec (var "i") (var "D"))) $
  vPi "parg" (
    vPi "A" VType $
    vPi "B" (var "A" `vArr` VDesc (var "I")) $
    vArr (vPi "a" (var "A") ("P" `vApp` (vApp "B" (var "a")))) $
    vApp "P" (VArg (var "A") (fbind "B" "a"))
  ) $
  vPi "D" (VDesc (var "I")) $
  vApp "P" (var "D")

elimDesc :: Value
elimDesc =
  vLam "I" $
  vLam "P" $
  vLam "pend" $
  vLam "prec" $
  vLam "parg" $
  vLam "D" $
  vElimDesc "I" "P" "pend" "prec" "parg" "D"

__Branches :: Type
__Branches =
  vPi "E" VEnum $
  vPi "P" (VTag (var "E") `vArr` VType) $
  VType

_Branches :: Value
_Branches = vLam "E" $ vLam "P" $
  vBranches "E" "P"

_Case :: Type
_Case =
  vPi "E" VEnum $
  vPi "P" (VTag (var "E") `vArr` VType) $
  vPi "cs" (vBranches "E" "P") $
  vPi "t" (VTag (var "E")) $
  vApp "P" (var "t")

_case :: Value
_case = vLam "E" $ vLam "P" $ vLam "cs" $ vLam "t" $
  vCase "E" "P" "cs" "t"

__Func :: Type
__Func =
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "X" (var "I" `vArr` VType) $
  vPi "i" (var "I") $
  VType

_Func :: Value
_Func = vLam "I" $ vLam "D" $ vLam "X" $ vLam "i" $
  vFunc "I" "D" "X" "i"

__Hyps :: Type
__Hyps =
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "X" (var "I" `vArr` VType) $
  vPi "M" (vPi "i" (var "I") $ ("X" `vApp` var "i") `vArr` VType) $
  vPi "i" (var "I") $
  vPi "xs" (vFunc "I" "D" "X" "i") $
  VType

_Hyps :: Value
_Hyps = vLam "I" $ vLam "D" $ vLam "X" $ vLam "M" $ vLam "i" $ vLam "xs" $
  vHyps "I" "D" "X" "M" "i" "xs"

_Prove :: Type
_Prove =
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "X" (var "I" `vArr` VType) $
  vPi "M" (vPi "i" (var "I") $ ("X" `vApp` var "i") `vArr` VType) $
  vPi "m" (vPi "i" (var "I") $ vPi "x" ("X" `vApp` var "i") $ vApp2 "M" (var "i") (var "x")) $
  vPi "i" (var "I") $
  vPi "xs" (vFunc "I" "D" "X" "i") $
  vHyps "I" "D" "X" "M" "i" "xs"

prove :: Value
prove = vLam "I" $ vLam "D" $ vLam "X" $ vLam "M" $ vLam "m" $ vLam "i" $ vLam "xs" $
  vProve "I" "D" "X" "M" "m" "i" "xs"

__Fix :: Type
__Fix =
  vPi "l" VString $
  vPi "P" VType $
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "p" (var "P") $
  vPi "i" (var "I") $
  VType

_Fix :: Value
_Fix = vLam "l" $ vLam "P" $ vLam "I" $ vLam "D" $ vLam "p" $ vLam "i" $
  vFix "l" "P" "I" "D" "p" "i"

def :: String -> Value -> Type -> VDef
def = VDef . s2n

----------------------------------------------------------------------
