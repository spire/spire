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
  , def B._Branches _Branches __Branches
  , def B._case _case _Case
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

__Branches :: Type
__Branches =
  vPi "E" VEnum $
  vPi "P" (VTag (var "E") `vArr` VType) $
  VType

_Branches :: Value
_Branches = vLam "E" $ vLam "P" $
  rBranches (s2n "E") (var "P")

_Case :: Type
_Case =
  vPi "E" VEnum $
  vPi "P" (VTag (var "E") `vArr` VType) $
  vPi "cs" (rBranches (s2n "E") (var "P")) $
  vPi "t" (VTag (var "E")) $
  vApp "P" (var "t")

_case :: Value
_case = vLam "E" $ vLam "P" $ vLam "cs" $ vLam "t" $
  vCase "E" "P" "cs" "t"

def :: String -> Value -> Type -> VDef
def = VDef . s2n

----------------------------------------------------------------------
