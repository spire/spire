module Spire.Canonical.InitialEnv ( initEnv , initSpireR ) where
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

def :: String -> Value -> Type -> VDef
def = VDef . s2n

----------------------------------------------------------------------
