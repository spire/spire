module Spire.Canonical.InitialEnv ( initEnv , initSpireR ) where
import Control.Applicative
import Data.Monoid (mempty)
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types
import Spire.Surface.PrettyPrinter

----------------------------------------------------------------------

initSpireR = emptySpireR { env = initEnv }

initEnv :: Env
initEnv = 
  [ def "tt" VTT VUnit
  , def "true" VTrue VBool
  , def "false" VFalse VBool
  , def "Unit" VUnit VType
  , def "Bool" VBool VType
  , def "String" VString VType
  , def "Type" VType VType
  , def "elimBool" elimBool _ElimBool
  ]

_ElimBool :: Type
_ElimBool =
  vPi "P" (vArr VBool VType) $
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

def :: String -> Value -> Type -> VDef
def = VDef . s2n

----------------------------------------------------------------------
