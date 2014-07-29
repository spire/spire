module Spire.Canonical.InitialEnv ( initEnv , initSpireR ) where
import Control.Applicative
import Data.Monoid (mempty)
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types

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
  ]

def :: String -> Value -> Type -> VDef
def = VDef . s2n

----------------------------------------------------------------------
