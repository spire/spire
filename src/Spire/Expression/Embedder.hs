module Spire.Expression.Embedder where
import Unbound.LocallyNameless
import Control.Applicative
import Spire.Canonical.Types
import Spire.Expression.Types
import Spire.Surface.Types

----------------------------------------------------------------------

embedI :: Infer -> FreshM Syntax
embedI ITT    = return STT
embedI ITrue  = return STrue
embedI IFalse = return SFalse
embedI IUnit  = return SUnit
embedI IBool  = return SBool
embedI IType  = return SType
embedI (IPi _A _B) = SPi <$> embedC _A <*> embedCB _B
embedI (ISg _A _B) = SSg <$> embedC _A <*> embedCB _B

embedI (IVar v) = return $ SVar v
embedI (IIf b ct cf) = SIf <$> embedC b <*> embedI ct <*> embedI cf
embedI (ICaseBool _P ct cf b) = SCaseBool <$> embedCB _P <*> embedC ct <*> embedC cf <*> embedC b
embedI (IProj1 ab) = SProj1 <$> embedI ab
embedI (IProj2 ab) = SProj2 <$> embedI ab
embedI (IApp f a) = SApp <$> embedI f <*> embedC a
embedI (IAnn a _A) = SAnn <$> embedC a <*> embedC _A

embedC :: Check -> FreshM Syntax
embedC (CPair a b) = SPair <$> embedC a <*> embedC b
embedC (CLam b) = SLam <$> embedCB b
embedC (Infer i) = embedI i

----------------------------------------------------------------------

embedCB :: Bind Nom Check -> FreshM (Bind Nom Syntax)
embedCB bnd_a = do
  (nm , a) <- unbind bnd_a
  a'       <- embedC a
  return   $ bind nm a'

embedCDef :: CDef -> FreshM SDef
embedCDef (CDef nm a _A) = SDef nm <$> embedC a <*> embedC _A

----------------------------------------------------------------------
