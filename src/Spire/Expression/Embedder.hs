module Spire.Expression.Embedder where
import Unbound.LocallyNameless
import Control.Applicative
import Spire.Canonical.Types
import Spire.Expression.Types
import Spire.Surface.Types

----------------------------------------------------------------------

embedI :: Infer -> FreshM Syntax
embedI ITT     = return STT
embedI ITrue   = return STrue
embedI IFalse  = return SFalse
embedI IUnit   = return SUnit
embedI IBool   = return SBool
embedI IString = return SString
embedI IType   = return SType
embedI (IList _A)  = SList <$> embedC _A
embedI (IPi _A _B) = SPi   <$> embedC _A <*> embedCB _B
embedI (ISg _A _B) = SSg   <$> embedC _A <*> embedCB _B
embedI (IEq a b)   = SEq   <$> embedI a  <*> embedI b

embedI (IVar v)    = return $ SVar v
embedI (IQuotes s) = return $ SQuotes s

embedI (IIf b ct cf) = SIf <$> embedC b <*> embedI ct <*> embedI cf
embedI (IElimBool _P ct cf b) = SElimBool <$> embedCB _P <*> embedC ct <*> embedC cf <*> embedC b
embedI (IElimList _P pn pc as) = SElimList <$> embedCB _P <*> embedC pn <*> embedCB pc <*> embedI as
embedI (ISubst _P q p) = SSubst <$> embedCB _P <*> embedI q <*> embedC p
embedI (IProj1 ab) = SProj1 <$> embedI ab
embedI (IProj2 ab) = SProj2 <$> embedI ab
embedI (IApp f a) = SApp <$> embedI f <*> embedC a
embedI (IAnn a _A) = SAnn <$> embedC a <*> embedC _A

embedC :: Check -> FreshM Syntax
embedC CNil         = return SNil
embedC CRefl        = return SRefl
embedC (CCons a as) = SCons <$> embedC a <*> embedC as
embedC (CPair a b)  = SPair <$> embedC a <*> embedC b
embedC (CLam b)     = SLam <$> embedCB b
embedC (Infer i)    = embedI i

----------------------------------------------------------------------

embedCB :: Alpha a => Bind a Check -> FreshM (Bind a Syntax)
embedCB bnd_a = do
  (nm , a) <- unbind bnd_a
  a'       <- embedC a
  return   $ bind nm a'

embedCDef :: CDef -> FreshM SDef
embedCDef (CDef nm a _ _A _) = SDef nm <$> embedC a <*> embedC _A

----------------------------------------------------------------------
