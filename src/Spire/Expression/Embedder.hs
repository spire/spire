module Spire.Expression.Embedder where
import Unbound.LocallyNameless
import Control.Applicative
import Spire.Canonical.Types
import Spire.Expression.Types
import Spire.Surface.Types

----------------------------------------------------------------------

embedI :: Infer -> FreshM Syntax
embedI (IPi       _A _B)     = SPi       <$> embedC _A <*> embedCB _B
embedI (ISg       _A _B)     = SSg       <$> embedC _A <*> embedCB _B
embedI (IEl       _D _X  i)  = SEl       <$> embedI _D <*> embedCB _X  <*> embedC i
embedI (IFix      _D i)      = SFix      <$> embedC _D <*> embedI  i
embedI (IEq       a  b)      = SEq       <$> embedI a  <*> embedI b

embedI (IVar v)    = return $ SVar v
embedI (IQuotes s) = return $ SQuotes s

embedI (IIf b ct cf) = SIf <$> embedC b <*> embedI ct <*> embedI cf
embedI (ISubst _P q  p) = SSubst <$> embedCB _P <*> embedI q <*> embedC p
embedI (IProj1 ab) = SProj1 <$> embedI ab
embedI (IProj2 ab) = SProj2 <$> embedI ab
embedI (IApp f a) = SApp <$> embedI f <*> embedC a
embedI (IAnn a _A) = SAnn <$> embedC a <*> embedC _A

embedC :: Check -> FreshM Syntax
embedC CRefl        = return SRefl
embedC CHere        = return SHere
embedC (CThere t)   = SThere <$> embedC t
embedC (CEnd i)     = SEnd   <$> embedC i
embedC (CRec i  _D) = SRec   <$> embedC i   <*> embedC  _D
embedC (CArg _A _B) = SArg   <$> embedC _A  <*> embedCB _B
embedC (CInit xs)   = SInit  <$> embedC  xs
embedC (CPair a b)  = SPair  <$> embedC a   <*> embedC  b
embedC (CLam b)     = SLam   <$> embedCB b
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
