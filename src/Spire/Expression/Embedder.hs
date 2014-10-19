module Spire.Expression.Embedder where
import Spire.Expression.Types
import Spire.Surface.Types
import Spire.Bound
import Bound.Scope.Simple

----------------------------------------------------------------------

embedI :: Captured a => Infer a -> Syntax
embedI (IPi       _A _B)     = SPi "x"   (embedC _A) (embedCB1 _B)
embedI (ISg       _A _B)     = SSg "x"   (embedC _A) (embedCB1 _B)
embedI (IEq       a  b)      = SEq       (embedI a)  (embedI b)

embedI (IVar v)    = SVar $ captured v
embedI (IQuotes s) = SQuotes s

embedI (IIf b ct cf) = SIf (embedC b) (embedI ct) (embedI cf)
embedI (IApp f a) = SApp (embedI f) (embedC a)
embedI (IAnn a _A) = SAnn (embedC a) (embedC _A)

embedC :: Captured a => Check a -> Syntax
embedC CRefl        = SRefl
embedC CHere        = SHere
embedC (CThere t)   = SThere $ embedC t
embedC (CEnd i)     = SEnd   $ embedC i
embedC (CRec i  _D) = SRec     (embedC i) (embedC  _D)
embedC (CArg _A _B) = SArg "x" (embedC _A)  (embedCB1 _B)
embedC (CInit xs)   = SInit    (embedC  xs)
embedC (CPair a b)  = SPair    (embedC a)   (embedC b)
embedC (CLam b)     = SLam "x" (embedCB1 b)
embedC (Infer i)    = embedI i

----------------------------------------------------------------------

embedCB1 :: Captured a => Scope () Check a -> Syntax
embedCB1 = embedC . fromScope

embedCB2 :: Captured a => Scope Bool Check a -> Syntax
embedCB2 = embedC . fromScope

embedCB3 :: Captured a => Scope Three Check a -> Syntax
embedCB3 = embedC . fromScope

embedCDef :: CDef -> Stmt
embedCDef (CDef nm a _A) = SDef nm (embedC a) (embedC _A)

----------------------------------------------------------------------
