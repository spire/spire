module Spire.Canonical.Embedder where
import Control.Applicative
import Data.Monoid (mempty)
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types
import Spire.Expression.Types

----------------------------------------------------------------------

embedV :: Value -> FreshM Check

embedV VTT                = return $ Infer ITT
embedV VTrue              = return $ Infer ITrue
embedV VFalse             = return $ Infer IFalse
embedV VNil               = return $ CNil
embedV VRefl              = return $ CRefl
embedV VHere              = return $ CHere
embedV (VQuotes s)        = return $ Infer (IQuotes s)
embedV VUnit              = return $ Infer IUnit
embedV VBool              = return $ Infer IBool
embedV VString            = return $ Infer IString
embedV VType              = return $ Infer IType
                          
embedV (VThere t)         = CThere <$> embedV t
embedV (VEnd   i)         = CEnd   <$> embedV i
embedV (VTag   _E)        = Infer <$> (ITag  <$> embedV _E)
embedV (VList  _A)        = Infer <$> (IList <$> embedV _A)
embedV (VDesc  _I)        = Infer <$> (IDesc <$> embedV _I)
                          
embedV (VSg       _A _B)  = Infer <$> (ISg       <$> embedV _A <*> embedVB _B)
embedV (VPi       _A _B)  = Infer <$> (IPi       <$> embedV _A <*> embedVB _B)
                          
embedV (VEq _A a _B b)    = Infer <$>
  (IEq <$> (IAnn <$> embedV a <*> embedV _A) <*> (IAnn <$> embedV b <*> embedV _B))
embedV (VFix _I _E _Ds i) = Infer <$>
  (IFix <$> embedV _E <*> embedV  _Ds <*> (IAnn <$> embedV i <*> embedV _I))

embedV (VRec  i  _D)      = CRec  <$> embedV i  <*> embedV  _D
embedV (VInit  t  xs)     = CInit <$> embedV t  <*> embedV  xs
embedV (VArg  _A _B)      = CArg  <$> embedV _A <*> embedVB _B
embedV (VCons a as)       = CCons <$> embedV a  <*> embedV  as
embedV (VPair a b)        = CPair <$> embedV a  <*> embedV  b
embedV (VLam b)           = CLam  <$> embedVB b

embedV (VNeut nm fs)      = Infer <$> embedN nm fs

----------------------------------------------------------------------

embedN :: Nom -> Spine -> FreshM Infer

embedN nm Id                 = return  $  IVar nm
embedN nm (Pipe fs (EApp a)) = IApp   <$> embedN nm fs <*> embedV a
embedN nm (Pipe fs EProj1)   = IProj1 <$> embedN nm fs
embedN nm (Pipe fs EProj2)   = IProj2 <$> embedN nm fs

embedN nm (Pipe fs (EBranches _P)) =
  IBranches <$> (Infer <$> embedN nm fs)
    <*> embedVB _P
embedN nm (Pipe fs (EEl _I _X i)) =
  IEl <$> embedN nm fs
    <*> embedVB _X <*> embedV i

embedN nm (Pipe fs (EElimBool _P pt pf)) =
  IElimBool <$> embedVB _P <*>
    embedV pt <*> embedV pf <*> (Infer <$> embedN nm fs)
embedN nm (Pipe fs (EElimList _P pn pc)) =
  IElimList <$> embedVB _P <*>
    embedV pn <*> embedVB pc <*> embedN nm fs
embedN nm (Pipe fs (ESubst _P p)) =
  ISubst <$> embedVB _P <*>
    embedN nm fs <*> embedV p
embedN nm (Pipe fs (ECase _P cs)) =
  ICase <$> embedVB _P <*>
    embedV cs <*> embedN nm fs

----------------------------------------------------------------------

embedVB :: Alpha a => Bind a Value -> FreshM (Bind a Check)
embedVB bnd_a = do
  (nm , a) <- unbind bnd_a
  a'       <- embedV a
  return   $ bind nm a'

embedVDef :: VDef -> FreshM CDef
embedVDef (VDef nm a _A) = CDef nm <$> embedV a  <*> pure mempty
                                   <*> embedV _A <*> pure mempty

----------------------------------------------------------------------