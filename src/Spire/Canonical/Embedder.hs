module Spire.Canonical.Embedder where
import Control.Applicative
import Data.Monoid (mempty)
import Unbound.LocallyNameless hiding ( Spine )
import Spire.Canonical.Types
import Spire.Expression.Types
import qualified Spire.Canonical.Builtins as B

----------------------------------------------------------------------

embedV :: Value -> FreshM Check

embedV VTT                = return $ cVar B.tt
embedV VTrue              = return $ cVar B.true
embedV VFalse             = return $ cVar B.false
embedV VNil               = return $ cVar B.nil
embedV VUnit              = return $ cVar B._Unit
embedV VBool              = return $ cVar B._Bool
embedV VString            = return $ cVar B._String
embedV VEnum              = return $ cVar B._Enum
embedV VType              = return $ cVar B._Type
                          
embedV VRefl              = return $ CRefl
embedV VHere              = return $ CHere
embedV (VQuotes s)        = return $ Infer (IQuotes s)

embedV (VThere t)         = CThere <$> embedV t
embedV (VEnd   i)         = CEnd   <$> embedV i
embedV (VTag   _E)        = Infer  <$> (IApp (iVar B._Tag)  <$> embedV _E)
embedV (VDesc  _I)        = Infer  <$> (IApp (iVar B._Desc) <$> embedV _I)
                          
embedV (VSg       _A _B)  = Infer <$> (ISg       <$> embedV _A <*> embedVB _B)
embedV (VPi       _A _B)  = Infer <$> (IPi       <$> embedV _A <*> embedVB _B)
                          
embedV (VEq _A a _B b)    = Infer <$>
  (IEq <$> (IAnn <$> embedV a <*> embedV _A) <*> (IAnn <$> embedV b <*> embedV _B))
embedV (VFix _I _D i) = Infer <$>
  (IFix <$> embedV _D <*> (IAnn <$> embedV i <*> embedV _I))

embedV (VRec  i  _D)      = CRec  <$> embedV i  <*> embedV  _D
embedV (VInit xs)         = CInit <$> embedV xs
embedV (VArg  _A _B)      = CArg  <$> embedV _A <*> embedVB _B
embedV (VCons x xs)       = Infer <$>
  iApps (iVar B.cons) <$> sequence [embedV x , embedV xs]
embedV (VPair a b)        = CPair <$> embedV a  <*> embedV  b
embedV (VLam b)           = CLam  <$> embedVB b

embedV (VNeut nm fs)      = Infer <$> embedN nm fs

----------------------------------------------------------------------

embedN :: Nom -> Spine -> FreshM Infer

embedN nm Id                 = return  $  IVar nm
embedN nm (Pipe fs (EApp a)) = IApp   <$> embedN nm fs <*> embedV a
embedN nm (Pipe fs EProj1)   = IProj1 <$> embedN nm fs
embedN nm (Pipe fs EProj2)   = IProj2 <$> embedN nm fs

embedN nm (Pipe fs (EEl _I _X i)) =
  IEl <$> embedN nm fs
    <*> embedVB _X <*> embedV i

embedN nm (Pipe fs (EElimBool _P pt pf)) =
  iApps (iVar B.elimBool) <$> sequence
    [ embedVF _P
    , embedV pt
    , embedV pf
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimEnum _P pn pc)) =
  iApps (iVar B.elimEnum) <$> sequence
    [ embedVF _P
    , embedV pn
    , embedVF3 pc
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (ESubst _P p)) =
  ISubst <$> embedVB _P <*>
    embedN nm fs <*> embedV p
embedN nm (Pipe fs (ECase _E _P cs)) =
  iApps (iVar B._case) <$> sequence
    [ embedV _E
    , embedVF _P
    , embedV cs
    , Infer <$> embedN nm fs
    ]

----------------------------------------------------------------------

embedVF :: Bind Nom Value -> FreshM Check
embedVF bnd = CLam <$> embedVB bnd

embedVF3 :: Bind Nom3 Value -> FreshM Check
embedVF3 bnd_a = do
  ((nm_x , nm_y , nm_z) , a) <- unbind bnd_a
  a' <- embedV a
  return $
    CLam $ bind nm_x $
    CLam $ bind nm_y $
    CLam $ bind nm_z $
    a'

embedVB :: Alpha a => Bind a Value -> FreshM (Bind a Check)
embedVB bnd_a = do
  (nm , a) <- unbind bnd_a
  a'       <- embedV a
  return   $ bind nm a'

embedVDef :: VDef -> FreshM CDef
embedVDef (VDef nm a _A) = CDef nm <$> embedV a  <*> pure mempty
                                   <*> embedV _A <*> pure mempty

----------------------------------------------------------------------