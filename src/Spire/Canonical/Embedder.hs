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
embedV VEmp               = return $ cVar B._Emp
embedV VUnit              = return $ cVar B._Unit
embedV VBool              = return $ cVar B._Bool
embedV VString            = return $ cVar B._String
embedV VEnum              = return $ cVar B._Enum
embedV VTel               = return $ cVar B._Tel
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
embedV (VFix l _P _I _D p i) = Infer <$>
  iApps (iVar B._Fix) <$> sequence
    [ embedV l
    , embedV _P
    , embedV _I
    , embedV _D
    , embedV p
    , embedV i
    ]

embedV (VRec  i  _D)      = CRec  <$> embedV i  <*> embedV  _D
embedV (VInit xs)         = CInit <$> embedV xs
embedV (VArg  _A _B)      = CArg  <$> embedV _A <*> embedVB _B
embedV (VCons x xs)       = Infer <$>
  iApps (iVar B.cons) <$> sequence [embedV x , embedV xs]
embedV (VExt _A _B) = Infer <$>
  iApps (iVar B._Ext) <$> sequence [ embedV _A , embedVF _B ]
embedV (VPair a b)        = CPair <$> embedV a  <*> embedV  b
embedV (VLam b)           = CLam  <$> embedVB b

embedV (VNeut nm fs)      = Infer <$> embedN nm fs

----------------------------------------------------------------------

embedN :: Nom -> Spine -> FreshM Infer

embedN nm Id                 = return  $  IVar nm
embedN nm (Pipe fs (EApp a)) = IApp   <$> embedN nm fs <*> embedV a

embedN nm (Pipe fs (EFunc _I _X i)) =
  iApps (iVar B._Func) <$> sequence
    [ embedV _I
    , Infer <$> embedN nm fs
    , embedVF _X
    , embedV i
    ]
embedN nm (Pipe fs (EHyps _I _X _M i xs)) =
  iApps (iVar B._Hyps) <$> sequence
    [ embedV _I
    , Infer <$> embedN nm fs
    , embedVF _X
    , embedVF2 _M
    , embedV i
    , embedV xs
    ]
embedN nm (Pipe fs (EProve _I _X _M m i xs)) =
  iApps (iVar B.prove) <$> sequence
    [ embedV _I
    , Infer <$> embedN nm fs
    , embedVF _X
    , embedVF2 _M
    , embedVF2 m
    , embedV i
    , embedV xs
    ]
embedN nm (Pipe fs (EInd l _P _I _D p _M m i)) =
  iApps (iVar B.ind) <$> sequence
    [ embedV l
    , embedV _P
    , embedV _I
    , embedV _D
    , embedV p
    , embedVF2 _M
    , embedVF3 m
    , embedV i
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimUnit _P ptt)) =
  iApps (iVar B.elimUnit) <$> sequence
    [ embedVF _P
    , embedV ptt
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimBool _P pt pf)) =
  iApps (iVar B.elimBool) <$> sequence
    [ embedVF _P
    , embedV pt
    , embedV pf
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimPair _A _B _P ppair)) =
  iApps (iVar B.elimPair) <$> sequence
    [ embedV _A
    , embedVF _B
    , embedVF _P
    , embedVF2 ppair
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimEq _A x _P prefl y)) =
  iApps (iVar B.elimEq) <$> sequence
    [ embedV _A
    , embedV x
    , embedVF2 _P
    , embedV prefl
    , embedV y
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimEnum _P pn pc)) =
  iApps (iVar B.elimEnum) <$> sequence
    [ embedVF _P
    , embedV pn
    , embedVF3 pc
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimTel _P pemp pext)) =
  iApps (iVar B.elimTel) <$> sequence
    [ embedVF _P
    , embedV pemp
    , embedVF3 pext
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EElimDesc _I _P pend prec parg)) =
  iApps (iVar B.elimDesc) <$> sequence
    [ embedV _I
    , embedVF _P
    , embedVF pend
    , embedVF3 prec
    , embedVF3 parg
    , Infer <$> embedN nm fs
    ]
embedN nm (Pipe fs (EBranches _P)) =
  iApps (iVar B._Branches) <$> sequence
    [ Infer <$> embedN nm fs
    , embedVF _P
    ]
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

embedVF2 :: Bind Nom2 Value -> FreshM Check
embedVF2 bnd_a = do
  ((nm_x , nm_y) , a) <- unbind bnd_a
  a' <- embedV a
  return $
    CLam $ bind nm_x $
    CLam $ bind nm_y $
    a'

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
embedVDef (VDef nm a _A) = CDef nm <$> embedV a <*> embedV _A

----------------------------------------------------------------------