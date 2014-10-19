{-# LANGUAGE
    ViewPatterns
  #-}


module Spire.Canonical.Embedder where
import Bound
import Spire.Bound
import Spire.Canonical.Types
import Spire.Expression.Types
import qualified Spire.Canonical.Builtins as B

----------------------------------------------------------------------

embedV :: Free a => Value a -> Check a

embedV VTT                = cVar B.tt
embedV VTrue              = cVar B.true
embedV VFalse             = cVar B.false
embedV VNil               = cVar B.nil
embedV VEmp               = cVar B._Emp
embedV VUnit              = cVar B._Unit
embedV VBool              = cVar B._Bool
embedV VString            = cVar B._String
embedV VEnum              = cVar B._Enum
embedV VTel               = cVar B._Tel
embedV VType              = cVar B._Type

embedV VRefl              = CRefl
embedV VHere              = CHere
embedV (VQuotes s)        = Infer (IQuotes s)

embedV (VThere t)         = CThere  $ embedV t
embedV (VEnd   i)         = CEnd    $ embedV i
embedV (VTag   _E)        = Infer   $ IApp (iVar B._Tag) $ embedV _E
embedV (VDesc  _I)        = Infer   $ IApp (iVar B._Desc) $ embedV _I

embedV (VSg       _A _B)  = Infer $ ISg (embedV _A) $ embedVB _B
embedV (VPi       _A _B)  = Infer $ IPi (embedV _A) $ embedVB _B
                          
embedV (VEq _A a _B b)    = Infer $
  IEq (IAnn (embedV a) (embedV _A)) (IAnn (embedV b) (embedV _B))
embedV (VFix l _P _I _D p i) = Infer $
  iApps (iVar B._Fix) $
    [ embedV l
    , embedV _P
    , embedV _I
    , embedV _D
    , embedV p
    , embedV i
    ]

embedV (VRec  i  _D)      = CRec (embedV i) (embedV  _D)
embedV (VInit xs)         = CInit $ embedV xs
embedV (VArg  _A _B)      = CArg  (embedV _A) (embedVB _B)
embedV (VCons x xs)       = Infer $
  iApps (iVar B.cons) $ [embedV x , embedV xs]
embedV (VExt _A _B) = Infer $
  iApps (iVar B._Ext) $ [ embedV _A , embedVF _B ]
embedV (VPair a b)        = CPair (embedV a)  (embedV  b)
embedV (VLam b)           = CLam $ embedVB b
       
embedV (VNeut nm fs)      = Infer $ embedN nm fs

----------------------------------------------------------------------

embedN :: Free a => a -> Spine (Elim a) -> Infer a

embedN nm Id                 = IVar nm
embedN nm (Pipe fs (EApp a)) = IApp (embedN nm fs) (embedV a)

embedN nm (Pipe fs (EFunc _I _X i)) =
  iApps (iVar B._Func) $
    [ embedV _I
    , Infer $ embedN nm fs
    , embedVF _X
    , embedV i
    ]
embedN nm (Pipe fs (EHyps _I _X _M i xs)) =
  iApps (iVar B._Hyps) $
    [ embedV _I
    , Infer $ embedN nm fs
    , embedVF _X
    , embedVF2 _M
    , embedV i
    , embedV xs
    ]
embedN nm (Pipe fs (EProve _I _X _M m i xs)) =
  iApps (iVar B.prove) $
    [ embedV _I
    , Infer $ embedN nm fs
    , embedVF _X
    , embedVF2 _M
    , embedVF2 m
    , embedV i
    , embedV xs
    ]
embedN nm (Pipe fs (EInd l _P _I _D p _M m i)) =
  iApps (iVar B.ind) $
    [ embedV l
    , embedV _P
    , embedV _I
    , embedV _D
    , embedV p
    , embedVF2 _M
    , embedVF3 m
    , embedV i
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EElimUnit _P ptt)) =
  iApps (iVar B.elimUnit) $
    [ embedVF _P
    , embedV ptt
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EElimBool _P pt pf)) =
  iApps (iVar B.elimBool) $
    [ embedVF _P
    , embedV pt
    , embedV pf
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EElimPair _A _B _P ppair)) =
  iApps (iVar B.elimPair) $
    [ embedV _A
    , embedVF _B
    , embedVF _P
    , embedVF2 ppair
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EElimEq _A x _P prefl y)) =
  iApps (iVar B.elimEq) $
    [ embedV _A
    , embedV x
    , embedVF2 _P
    , embedV prefl
    , embedV y
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EElimEnum _P pn pc)) =
  iApps (iVar B.elimEnum) $
    [ embedVF _P
    , embedV pn
    , embedVF3 pc
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EElimTel _P pemp pext)) =
  iApps (iVar B.elimTel) $
    [ embedVF _P
    , embedV pemp
    , embedVF3 pext
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EElimDesc _I _P pend prec parg)) =
  iApps (iVar B.elimDesc) $
    [ embedV _I
    , embedVF _P
    , embedVF pend
    , embedVF3 prec
    , embedVF3 parg
    , Infer $ embedN nm fs
    ]
embedN nm (Pipe fs (EBranches _P)) =
  iApps (iVar B._Branches) $
    [ Infer $ embedN nm fs
    , embedVF _P
    ]
embedN nm (Pipe fs (ECase _E _P cs)) =
  iApps (iVar B._case) $
    [ embedV _E
    , embedVF _P
    , embedV cs
    , Infer $ embedN nm fs
    ]

----------------------------------------------------------------------

embedVB :: Free a => Bind b Value a -> SBind b Check a
embedVB = liftScope embedV

embedVF :: Free a => Bind Nom Value a -> Check a
embedVF = CLam . embedVB

embedVF2 :: Free a => Bind Nom2 Value a -> Check a
embedVF2 b = embedV $ locals1 $ \ u ->
  VLam . Scope $ VLam . Scope $
  sub2 ### b #!! u #! u

embedVF3 :: Free a => Bind Nom3 Value a -> Check a
embedVF3 b = embedV $ locals1 $ \ u ->
  VLam . Scope $ VLam . Scope $ VLam . Scope $
  sub3 #### b #!!! u #!! u #! u

embedVDef :: VDef -> CDef
embedVDef (VDef nm a _A) = CDef nm (embedV a) (embedV _A)

----------------------------------------------------------------------