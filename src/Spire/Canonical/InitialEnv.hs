module Spire.Canonical.InitialEnv ( _Branches , initEnv ) where
import Spire.Canonical.Types
import Spire.Bound
import qualified Spire.Canonical.Builtins as B

----------------------------------------------------------------------

initEnv :: Env
initEnv = 
  [ def B.tt VTT VUnit
  , def B.true VTrue VBool
  , def B.false VFalse VBool
  , def B._Unit VUnit VType
  , def B._Bool VBool VType
  , def B._String VString VType
  , def B._Enum VEnum VType
  , def B._Tel VTel VType
  , def B._Type VType VType
  , def B.nil VNil VEnum
  , def B.cons (vEta2 VCons "x" "xs") (vArr VString (VEnum `vArr` VEnum))
  , def B._Emp VEmp VTel
  , def B._Ext _Ext __Ext
  , def B._Desc (vEta VDesc "I" ) (VType `vArr` VType)
  , def B._Tag (vEta VTag "E") (VEnum `vArr` VType)
  , def B.elimUnit elimUnit _ElimUnit
  , def B.elimBool elimBool _ElimBool
  , def B.elimPair elimPair _ElimPair
  , def B.elimEq elimEq _ElimEq
  , def B.elimEnum elimEnum _ElimEnum
  , def B.elimTel elimTel _ElimTel
  , def B.elimDesc elimDesc _ElimDesc
  , def B._Branches _Branches __Branches
  , def B._case _case _Case
  , def B._Func _Func __Func
  , def B._Hyps _Hyps __Hyps
  , def B.prove prove _Prove
  , def B.ind ind _Ind
  , def B._Fix _Fix __Fix
  ]

__Ext :: Type String
__Ext =
  vPi "A" VType $
  vPi "B" (var "A" `vArr` VTel) $
  VTel

_Ext :: Value String
_Ext = vLam "A" $ vLam "B" $
  vExt (var "A") (fbind1 "B" "a")

_ElimUnit :: Type String
_ElimUnit =
  vPi "P" (VUnit `vArr` VType) $
  vArr (vApp "P" VTT) $
  vPi "u" VUnit $
  vApp "P" (var "u")

elimUnit :: Value String
elimUnit = vLam "P" $ vLam "ptt" $ vLam "u" $
  vElimUnit (fbind1 "P" "u") (var "ptt") "u"

_ElimPair :: Type String
_ElimPair =
  vPi "A" VType $
  vPi "B" (var "A" `vArr` VType) $
  vPi "P" (vSg (var "A") (fbind1 "B" "a") `vArr` VType) $
  vArr (vPi "a" (var "A") $ vPi "b" ("B" `vApp` var "a") $ ("P" `vApp` VPair (var "a") (var "b"))) $
  vPi "ab" (vSg (var "A") (fbind1 "B" "a")) $
  vApp "P" (var "ab")

elimPair :: Value String
elimPair = vLam "A" $ vLam "B" $ vLam "P" $ vLam "ppair" $ vLam "ab" $
  vElimPair (var "A") (fbind1 "B" "a") (fbind1 "P" "ab") (fbind2 "ppair" "a" "b") "ab"

_ElimBool :: Type String
_ElimBool =
  vPi "P" (VBool `vArr` VType) $
  vArr (vApp "P" VTrue) $
  vArr (vApp "P" VFalse) $
  vPi "b" VBool $
  vApp "P" (var "b")

elimBool :: Value String
elimBool = vLam "P" $ vLam "pt" $ vLam "pf" $ vLam "b" $
  vElimBool (fbind1 "P" "b") (var "pt") (var "pf") "b"

_ElimEq :: Type String
_ElimEq =
  vPi "A" VType $
  vPi "x" (var "A") $
  vPi "P" (vPi "y" (var "A") $ VEq (var "A") (var "x") (var "A") (var "y") `vArr` VType) $
  vArr (vApp2 "P" (var "x") VRefl) $
  vPi "y" (var "A") $
  vPi "q" (VEq (var "A") (var "x") (var "A") (var "y")) $
  vApp2 "P" (var "y") (var "q")

elimEq :: Value String
elimEq = vLam "A" $ vLam "x" $ vLam "P" $ vLam "prefl" $ vLam "y" $ vLam "q" $
  vElimEq (var "A") (var "x") (fbind2 "P" "y" "q") (var "prefl") (var "y") "q"

_ElimEnum :: Type String
_ElimEnum =
  vPi "P" (VEnum `vArr` VType) $
  vArr (vApp "P" VNil) $
  vArr (vPi "x" VString $ vPi "xs" VEnum $ vArr (vApp "P" (var "xs")) $ vApp "P" (VCons (var "x") (var "xs"))) $
  vPi "E" VEnum $
  vApp "P" (var "E")

elimEnum :: Value String
elimEnum =
  vLam "P" $
  vLam "pnil" $
  vLam "pcons" $
  vLam "xs" $
  vElimEnum (fbind1 "P" "xs") (var "pnil") (fbind3 "pcons" "x" "xs" "p") "xs"

_ElimTel :: Type String
_ElimTel =
  vPi "P" (VTel `vArr` VType) $
  vPi "pemp" ("P" `vApp` VEmp) $
  vPi "pext" (
    vPi "A" VType $
    vPi "B" (var "A" `vArr` VTel) $
    vArr (vPi "a" (var "A") ("P" `vApp` (vApp "B" (var "a")))) $
    vApp "P" (vExt (var "A") (fbind1 "B" "a"))
  ) $
  vPi "T" VTel $
  vApp "P" (var "T")

elimTel :: Value String
elimTel =
  vLam "P" $
  vLam "pemp" $
  vLam "pext" $
  vLam "T" $
  vElimTel (fbind1 "P" "T") (var "pemp") (fbind3 "pext" "A" "B" "pb") "T"

_ElimDesc :: Type String
_ElimDesc =
  vPi "I" VType $
  vPi "P" (VDesc (var "I") `vArr` VType) $
  vPi "pend" (vPi "i" (var "I") $ vApp "P" (VEnd (var "i"))) $
  vPi "prec" (vPi "i" (var "I") $ vPi "D" (VDesc (var "I")) $ vApp "P" (var "D") `vArr` vApp "P" (VRec (var "i") (var "D"))) $
  vPi "parg" (
    vPi "A" VType $
    vPi "B" (var "A" `vArr` VDesc (var "I")) $
    vArr (vPi "a" (var "A") ("P" `vApp` (vApp "B" (var "a")))) $
    vApp "P" (vArg (var "A") (fbind1 "B" "a"))
  ) $
  vPi "D" (VDesc (var "I")) $
  vApp "P" (var "D")

elimDesc :: Value String
elimDesc =
  vLam "I" $
  vLam "P" $
  vLam "pend" $
  vLam "prec" $
  vLam "parg" $
  vLam "D" $
  vElimDesc (var "I") (fbind1 "P" "D")
    (fbind1 "pend" "i")
    (fbind3 "prec" "i" "D" "pd")
    (fbind3 "parg" "A" "B" "pb")
    "D"

__Branches :: Type String
__Branches =
  vPi "E" VEnum $
  vPi "P" (VTag (var "E") `vArr` VType) $
  VType

_Branches :: Value String
_Branches = vLam "E" $ vLam "P" $
  vBranches "E" (fbind1 "P" "t")

_Case :: Type String
_Case =
  vPi "E" VEnum $
  vPi "P" (VTag (var "E") `vArr` VType) $
  vPi "cs" (vBranches "E" (fbind1 "P" "t")) $
  vPi "t" (VTag (var "E")) $
  vApp "P" (var "t")

_case :: Value String
_case = vLam "E" $ vLam "P" $ vLam "cs" $ vLam "t" $
  vCase (var "E") (fbind1 "P" "t") (var "cs") "t"

__Func :: Type String
__Func =
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "X" (var "I" `vArr` VType) $
  vPi "i" (var "I") $
  VType

_Func :: Value String
_Func = vLam "I" $ vLam "D" $ vLam "X" $ vLam "i" $
  vFunc (var "I") "D" (fbind1 "X" "i") (var "i")

__Hyps :: Type String
__Hyps =
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "X" (var "I" `vArr` VType) $
  vPi "M" (vPi "i" (var "I") $ ("X" `vApp` var "i") `vArr` VType) $
  vPi "i" (var "I") $
  vPi "xs" (vFunc (var "I") "D" (fbind1 "X" "i") (var "i")) $
  VType

_Hyps :: Value String
_Hyps = vLam "I" $ vLam "D" $ vLam "X" $ vLam "M" $ vLam "i" $ vLam "xs" $
  vHyps (var "I") "D" (fbind1 "X" "i") (fbind2 "M" "i" "x") (var "i") (var "xs")

_Prove :: Type String
_Prove =
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "X" (var "I" `vArr` VType) $
  vPi "M" (vPi "i" (var "I") $ ("X" `vApp` var "i") `vArr` VType) $
  vPi "m" (vPi "i" (var "I") $ vPi "x" ("X" `vApp` var "i") $ vApp2 "M" (var "i") (var "x")) $
  vPi "i" (var "I") $
  vPi "xs" (vFunc (var "I") "D" (fbind1 "X" "i") (var "i")) $
  vHyps (var "I") "D" (fbind1 "X" "i") (fbind2 "M" "i" "x") (var "i") (var "xs")

prove :: Value String
prove = vLam "I" $ vLam "D" $ vLam "X" $ vLam "M" $ vLam "m" $ vLam "i" $ vLam "xs" $
  vProve (var "I") "D" (fbind1 "X" "i") (fbind2 "M" "i" "x") (fbind2 "m" "i" "x") (var "i") (var "xs")

_Ind :: Type String
_Ind =
  vPi "l" VString $
  vPi "P" VType $
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "p" (var "P") $
  vPi "M" (vPi "i" (var "I") $ (VFix (var "l") (var "P") (var "I") (var "D") (var "p") (var "i")) `vArr` VType) $
  vPi "m" (vPi "i" (var "I") $
    vPi "xs" (vFunc (var "I") "D" ("i" , VFix (var "l") (var "P") (var "I") (var "D") (var "p") (var "i")) (var "i")) $
    vPi "ihs" (vHyps (var "I") "D" ("i" , VFix (var "l") (var "P") (var "I") (var "D") (var "p") (var "i")) (fbind2 "M" "i" "x") (var "i") (var "xs")) $
    vApp2 "M" (var "i") (VInit (var "xs"))) $
  vPi "i" (var "I") $
  vPi "x" (VFix (var "l") (var "P") (var "I") (var "D") (var "p") (var "i")) $
  vApp2 "M" (var "i") (var "x")

ind :: Value String
ind = vLam "l" $ vLam "P" $ vLam "I" $ vLam "D" $ vLam "p" $ vLam "M" $ vLam "m" $ vLam "i" $ vLam "x" $
  vInd (var "l") (var "P") (var "I") (var "D") (var "p")
    (fbind2 "M" "i" "x") (fbind3 "m" "i" "xs" "ihs") (var "i") "x"

__Fix :: Type String
__Fix =
  vPi "l" VString $
  vPi "P" VType $
  vPi "I" VType $
  vPi "D" (VDesc (var "I")) $
  vPi "p" (var "P") $
  vPi "i" (var "I") $
  VType

_Fix :: Value String
_Fix = vLam "l" $ vLam "P" $ vLam "I" $ vLam "D" $ vLam "p" $ vLam "i" $
  VFix (var "l") (var "P") (var "I") (var "D") (var "p") (var "i")

def :: String -> Value String -> Type String -> VDef
def = VDef

----------------------------------------------------------------------
