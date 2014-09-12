{-# LANGUAGE
    ViewPatterns
  , FlexibleInstances
  , MultiParamTypeClasses
  , TypeSynonymInstances
  #-}

module Spire.Canonical.Types where

import Control.Applicative
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import Data.Traversable
import Data.List (isPrefixOf)

import Spire.Rebound
import Spire.Options

----------------------------------------------------------------------

type Type = Value
type Nom = Name
type NomType = (Nom , Type)

data Value =
    VUnit | VBool | VEnum | VTel | VString | VType
  | VTag Value | VDesc Value

  | VPi  Value (Bind1 Value)
  | VSg  Value (Bind1 Value)

  | VFix Value Value Value Value Value Value
  | VEq  Value Value Value Value

  | VTT | VTrue | VFalse | VNil | VRefl | VHere | VEmp
  | VThere Value | VEnd Value

  | VRec Value Value | VInit Value
  | VCons Value Value
  | VPair Value Value

  | VExt Value (Bind1 Value)
  | VArg Value (Bind1 Value)

  | VLam (Bind1 Value)

  | VQuotes String
  | VNeut Nom Spine
  deriving (Show,Read,Eq,Ord)

data Elim =
    EApp Value

  | EFunc Value (Bind1 Value) Value
  | EHyps Value (Bind1 Value) (Bind2 Value) Value Value

  | EElimUnit (Bind1 Value) Value
  | EElimBool (Bind1 Value) Value Value
  | EElimPair Value (Bind1 Value) (Bind1 Value) (Bind2 Value)
  | EElimEq Value Value (Bind2 Value) Value Value
  | EElimEnum (Bind1 Value) Value (Bind3 Value)
  | EElimTel  (Bind1 Value) Value (Bind3 Value)
  | EElimDesc Value (Bind1 Value) (Bind1 Value) (Bind3 Value) (Bind3 Value)

  | EBranches (Bind1 Value)
  | ECase Value (Bind1 Value) Value
  | EProve Value (Bind1 Value) (Bind2 Value) (Bind2 Value) Value Value
  | EInd Value Value Value Value Value (Bind2 Value) (Bind3 Value) Value
  deriving (Show,Read,Eq,Ord)

data Spine = Id | Pipe Spine Elim
  deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

data Tel = Empty
  | Extend NomType Tel
  deriving (Show,Read,Eq,Ord)

snocTel :: Tel -> NomType -> Tel
snocTel Empty y = Extend y Empty
snocTel (Extend x xs) y = Extend x (snocTel xs y)

tel2List :: Tel -> [NomType]
tel2List Empty = []
tel2List (Extend (nm , _T) xs) =
  (nm , _T) : tel2List xs

----------------------------------------------------------------------

data VDef = VDef Nom Value Value
  deriving (Show,Read,Eq,Ord)

type Env = [VDef]
type VProg = Env

----------------------------------------------------------------------

data SpireR = SpireR { ctx :: Tel , env :: Env , conf :: Conf }
emptySpireR = SpireR { ctx = Empty
                     , env = []
                     , conf = error "You need to define 'conf' before using 'emptySpireR'."
                     }
data SpireS = SpireS { unifierCtx :: UnifierCtx }
emptySpireS = SpireS { unifierCtx = [] }
type UnifierCtx = Env
type SpireM = StateT SpireS (ReaderT SpireR (Except String))

----------------------------------------------------------------------

extendCtx :: Nom -> Type -> SpireM a -> SpireM a
extendCtx x _A = local
  (\r -> r { ctx = snocTel (ctx r) (x , _A) })

extendEnv :: Nom -> Value -> Type -> SpireM a -> SpireM a
extendEnv x a _A = local
  (\r -> r { env = VDef x a _A : (env r) })

----------------------------------------------------------------------

wildcard = "_"
wildcardR :: Nom
wildcardR = s2n wildcard

isWildcard :: Nom -> Bool
isWildcard nm = n2s nm == wildcard

----------------------------------------------------------------------

instance Subst SpireM Value where
  vari = return . flip VNeut Id

  trav s VUnit = return VUnit
  trav s VBool = return VBool
  trav s VEnum = return VEnum
  trav s VTel = return VTel
  trav s VString = return VString
  trav s VType = return VType

  trav s VTT = return VTT
  trav s VTrue = return VTrue
  trav s VFalse = return VFalse
  trav s VNil = return VNil
  trav s VRefl = return VRefl
  trav s VHere = return VHere
  trav s VEmp = return VEmp

  trav s (VQuotes str) = return (VQuotes str)

  trav s (VTag _E) = VTag <$> trav s _E
  trav s (VDesc _I) = VDesc <$> trav s _I
  trav s (VThere t) = VThere <$> trav s t
  trav s (VEnd i) = VEnd <$> trav s i
  trav s (VInit xs) = VInit <$> trav s xs

  trav s (VLam b) = VLam <$> travBind s b

  trav s (VPi _A _B) = VPi <$> trav s _A <*> travBind s _B
  trav s (VSg _A _B) = VSg <$> trav s _A <*> travBind s _B
  trav s (VExt _A _B) = VExt <$> trav s _A <*> travBind s _B
  trav s (VArg _A _B) = VArg <$> trav s _A <*> travBind s _B

  trav s (VFix l _P _I _D p i) =
    VFix <$> trav s l <*> trav s _P <*> trav s _I <*> trav s _D <*> trav s p <*> trav s i

  trav s (VEq _A a _B b) =
    VEq <$> trav s _A <*> trav s a <*> trav s _B <*> trav s b

  trav s (VRec i _D) = VRec <$> trav s i <*> trav s _D
  trav s (VCons x xs) = VCons <$> trav s x <*> trav s xs
  trav s (VPair a b) = VPair <$> trav s a <*> trav s b

  trav s (VNeut nm xs) = do
    xs' <- travSpine s xs
    x' <- s nm
    elims x' xs'

travSpine :: Sig SpireM Value -> Spine -> SpireM Spine
travSpine s Id = return Id
travSpine s (Pipe xs x) = Pipe <$> travSpine s xs <*> travElim s x

travElim :: Sig SpireM Value -> Elim -> SpireM Elim
travElim s (EApp a) = EApp <$> trav s a
travElim s (EFunc _I _X i) = EFunc <$> trav s _I <*> travBind s _X <*> trav s i
travElim s (EHyps _I _X _M i xs) =
  EHyps <$> trav s _I <*> travBind s _X <*> travBind s _M <*> trav s i <*> trav s xs
travElim s (EElimUnit _P ptt) = EElimUnit <$> travBind s _P <*> trav s ptt
travElim s (EElimBool _P pt pf) = EElimBool <$> travBind s _P <*> trav s pt <*> trav s pf
travElim s (EElimPair _A _B _P ppair) =
  EElimPair <$> trav s _A <*> travBind s _B <*> travBind s _P <*> travBind s ppair
travElim s (EElimEq _A x _P prefl y) =
  EElimEq <$> trav s _A <*> trav s x <*> travBind s _P <*> trav s prefl <*> trav s y
travElim s (EElimEnum _P pnil pcons) =
  EElimEnum <$> travBind s _P <*> trav s pnil <*> travBind s pcons
travElim s (EElimTel _P pemp pext) =
  EElimTel <$> travBind s _P <*> trav s pemp <*> travBind s pext
travElim s (EElimDesc _I _P pend prec parg) =
  EElimDesc <$> trav s _I <*> travBind s _P <*> travBind s pend <*> travBind s prec <*> travBind s parg
travElim s (EBranches _P) = EBranches <$> travBind s _P
travElim s (ECase _E _P cs) = ECase <$> trav s _E <*> travBind s _P <*> trav s cs
travElim s (EProve _I _X _M m i xs) =
  EProve <$> trav s _I <*> travBind s _X <*> travBind s _M <*> travBind s m <*> trav s i <*> trav s xs
travElim s (EInd l _P _I _D p _M m i) =
  EInd <$> trav s l <*> trav s _P <*> trav s _I <*> trav s _D
       <*> trav s p <*> travBind s _M <*> travBind s m <*> trav s i

----------------------------------------------------------------------

elims :: Value -> Spine -> SpireM Value
elims x Id = return x
elims x (Pipe fs f) = flip elim f =<< elims x fs

elimB :: Bind f Value -> Elim -> SpireM (Bind f Value)
elimB (Bind v) e = Bind <$> elim v e

----------------------------------------------------------------------

elim :: Value -> Elim -> SpireM Value

elim (VNeut nm fs) f        = return $ VNeut nm (Pipe fs f)
elim (VLam f)      (EApp a) = f `sub1` a
elim _             (EApp _) = throwError "Ill-typed evaluation of function application"

elim VTT    (EElimUnit _P ptt)  = return ptt
elim _      (EElimUnit _P ptt)  = throwError "Ill-typed evaluation of elimUnit"

elim VTrue  (EElimBool _P pt _) = return pt
elim VFalse (EElimBool _P _ pf) = return pf
elim _      (EElimBool _P _  _) = throwError "Ill-typed evaluation of elimBool"

elim (VPair a b) (EElimPair _A _B _P ppair) = do
  sub2 ppair a b
elim _               (EElimPair _A _B _P ppair)  =
  throwError "Ill-typed evaluation of elimPair"

elim VRefl (EElimEq _A x _P prefl y) =
  return prefl
elim _               (EElimEq _A x _P prefl y)  =
  throwError "Ill-typed evaluation of elimEq"

elim VNil         (EElimEnum _P pn _)  =
  return pn
elim (VCons x xs) (EElimEnum _P pn pc) = do
  ih <- xs `elim` EElimEnum _P pn pc
  sub3 pc x xs ih
elim _            (EElimEnum _P _ _)  =
  throwError "Ill-typed evaluation of elimEnum"

elim VEmp            (EElimTel _P pemp pext) =
  return pemp
elim (VExt _A _B) (EElimTel _P pemp pext) = do
  ih <- _B `elimB` (EElimTel _P pemp pext)
  sub3 pext _A (VLam _B) (VLam ih)
elim _               (EElimTel _P pemp pext)  =
  throwError "Ill-typed evaluation of elimTel"

elim (VEnd i)        (EElimDesc _I _P pend prec parg) =
  pend `sub1` i
elim (VRec i _D)     (EElimDesc _I _P pend prec parg) = do
  ih <- _D `elim` EElimDesc _I _P pend prec parg
  sub3 prec i _D ih
elim (VArg _A _B) (EElimDesc _I _P pend prec parg) = do
  ih <- _B `elimB` (EElimDesc _I _P pend prec parg)
  sub3 parg _A (VLam _B) (VLam ih)
elim _            (EElimDesc _I _P pend prec parg)  =
  throwError "Ill-typed evaluation of elimDesc"

elim (VInit xs) (EInd l _P _I _D p _M m i) = do
  _X <- vBind "i" (VFix l _P _I _D p)
  ih <- rBind2 "i" "x" $ \ j x -> rInd l _P _I _D p _M m (vVar j) x
  ihs <- _D `elim` EProve _I _X _M ih i xs
  sub3 m i xs ihs
elim _            (EInd l _P _I _D p _M m i)  =
  throwError "Ill-typed evaluation of ind"

elim (VEnd j)        (EFunc _I _X i) =
  return $ VEq _I j _I i
elim (VRec j _D)     (EFunc _I _X i) =
  vProd <$> _X `sub1` j <*> _D `elim` EFunc _I _X i
elim (VArg _A _B)    (EFunc _I _X i) =
  VSg _A <$> _B `elimB` EFunc _I _X i
elim _               (EFunc _I _X i) =
  throwError "Ill-typed evaluation of Func"

elim (VEnd j)        (EHyps _I _X _M i q) =
  return $ VUnit
elim (VRec j _D)     (EHyps _I _X _M i xxs) = do
  _A <- _X `sub1` j
  _B <- _D `elim` EFunc _I _X i
  let (x , xs) = ("x" , "xs")
  ppair <- vProd <$> sub2 _M j (var x) <*> _D `elim` EHyps _I _X _M i (var xs)
  elim xxs =<< (return . EElimPair _A (kBind _B) (kBind VType) =<< bind2 x xs ppair)
elim (VArg _A _B)    (EHyps _I _X _M i axs) = do
  _B' <- _B `elimB` EFunc _I _X i
  let xs = "xs"
  undefined
  -- ppair <- _B `elim` EHyps _I _X _M i (var xs)
--   axs `elim` EElimPair _A _B' (kBind VType) (bind2 a xs ppair)
elim _D               (EHyps _I _X _M i xs) =
  throwError $
   "Ill-typed evaluation of Hyps:" ++
   "\nDescription:\n" ++ show _D ++
   "\nPair:\n" ++ show xs

-- elim (VEnd j)        (EProve _I _X _M m i q) =
--   return $ VTT
-- elim (VRec j _D)     (EProve _I _X _M m i xxs) = do
--   _A <- _X `sub` j
--   _B <- _D `elim` EFunc _I _X i
--   (nm_xxs , x , xs) <- (,,) <$> freshR "xxs" <*> freshR "x" <*> freshR "xs"
--   _M' <- VRec j _D `elim` EHyps _I _X _M i (vVar nm_xxs)
--   ppair <- VPair <$> m `sub2` (j , vVar x) <*> _D `elim` EProve _I _X _M m i (vVar xs)
--   xxs `elim` EElimPair _A (kBind _B) (bind nm_xxs _M') (bind2 x xs ppair)
-- elim (VArg _A _B)    (EProve _I _X _M m i axs) = do
--   (nm_axs , a , xs) <- (,,) <$> freshR "axs" <*> freshR "a" <*> freshR "xs"
--   _Ba <- _B `sub` vVar a
--   _B' <- _Ba `elim` (EFunc _I _X i)
--   _M' <- VArg _A _B `elim` EHyps _I _X _M i (vVar nm_axs)
--   ppair <- _Ba `elim` EProve _I _X _M m i (vVar xs)
--   axs `elim` EElimPair _A (bind a _B') (bind nm_axs _M') (bind2 a xs ppair)
-- elim _               (EProve _I _X _M m i xs) =
--   throwError "Ill-typed evaluation of prove"

elim VNil         (EBranches _P) =
  return VUnit
elim (VCons l _E)    (EBranches _P) = do
  _P' <- _P `subComp1` (VThere . vVar)
  vProd <$> _P `sub1` VHere  <*> _E `elim` EBranches _P'
elim _             (EBranches _P) =
  throwError "Ill-typed evaluation of Branches"

-- elim VHere         (ECase (VCons l _E) _P ccs) = do
--   _Pthere <- _P `subCompose` VThere
--   _A <- _P `sub` VHere
--   _B <- _E `elim` EBranches _Pthere
--   let _M = _A
--   c <- freshR "c"
--   let ppair = vVar c
--   ccs `elim` EElimPair _A (kBind _B) (kBind _M) (bind2 c wildcardR ppair)
-- elim (VThere t)    (ECase (VCons l _E) _P ccs) = do
--   _Pthere <- _P `subCompose` VThere
--   _A <- _P `sub` VHere
--   _B <- _E `elim` EBranches _Pthere
--   _M <- _P `sub` (VThere t)
--   cs <- freshR "cs"
--   ppair <- t `elim` ECase _E _Pthere (vVar cs)
--   ccs `elim` EElimPair _A (kBind _B) (kBind _M) (bind2 wildcardR cs ppair)
-- elim _             (ECase _E _P ccs) =
--   throwError "Ill-typed evaluation of case"

elim _ _ = undefined

----------------------------------------------------------------------

-- vPi :: String -> SpireM Value ->  SpireM Value -> SpireM Value
-- vPi s x y = do
--   x' <- x
--   y' <- y
--   return . (VPi x') =<< bind1 s y'

vBind :: String -> (Value -> Value) -> SpireM (Bind1 Value)
vBind x f = bind1 x (f (var x))

kBind :: Value -> Bind1 Value
kBind x = Bind x

rBind :: String -> (Nom -> Value) -> SpireM (Bind1 Value)
rBind x f = bind1 x (f (s2n x))

rBind2 :: String -> String -> (Nom -> Nom -> Value) -> SpireM (Bind2 Value)
rBind2 x y f = bind2 x y (f (s2n x) (s2n y))

var :: String -> Value
var = vVar . s2n

vVar :: Name -> Value
vVar nm = VNeut nm Id

vProd :: Value -> Value -> Value
vProd _A _B = VSg _A (Bind _B)

vArr :: Value -> Value -> Value
vArr _A _B = VPi _A (Bind _B)

eIf :: Value -> Value -> Value -> Elim
eIf _C ct cf = EElimBool (Bind _C) ct cf

----------------------------------------------------------------------

rElimUnit :: Bind1 Value -> Value -> Nom -> Value
rElimUnit _P ptt u = VNeut u (Pipe Id (EElimUnit _P ptt))

rElimBool :: Bind1 Value -> Value -> Value -> Nom -> Value
rElimBool _P pt pf b = VNeut b (Pipe Id (EElimBool _P pt pf))

rElimPair :: Type -> Bind1 Type -> Bind1 Type -> Bind2 Value -> Nom -> Value
rElimPair _A _B _P ppair ab = VNeut ab (Pipe Id (EElimPair _A _B _P ppair))

rElimEq :: Type -> Value -> Bind2 Value -> Value -> Value -> Nom -> Value
rElimEq _A x _P prefl y q = VNeut q (Pipe Id (EElimEq _A x _P prefl y))

rElimEnum :: Bind1 Value -> Value -> Bind3 Value -> Nom -> Value
rElimEnum _P pnil pcons xs = VNeut xs (Pipe Id (EElimEnum _P pnil pcons))

rElimTel :: Bind1 Value -> Value -> Bind3 Value -> Nom -> Value
rElimTel _P pemp pext _T = VNeut _T (Pipe Id (EElimTel _P pemp pext))

rElimDesc :: Value -> Bind1 Value -> Bind1 Value -> Bind3 Value -> Bind3 Value -> Nom -> Value
rElimDesc _I _P pend prec parg _D = VNeut _D (Pipe Id (EElimDesc _I _P pend prec parg))

rBranches :: Nom -> Bind1 Value -> Type
rBranches _E _P = VNeut _E (Pipe Id (EBranches _P))

rFunc :: Value -> Nom -> Bind1 Value -> Value -> Type
rFunc _I _D _X i = VNeut _D (Pipe Id (EFunc _I _X i))

rHyps :: Value -> Nom -> Bind1 Value -> Bind2 Value -> Value -> Value -> Type
rHyps _I _D _X _M i xs = VNeut _D (Pipe Id (EHyps _I _X _M i xs))

rProve :: Value -> Nom -> Bind1 Value -> Bind2 Value -> Bind2 Value -> Value -> Value -> Type
rProve _I _D _X _M m i xs = VNeut _D (Pipe Id (EProve _I _X _M m i xs))

rInd :: Value -> Value -> Value -> Value -> Value -> Bind2 Value -> Bind3 Value -> Value -> Nom -> Type
rInd l _P _I _D p _M m i x = VNeut x (Pipe Id (EInd l _P _I _D p _M m i))

rCase :: Value -> (Bind1 Value) -> Value -> Nom -> Value
rCase _E _P cs t = VNeut t (Pipe Id (ECase _E _P cs))

----------------------------------------------------------------------

-- vLam :: String -> Value -> Value
-- vLam s b = VLam (sbind s b)

-- vEta :: (Value -> Value) -> String -> Value
-- vEta f s = vLam s (f (var s))

-- vEta2 :: (Value -> Value -> Value) -> String -> String -> Value
-- vEta2 f s1 s2 = vLam s1 $ vLam s2 $ f (var s1) (var s2)

-- vApp :: String -> Value -> Value
-- vApp = vApp' . s2n

-- vApp' :: Nom -> Value -> Value
-- vApp' f x = VNeut f (Pipe Id (EApp x))

-- vApp2 :: String -> Value -> Value -> Value
-- vApp2 f x y = VNeut (s2n f) (Pipe (Pipe Id (EApp x)) (EApp y))

-- vApp3 :: String -> Value -> Value -> Value -> Value
-- vApp3 f x y z = VNeut (s2n f) (Pipe (Pipe (Pipe Id (EApp x)) (EApp y)) (EApp z))

-- fbind :: String -> String -> Bind1 Value
-- fbind = fbind' . s2n

-- fbind' :: Nom -> String -> Bind1 Value
-- fbind' f x = sbind x $ vApp' f (var x)

-- fbind2 :: String -> String -> String -> Bind2 Value
-- fbind2 f x y = sbind2 x y $ vApp2 f (var x) (var y)

-- fbind3 :: String -> String -> String -> String -> Bind3 Value
-- fbind3 f x y z = sbind3 x y z $ vApp3 f (var x) (var y) (var z)

-- vElimUnit :: String -> String -> String -> Value
-- vElimUnit _P ptt u = rElimUnit (fbind _P "u") (var ptt) (s2n u)

-- vElimBool :: String -> String -> String -> String -> Value
-- vElimBool _P pt pf b = rElimBool (fbind _P "b") (var pt) (var pf) (s2n b)

-- vElimPair :: String -> String -> String -> String -> String -> Value
-- vElimPair _A _B _P ppair ab = rElimPair
--   (var _A)
--   (fbind _B "a")
--   (fbind _P "xs")
--   (fbind2 ppair "a" "b")
--   (s2n ab)

-- vElimEq :: String -> String -> String -> String -> String -> String -> Value
-- vElimEq _A x _P prefl y q = rElimEq
--   (var _A)
--   (var x)
--   (fbind2 _P "y" "q")
--   (var prefl)
--   (var y)
--   (s2n q)

-- vElimEnum :: String -> String -> String -> String -> Value
-- vElimEnum _P pnil pcons xs = rElimEnum
--   (fbind _P "xs")
--   (var pnil)
--   (fbind3 pcons "x" "xs" "pxs")
--   (s2n xs)

-- vElimTel :: String -> String -> String -> String -> Value
-- vElimTel _P pemp pext _T = rElimTel
--   (fbind _P "T")
--   (var pemp)
--   (fbind3 pext "A" "B" "pb")
--   (s2n _T)

-- vElimDesc :: String -> String -> String -> String -> String -> String -> Value
-- vElimDesc _I _P pend prec parg _D = rElimDesc
--   (var _I)
--   (fbind _P "D")
--   (fbind pend "i")
--   (fbind3 prec "i" "D" "pd")
--   (fbind3 parg "A" "B" "pb")
--   (s2n _D)

-- vBranches :: String -> String -> Value
-- vBranches _E _P = rBranches
--   (s2n _E)
--   (fbind _P "t")

-- vFunc :: String -> String -> String -> String -> Value
-- vFunc _I _D _X i = rFunc
--   (var _I)
--   (s2n _D)
--   (fbind _X "i")
--   (var i)

-- vHyps :: String -> String -> String -> String -> String -> String -> Value
-- vHyps _I _D _X _M i xs = rHyps
--   (var _I)
--   (s2n _D)
--   (fbind _X "i")
--   (fbind2 _M "i" "x")
--   (var i)
--   (var xs)

-- vProve :: String -> String -> String -> String -> String -> String -> String -> Value
-- vProve _I _D _X _M m i xs = rProve
--   (var _I)
--   (s2n _D)
--   (fbind _X "i")
--   (fbind2 _M "i" "x")
--   (fbind2 m "i" "x")
--   (var i)
--   (var xs)

-- vInd :: String -> String -> String -> String -> String -> String -> String -> String -> String -> Value
-- vInd l _P _I _D p _M m i x = rInd
--   (var l)
--   (var _P)
--   (var _I)
--   (var _D)
--   (var p)
--   (fbind2 _M "i" "x")
--   (fbind3 m "i" "xs" "ihs")
--   (var i)
--   (s2n x)

-- vCase :: String -> String -> String -> String -> Value
-- vCase _E _P cs t = rCase
--   (var _E)
--   (fbind _P "t")
--   (var cs)
--   (s2n t)

-- vFix :: String -> String -> String -> String -> String -> String -> Value
-- vFix l _P _I _D p i = VFix
--   (var l)
--   (var _P)
--   (var _I)
--   (var _D)
--   (var p)
--   (var i)

-- ----------------------------------------------------------------------
