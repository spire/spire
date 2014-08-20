{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  , DeriveFunctor , DeriveFoldable , DeriveTraversable
  #-}

module Spire.Canonical.Types where

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import Data.Traversable
import Data.List (isPrefixOf)
import Unbound.LocallyNameless hiding ( Spine )

import Spire.Options

----------------------------------------------------------------------

instance Fresh m => Fresh (ReaderT r m) where
  fresh = lift . fresh

instance Fresh m => Fresh (StateT r m) where
  fresh = lift . fresh

instance (Error e, Fresh m) => Fresh (ErrorT e m) where
  fresh = lift . fresh

----------------------------------------------------------------------

type Type = Value

type Nom   = Name Value
type HNom  = Name (Rebind Nom Value)
type Nom2  = (Nom , Nom)
type Nom3  = (Nom , Nom , Nom)
type Nom4  = (Nom , Nom , Nom , Nom)

type NomType = (Nom , Embed Type)

----------------------------------------------------------------------

data Value =
    VUnit | VBool | VEnum | VTel | VString | VType
  | VTag Value | VDesc Value

  | VPi  Value (Bind Nom Value)
  | VSg  Value (Bind Nom Value)

  | VFix Value Value Value Value Value Value
  | VEq  Value Value Value Value

  | VTT | VTrue | VFalse | VNil | VRefl | VHere | VEmp
  | VThere Value | VEnd Value

  | VRec Value Value | VInit Value
  | VCons Value Value
  | VPair Value Value

  | VExt Value (Bind Nom Value)
  | VArg Value (Bind Nom Value)

  | VLam (Bind Nom Value)

  | VQuotes String
  | VNeut Nom Spine
  deriving Show

data Elim =
    EApp Value

  | EFunc Value (Bind Nom Value) Value
  | EHyps Value (Bind Nom Value) (Bind Nom2 Value) Value Value

  | EElimUnit (Bind Nom Value) Value
  | EElimBool (Bind Nom Value) Value Value
  | EElimPair Value (Bind Nom Value) (Bind Nom Value) (Bind Nom2 Value)
  | EElimEq Value Value (Bind Nom2 Value) Value Value
  | EElimEnum (Bind Nom Value) Value (Bind Nom3 Value)
  | EElimTel  (Bind Nom Value) Value (Bind Nom3 Value)
  | EElimDesc Value (Bind Nom Value) (Bind Nom Value) (Bind Nom3 Value) (Bind Nom3 Value)

  | EBranches (Bind Nom Value)
  | ECase Value (Bind Nom Value) Value
  | EProve Value (Bind Nom Value) (Bind Nom2 Value) (Bind Nom2 Value) Value Value
  | EInd Value Value Value Value Value (Bind Nom2 Value) (Bind Nom3 Value) Value
  deriving Show

type Spine = SpineFunctor Elim

data SpineFunctor a = Id | Pipe (SpineFunctor a) a
  deriving (Show , Functor , Foldable , Traversable)

$(derive [''Value , ''Elim , ''SpineFunctor])
instance Alpha Value
instance Alpha Elim
instance Alpha Spine

instance Eq Value where
  (==) = aeq
instance Eq Elim where
  (==) = aeq
instance Eq Spine where
  (==) = aeq

----------------------------------------------------------------------

-- ??? Why have 'Rebind' here?
data Tel = Empty
  | Extend (Rebind NomType Tel)
  deriving Show

$(derive [''Tel])
instance Alpha Tel

snocTel :: Tel -> NomType -> Tel
snocTel Empty y = Extend (rebind y Empty)
snocTel (Extend (unrebind -> (x , xs))) y = Extend (rebind x (snocTel xs y))

tel2List :: Tel -> [(Nom , Type)]
tel2List Empty = []
tel2List (Extend (unrebind -> ((nm , unembed -> _T) , xs))) =
  (nm , _T) : tel2List xs

----------------------------------------------------------------------

data VDef = VDef Nom Value Value
  deriving (Show , Eq)

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
type SpireM = StateT SpireS (ReaderT SpireR (ErrorT String FreshM))

----------------------------------------------------------------------

extendCtx :: Nom -> Type -> SpireM a -> SpireM a
extendCtx x _A = local
  (\r -> r { ctx = snocTel (ctx r) (x , Embed _A) })

extendEnv :: Nom -> Value -> Type -> SpireM a -> SpireM a
extendEnv x a _A = local
  (\r -> r { env = VDef x a _A : (env r) })

----------------------------------------------------------------------

wildcard = "_"
wildcardR :: Nom
wildcardR = s2n wildcard

isWildcard :: Nom -> Bool
isWildcard nm = name2String nm == wildcard

----------------------------------------------------------------------

freshR :: Fresh m => String -> m Nom
freshR = fresh . s2n

freshMV :: Fresh m => String -> m Nom
freshMV suffix = fresh . s2n $ "?" ++ suffix

isMV :: Nom -> Bool
isMV nm = "?" `isPrefixOf` name2String nm

-- Return the non-'?' part of a mvars string.
mv2String :: Nom -> String
mv2String nm = case name2String nm of
  '?':suffix -> suffix
  _          -> error $ "mv2String: not an mvar: " ++ show nm

bind2 x y = bind (x , y)
bind3 x y z = bind (x , y , z)
sbind :: (Alpha t, Rep a) => String -> t -> Bind (Name a) t
sbind x = bind (s2n x)
sbind2 x y = bind2 (s2n x) (s2n y)
sbind3 x y z = bind3 (s2n x) (s2n y) (s2n z)

----------------------------------------------------------------------

vPi :: String -> Value ->  Value -> Value
vPi s x y = VPi x (bind (s2n s) y)

vBind :: String -> (Value -> Value) -> Bind Nom Value
vBind x f = bind (s2n x) (f (var x))

kBind :: Value -> Bind Nom Value
kBind x = bind wildcardR x

rBind :: String -> (Nom -> Value) -> Bind Nom Value
rBind x f = sbind x (f (s2n x))

rBind2 :: String -> String -> (Nom -> Nom -> Value) -> Bind Nom2 Value
rBind2 x y f = sbind2 x y (f (s2n x) (s2n y))

var :: String -> Value
var = vVar . s2n

vVar :: Nom -> Value
vVar nm = VNeut nm Id

vProd :: Value -> Value -> Value
vProd _A _B = VSg _A (bind (s2n wildcard) _B)

vArr :: Value -> Value -> Value
vArr _A _B = VPi _A (bind (s2n wildcard) _B)

eIf :: Value -> Value -> Value -> Elim
eIf _C ct cf = EElimBool (bind (s2n wildcard) _C) ct cf

----------------------------------------------------------------------

rElimUnit :: Bind Nom Value -> Value -> Nom -> Value
rElimUnit _P ptt u = VNeut u (Pipe Id (EElimUnit _P ptt))

rElimBool :: Bind Nom Value -> Value -> Value -> Nom -> Value
rElimBool _P pt pf b = VNeut b (Pipe Id (EElimBool _P pt pf))

rElimPair :: Type -> Bind Nom Type -> Bind Nom Type -> Bind Nom2 Value -> Nom -> Value
rElimPair _A _B _P ppair ab = VNeut ab (Pipe Id (EElimPair _A _B _P ppair))

rElimEq :: Type -> Value -> Bind Nom2 Value -> Value -> Value -> Nom -> Value
rElimEq _A x _P prefl y q = VNeut q (Pipe Id (EElimEq _A x _P prefl y))

rElimEnum :: Bind Nom Value -> Value -> Bind Nom3 Value -> Nom -> Value
rElimEnum _P pnil pcons xs = VNeut xs (Pipe Id (EElimEnum _P pnil pcons))

rElimTel :: Bind Nom Value -> Value -> Bind Nom3 Value -> Nom -> Value
rElimTel _P pemp pext _T = VNeut _T (Pipe Id (EElimTel _P pemp pext))

rElimDesc :: Value -> Bind Nom Value -> Bind Nom Value -> Bind Nom3 Value -> Bind Nom3 Value -> Nom -> Value
rElimDesc _I _P pend prec parg _D = VNeut _D (Pipe Id (EElimDesc _I _P pend prec parg))

rBranches :: Nom -> Bind Nom Value -> Type
rBranches _E _P = VNeut _E (Pipe Id (EBranches _P))

rFunc :: Value -> Nom -> Bind Nom Value -> Value -> Type
rFunc _I _D _X i = VNeut _D (Pipe Id (EFunc _I _X i))

rHyps :: Value -> Nom -> Bind Nom Value -> Bind Nom2 Value -> Value -> Value -> Type
rHyps _I _D _X _M i xs = VNeut _D (Pipe Id (EHyps _I _X _M i xs))

rProve :: Value -> Nom -> Bind Nom Value -> Bind Nom2 Value -> Bind Nom2 Value -> Value -> Value -> Type
rProve _I _D _X _M m i xs = VNeut _D (Pipe Id (EProve _I _X _M m i xs))

rInd :: Value -> Value -> Value -> Value -> Value -> Bind Nom2 Value -> Bind Nom3 Value -> Value -> Nom -> Type
rInd l _P _I _D p _M m i x = VNeut x (Pipe Id (EInd l _P _I _D p _M m i))

rCase :: Value -> (Bind Nom Value) -> Value -> Nom -> Value
rCase _E _P cs t = VNeut t (Pipe Id (ECase _E _P cs))

----------------------------------------------------------------------

vLam :: String -> Value -> Value
vLam s b = VLam (sbind s b)

vEta :: (Value -> Value) -> String -> Value
vEta f s = vLam s (f (var s))

vEta2 :: (Value -> Value -> Value) -> String -> String -> Value
vEta2 f s1 s2 = vLam s1 $ vLam s2 $ f (var s1) (var s2)

vApp :: String -> Value -> Value
vApp = vApp' . s2n

vApp' :: Nom -> Value -> Value
vApp' f x = VNeut f (Pipe Id (EApp x))

vApp2 :: String -> Value -> Value -> Value
vApp2 f x y = VNeut (s2n f) (Pipe (Pipe Id (EApp x)) (EApp y))

vApp3 :: String -> Value -> Value -> Value -> Value
vApp3 f x y z = VNeut (s2n f) (Pipe (Pipe (Pipe Id (EApp x)) (EApp y)) (EApp z))

fbind :: String -> String -> Bind Nom Value
fbind = fbind' . s2n

fbind' :: Nom -> String -> Bind Nom Value
fbind' f x = sbind x $ vApp' f (var x)

fbind2 :: String -> String -> String -> Bind Nom2 Value
fbind2 f x y = sbind2 x y $ vApp2 f (var x) (var y)

fbind3 :: String -> String -> String -> String -> Bind Nom3 Value
fbind3 f x y z = sbind3 x y z $ vApp3 f (var x) (var y) (var z)

vElimUnit :: String -> String -> String -> Value
vElimUnit _P ptt u = rElimUnit (fbind _P "u") (var ptt) (s2n u)

vElimBool :: String -> String -> String -> String -> Value
vElimBool _P pt pf b = rElimBool (fbind _P "b") (var pt) (var pf) (s2n b)

vElimPair :: String -> String -> String -> String -> String -> Value
vElimPair _A _B _P ppair ab = rElimPair
  (var _A)
  (fbind _B "a")
  (fbind _P "xs")
  (fbind2 ppair "a" "b")
  (s2n ab)

vElimEq :: String -> String -> String -> String -> String -> String -> Value
vElimEq _A x _P prefl y q = rElimEq
  (var _A)
  (var x)
  (fbind2 _P "y" "q")
  (var prefl)
  (var y)
  (s2n q)

vElimEnum :: String -> String -> String -> String -> Value
vElimEnum _P pnil pcons xs = rElimEnum
  (fbind _P "xs")
  (var pnil)
  (fbind3 pcons "x" "xs" "pxs")
  (s2n xs)

vElimTel :: String -> String -> String -> String -> Value
vElimTel _P pemp pext _T = rElimTel
  (fbind _P "T")
  (var pemp)
  (fbind3 pext "A" "B" "pb")
  (s2n _T)

vElimDesc :: String -> String -> String -> String -> String -> String -> Value
vElimDesc _I _P pend prec parg _D = rElimDesc
  (var _I)
  (fbind _P "D")
  (fbind pend "i")
  (fbind3 prec "i" "D" "pd")
  (fbind3 parg "A" "B" "pb")
  (s2n _D)

vBranches :: String -> String -> Value
vBranches _E _P = rBranches
  (s2n _E)
  (fbind _P "t")

vFunc :: String -> String -> String -> String -> Value
vFunc _I _D _X i = rFunc
  (var _I)
  (s2n _D)
  (fbind _X "i")
  (var i)

vHyps :: String -> String -> String -> String -> String -> String -> Value
vHyps _I _D _X _M i xs = rHyps
  (var _I)
  (s2n _D)
  (fbind _X "i")
  (fbind2 _M "i" "x")
  (var i)
  (var xs)

vProve :: String -> String -> String -> String -> String -> String -> String -> Value
vProve _I _D _X _M m i xs = rProve
  (var _I)
  (s2n _D)
  (fbind _X "i")
  (fbind2 _M "i" "x")
  (fbind2 m "i" "x")
  (var i)
  (var xs)

vInd :: String -> String -> String -> String -> String -> String -> String -> String -> String -> Value
vInd l _P _I _D p _M m i x = rInd
  (var l)
  (var _P)
  (var _I)
  (var _D)
  (var p)
  (fbind2 _M "i" "x")
  (fbind3 m "i" "xs" "ihs")
  (var i)
  (s2n x)

vCase :: String -> String -> String -> String -> Value
vCase _E _P cs t = rCase
  (var _E)
  (fbind _P "t")
  (var cs)
  (s2n t)

vFix :: String -> String -> String -> String -> String -> String -> Value
vFix l _P _I _D p i = VFix
  (var l)
  (var _P)
  (var _I)
  (var _D)
  (var p)
  (var i)

----------------------------------------------------------------------
