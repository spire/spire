{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  , StandaloneDeriving
  , RankNTypes
  , DeriveFunctor , DeriveFoldable , DeriveTraversable
  #-}

module Spire.Canonical.Types where

import Control.Applicative
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import Data.Traversable
import Data.List (isPrefixOf)
import Prelude.Extras
import Bound

import Spire.Bound
import Spire.Options

----------------------------------------------------------------------

type Type = Value
-- type HNom  = Name (Rebind Nom Value)

-- type NomType = (Nom , Embed Type)

----------------------------------------------------------------------

data Value a =
    VUnit | VBool | VEnum | VTel | VString | VType
  | VTag (Value a) | VDesc (Value a)

  | VPi (Value a) (Bind Nom Value a)
  | VSg  (Value a) (Bind Nom Value a)

  | VFix (Value a) (Value a) (Value a) (Value a) (Value a) (Value a)
  | VEq  (Value a) (Value a) (Value a) (Value a)

  | VTT | VTrue | VFalse | VNil | VRefl | VHere | VEmp
  | VThere (Value a) | VEnd (Value a)

  | VRec (Value a) (Value a) | VInit (Value a)
  | VCons (Value a) (Value a)
  | VPair (Value a) (Value a)

  | VExt (Value a) (Bind Nom Value a)
  | VArg (Value a) (Bind Nom Value a)

  | VLam (Bind Nom Value a)

  | VQuotes String
  | VNeut a (Spine (Elim a))
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Spine a = Id | Pipe (Spine a) a
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

data Elim a =
    EApp (Value a)

  | EFunc (Value a) (Bind Nom Value a) (Value a)
  | EHyps (Value a) (Bind Nom Value a) (Bind Nom2 Value a) (Value a) (Value a)

  | EElimUnit (Bind Nom Value a) (Value a)
  | EElimBool (Bind Nom Value a) (Value a) (Value a)
  | EElimPair (Value a) (Bind Nom Value a) (Bind Nom Value a) (Bind Nom2 Value a)
  | EElimEq (Value a) (Value a) (Bind Nom2 Value a) (Value a) (Value a)
  | EElimEnum (Bind Nom Value a) (Value a) (Bind Nom3 Value a)
  | EElimTel  (Bind Nom Value a) (Value a) (Bind Nom3 Value a)
  | EElimDesc (Value a) (Bind Nom Value a) (Bind Nom Value a) (Bind Nom3 Value a) (Bind Nom3 Value a)

  | EBranches (Bind Nom Value a)
  | ECase (Value a) (Bind Nom Value a) (Value a)
  | EProve (Value a) (Bind Nom Value a) (Bind Nom2 Value a) (Bind Nom2 Value a) (Value a) (Value a)
  | EInd (Value a) (Value a) (Value a) (Value a) (Value a) (Bind Nom2 Value a) (Bind Nom3 Value a) (Value a)
  deriving (Show,Read,Eq,Ord,Functor,Foldable,Traversable)

----------------------------------------------------------------------

instance Eq1   Value
instance Ord1  Value
instance Show1 Value
instance Read1 Value
instance (Functor f , Monad f) => Applicative f where
  pure = return
  (<*>) = ap

----------------------------------------------------------------------

sub :: Bind Nom Value a -> Value a -> Value a
sub = flip instantiate1

sub2 :: Bind Nom2 Value a -> Value a -> Value a -> Value a
sub2 f x y = instantiate2 (x , y) f

sub3 :: Bind Nom3 Value a -> Value a -> Value a -> Value a -> Value a
sub3 f x y z = instantiate3 (x , y , z) f

elims :: Value a -> Spine (Elim a) -> Value a
elims = Data.Foldable.foldl elim

elimB :: Bind b Value a -> Elim a -> Bind b Value a
elimB f g = Scope $ elim (unscope f) (fmap (F . return) g)

subCompose :: Bind b Value a -> (Value a -> Value a) -> Bind b Value a
subCompose b f = b >>>= f . return

vVar :: a -> Value a
vVar a = VNeut a Id

----------------------------------------------------------------------

instance Monad Value where
  return = vVar

  VQuotes str >>= s = VQuotes str

  VUnit >>= s = VUnit
  VBool >>= s = VBool
  VEnum >>= s = VEnum
  VTel >>= s = VTel
  VString >>= s = VString
  VType >>= s = VType

  VTT >>= s = VTT
  VTrue >>= s = VTrue
  VFalse >>= s = VFalse
  VNil >>= s = VNil
  VRefl >>= s = VRefl
  VHere >>= s = VHere
  VEmp >>= s = VEmp

  VTag _E >>= s = VTag (_E >>= s)
  VDesc _I >>= s = VDesc (_I >>= s)
  VThere t >>= s = VThere (t >>= s)
  VEnd i >>= s = VEnd (i >>= s)
  VInit xs >>= s = VInit (xs >>= s)

  VLam b >>= s = VLam (b >>>= s)

  VRec i _D >>= s = VRec (i >>= s) (_D >>= s)
  VCons l _E >>= s = VCons (l >>= s) (_E >>= s)
  VPair a b >>= s = VPair (a >>= s) (b >>= s)

  VPi _A _B >>= s = VPi (_A >>= s) (_B >>>= s)
  VSg _A _B >>= s = VSg (_A >>= s) (_B >>>= s)
  VExt _A _B >>= s = VExt (_A >>= s) (_B >>>= s)
  VArg _A _B >>= s = VArg (_A >>= s) (_B >>>= s)

  VFix l _P _I _D p i >>= s = VFix (l >>= s) (_P >>= s) (_I >>= s) (_D >>= s) (p >>= s) (i >>= s)
  VEq _A a _B b >>= s = VEq (_A >>= s) (a >>= s) (_B >>= s) (b >>= s)

  VNeut nm xs >>= s = elims (s nm) (fmap g xs)
    where
    g e = case e of
      EApp a -> EApp (a >>= s)
      EFunc _I _X i -> EFunc (_I >>= s) (_X >>>= s) (i >>= s)
      EHyps _I _X _M i q -> EHyps (_I >>= s) (_X >>>= s) (_M >>>= s) (i >>= s) (q >>= s)
      
      EElimUnit _P ptt -> EElimUnit (_P >>>= s) (ptt >>= s)
      EElimBool _P pt pf -> EElimBool (_P >>>= s) (pt >>= s) (pf >>= s)
      EElimPair _A _B _P ppair -> EElimPair (_A >>= s) (_B >>>= s) (_P >>>= s) (ppair >>>= s)
      EElimEq _A x _P prefl y -> EElimEq (_A >>= s) (x >>= s) (_P >>>= s) (prefl >>= s) (y >>= s)
      EElimEnum _P pn pc -> EElimEnum (_P >>>= s) (pn >>= s) (pc >>>= s)
      EElimTel _P pemp pext -> EElimTel (_P >>>= s) (pemp >>= s) (pext >>>= s)
      EElimDesc _I _P pend prec parg -> EElimDesc (_I >>= s) (_P >>>= s) (pend >>>= s) (prec >>>= s) (parg >>>= s)

      EBranches _P -> EBranches (_P >>>= s)
      ECase _E _P ccs -> ECase (_E >>= s) (_P >>>= s) (ccs >>= s)
      EProve _I _X _M ih i xs -> EProve (_I >>= s) (_X >>>= s) (_M >>>= s) (ih >>>= s) (i >>= s) (xs >>= s)
      EInd l _P _I _D p _M m i -> EInd (l >>= s) (_P >>= s) (_I >>= s) (_D >>= s) (p >>= s) (_M >>>= s) (m >>>= s) (i >>= s)

----------------------------------------------------------------------

elim :: Value a -> Elim a -> Value a

elim (VNeut nm fs) f        = VNeut nm (Pipe fs f)

elim (VLam f)      (EApp a) = f `sub` a
elim _             (EApp _) = error "Ill-typed evaluation of function application"

elim VTT    (EElimUnit _P ptt)  = ptt
elim _      (EElimUnit _P ptt)  = error "Ill-typed evaluation of elimUnit"

elim VTrue  (EElimBool _P pt _) = pt
elim VFalse (EElimBool _P _ pf) = pf
elim _      (EElimBool _P _  _) = error "Ill-typed evaluation of elimBool"

elim (VPair a b) (EElimPair _A _B _P ppair) = do
  sub2 ppair a b
elim _               (EElimPair _A _B _P ppair)  =
  error "Ill-typed evaluation of elimPair"

elim VRefl (EElimEq _A x _P prefl y) =
  prefl
elim _               (EElimEq _A x _P prefl y)  =
  error "Ill-typed evaluation of elimEq"

elim VNil         (EElimEnum _P pn _)  =
  pn
elim (VCons x xs) (EElimEnum _P pn pc) = let
  ih = xs `elim` EElimEnum _P pn pc
  in sub3 pc x xs ih
elim _            (EElimEnum _P _ _)  =
  error "Ill-typed evaluation of elimEnum"

elim VEmp            (EElimTel _P pemp pext) =
  pemp
elim (VExt _A _B) (EElimTel _P pemp pext) = let
  ih = elimB _B (EElimTel _P pemp pext)
  in sub3 pext _A (VLam _B) (VLam ih)
elim _               (EElimTel _P pemp pext)  =
  error "Ill-typed evaluation of elimTel"

elim (VEnd i)        (EElimDesc _I _P pend prec parg) =
  pend `sub` i
elim (VRec i _D)     (EElimDesc _I _P pend prec parg) = let
  ih = _D `elim` EElimDesc _I _P pend prec parg
  in sub3 prec i _D ih
elim (VArg _A _B) (EElimDesc _I _P pend prec parg) = let
  ih = elimB _B (EElimDesc _I _P pend prec parg)
  in sub3 parg _A (VLam _B) (VLam ih)
elim _            (EElimDesc _I _P pend prec parg)  =
  error "Ill-typed evaluation of elimDesc"

elim (VInit xs) (EInd l _P _I _D p _M m i) = let
  _X = bind1$ \ j -> VFix # l # _P # _I # _D # p #! j
  ih = bind2$ \ j x -> rInd # l # _P # _I # _D # p ## _M ## m #! j #| x
  ihs = _D `elim` EProve _I _X _M ih i xs
  in sub3 m i xs ihs
elim _            (EInd l _P _I _D p _M m i)  =
  error "Ill-typed evaluation of ind"

elim (VEnd j)        (EFunc _I _X i) =
  VEq _I j _I i
elim (VRec j _D)     (EFunc _I _X i) =
  vProd (_X `sub` j) (_D `elim` EFunc _I _X i)
elim (VArg _A _B)    (EFunc _I _X i) =
  VSg _A $ _B `elimB` EFunc _I _X i
elim _               (EFunc _I _X i) =
  error "Ill-typed evaluation of Func"

elim (VEnd j)        (EHyps _I _X _M i q) =
  VUnit
elim (VRec j _D)     (EHyps _I _X _M i xxs) = let
  _A = _X `sub` j
  _B = bind0$ _D `elim` EFunc _I _X i
  _M = bind0$ VType
  ppair = bind2$ \ x xs -> vProd (sub2 ## _M # j #! x) (elim # _D $ EHyps # _I ## _X ## _M # i #! xs)
  in xxs `elim` EElimPair _A _B _M ppair
elim (VArg _A _B)    (EHyps _I _X _M i axs) = let
  _B' = _B `elimB` EFunc _I _X i
  ppair = bind2$ \ a xs -> (sub ## _B #! a) `elim` (EHyps # _I ## _X ## _M # i #! xs)
  in axs `elim` EElimPair _A _B' (bind0 VType) ppair
elim _D               (EHyps _I _X _M i xs) =
  error "Ill-typed evaluation of Hyps"

elim (VEnd j)        (EProve _I _X _M m i q) =
  VTT
elim (VRec j _D)     (EProve _I _X _M m i xxs) = let
  _A = _X `sub` j
  _B = bind0$ _D `elim` EFunc _I _X i
  _M' = bind1$ \xxs -> (VRec # j # _D) `elim` (EHyps # _I ## _X ## _M # i #! xxs)
  ppair = bind2$ \ x xs -> (VPair (sub2 ## m # j #! x) # _D) `elim` (EProve # _I ## _X ## _M ## m # i #! xs)
  in xxs `elim` EElimPair _A _B _M' ppair
elim (VArg _A _B)    (EProve _I _X _M m i axs) = let
  _B' = _B `elimB` EFunc _I _X i
  _M' = bind1$ \ axs' -> (VArg # _A ## _B) `elim` (EHyps # _I ## _X ## _M # i #! axs')
  ppair = bind2$ \ a xs -> (sub ## _B #! a) `elim` (EProve # _I ## _X ## _M ## m # i #! xs)
  in axs `elim` EElimPair _A _B' _M' ppair
elim _               (EProve _I _X _M m i xs) =
  error "Ill-typed evaluation of prove"

elim VNil         (EBranches _P) =
  VUnit
elim (VCons l _E)    (EBranches _P) = let
  _P' = _P `subCompose` VThere
  in vProd (_P `sub` VHere)  (_E `elim` EBranches _P')
elim _             (EBranches _P) =
  error "Ill-typed evaluation of Branches"

elim VHere         (ECase (VCons l _E) _P ccs) = let
  _Pthere = _P `subCompose` VThere
  _A = _P `sub` VHere
  _B = bind0$ _E `elim` EBranches _Pthere
  _M = bind0$ _A
  ppair = bind2$ \ c cs -> id #! c
  in ccs `elim` EElimPair _A _B _M ppair
elim (VThere t)    (ECase (VCons l _E) _P ccs) = let
  _Pthere = _P `subCompose` VThere
  _A = _P `sub` VHere
  _B = bind0$ _E `elim` EBranches _Pthere
  _M = bind0$ _P `sub` (VThere t)
  ppair = bind2$ \ c cs -> elim # t $ ECase # _E ## _Pthere #! cs
  in ccs `elim` EElimPair _A _B _M ppair
elim _             (ECase _E _P ccs) =
  error "Ill-typed evaluation of case"

----------------------------------------------------------------------

data VDef = VDef String (Value String) (Value String)
  deriving (Show,Read,Eq,Ord)

type Env = [VDef]
type VProg = Env

----------------------------------------------------------------------

data SpireR = SpireR { ctx :: () , env :: Env , conf :: Conf }
emptySpireR = SpireR { ctx = ()
                     , env = []
                     , conf = error "You need to define 'conf' before using 'emptySpireR'."
                     }
data SpireS = SpireS { unState :: () }
emptySpireS = SpireS { unState = () }
type SpireM = StateT SpireS (ReaderT SpireR (Either String))

----------------------------------------------------------------------

-- extendCtx :: Nom -> Type -> SpireM a -> SpireM a
-- extendCtx x _A = local
--   (\r -> r { ctx = snocTel (ctx r) (x , Embed _A) })

extendEnv :: String -> Value String -> Type String -> SpireM a -> SpireM a
extendEnv x a _A = local
  (\r -> r { env = VDef x a _A : (env r) })

----------------------------------------------------------------------

wildcard = "_"
-- wildcardR :: Nom
-- wildcardR = s2n wildcard

-- isWildcard :: Nom -> Bool
-- isWildcard nm = name2String nm == wildcard

----------------------------------------------------------------------

-- freshR :: Fresh m => String -> m Nom
-- freshR = fresh . s2n

-- freshMV :: Fresh m => String -> m Nom
-- freshMV suffix = fresh . s2n $ "?" ++ suffix

-- isMV :: Nom -> Bool
-- isMV nm = "?" `isPrefixOf` name2String nm

-- -- Return the non-'?' part of a mvars string.
-- mv2String :: Nom -> String
-- mv2String nm = case name2String nm of
--   '?':suffix -> suffix
--   _          -> error $ "mv2String: not an mvar: " ++ show nm

-- bind2 x y = bind (x , y)
-- bind3 x y z = bind (x , y , z)
-- sbind :: (Alpha t, Rep a) => String -> t -> Bind (Name a) t
-- sbind x = bind (s2n x)
-- sbind2 x y = bind2 (s2n x) (s2n y)
-- sbind3 x y z = bind3 (s2n x) (s2n y) (s2n z)

----------------------------------------------------------------------

vPi :: Eq a => a -> Value a -> Value a -> Value a
vPi s x y = VPi x (abstract1 s y)

vSg :: Eq a => Value a -> (a , Value a) -> Value a
vSg _A (nm , _B) = VSg _A (abstract1 nm _B)

vExt :: Eq a => Value a -> (a , Value a) -> Value a
vExt _A (nm , _B) = VExt _A (abstract1 nm _B)

-- vBind :: String -> (Value -> Value) -> Bind Nom Value
-- vBind x f = bind (s2n x) (f (var x))

-- rBind :: String -> (Nom -> Value) -> Bind Nom Value
-- rBind x f = sbind x (f (s2n x))

-- rBind2 :: String -> String -> (Nom -> Nom -> Value) -> Bind Nom2 Value
-- rBind2 x y f = sbind2 x y (f (s2n x) (s2n y))

-- var :: String -> Value
-- var = vVar . s2n

vProd :: Value a -> Value a -> Value a
vProd _A _B = VSg _A (bind0 _B)

vArr :: Value a -> Value a -> Value a
vArr _A _B = VPi _A (bind0 _B)

-- eIf :: Value -> Value -> Value -> Elim
-- eIf _C ct cf = EElimBool (bind (s2n wildcard) _C) ct cf

-- ----------------------------------------------------------------------

rElimUnit :: Eq a => Bind Nom Value a -> Value a -> a -> Value a
rElimUnit _P ptt u = VNeut u (Pipe Id (EElimUnit _P ptt))

rElimBool :: Eq a => Bind Nom Value a -> Value a -> Value a -> a -> Value a
rElimBool _P pt pf b = VNeut b (Pipe Id (EElimBool _P pt pf))

rElimPair :: Eq a => Type a -> Bind Nom Type a -> Bind Nom Type a -> Bind Nom2 Value a -> a -> Value a
rElimPair _A _B _P ppair ab = VNeut ab (Pipe Id (EElimPair _A _B _P ppair))

rElimEq :: Eq a => Type a -> Value a -> Bind Nom2 Value a -> Value a -> Value a -> a -> Value a
rElimEq _A x _P prefl y q = VNeut q (Pipe Id (EElimEq _A x _P prefl y))

rElimEnum :: Eq a => Bind Nom Value a -> Value a -> Bind Nom3 Value a -> a -> Value a
rElimEnum _P pnil pcons xs = VNeut xs (Pipe Id (EElimEnum _P pnil pcons))

rElimTel :: Eq a => Bind Nom Value a -> Value a -> Bind Nom3 Value a -> a -> Value a
rElimTel _P pemp pext _T = VNeut _T (Pipe Id (EElimTel _P pemp pext))

rElimDesc :: Eq a => Value a -> Bind Nom Value a -> Bind Nom Value a -> Bind Nom3 Value a -> Bind Nom3 Value a -> a -> Value a
rElimDesc _I _P pend prec parg _D = VNeut _D (Pipe Id (EElimDesc _I _P pend prec parg))

rBranches :: Eq a => a -> Bind Nom Value a -> Type a
rBranches _E _P = VNeut _E (Pipe Id (EBranches _P))

rFunc :: Eq a => Value a -> a -> Bind Nom Value a -> Value a -> Type a
rFunc _I _D _X i = VNeut _D (Pipe Id (EFunc _I _X i))

rHyps :: Eq a => Value a -> a -> Bind Nom Value a -> Bind Nom2 Value a -> Value a -> Value a -> Type a
rHyps _I _D _X _M i xs = VNeut _D (Pipe Id (EHyps _I _X _M i xs))

rProve :: Eq a => Value a -> a -> Bind Nom Value a -> Bind Nom2 Value a -> Bind Nom2 Value a -> Value a -> Value a -> Type a
rProve _I _D _X _M m i xs = VNeut _D (Pipe Id (EProve _I _X _M m i xs))

rInd :: Value a -> Value a -> Value a -> Value a -> Value a -> Bind Nom2 Value a -> Bind Nom3 Value a -> Value a -> a -> Type a
rInd l _P _I _D p _M m i x = VNeut x (Pipe Id (EInd l _P _I _D p _M m i))

rCase :: Eq a => Value a -> Bind Nom Value a -> Value a -> a -> Value a
rCase _E _P cs t = VNeut t (Pipe Id (ECase _E _P cs))

----------------------------------------------------------------------

vLam :: Eq a => a -> Value a -> Value a
vLam s b = VLam (abstract1 s b)

-- vEta :: (Value -> Value) -> String -> Value
-- vEta f s = vLam s (f (var s))

-- vEta2 :: (Value -> Value -> Value) -> String -> String -> Value
-- vEta2 f s1 s2 = vLam s1 $ vLam s2 $ f (var s1) (var s2)

vApp :: a -> Value a -> Value a
vApp f x = VNeut f (Pipe Id (EApp x))

vApp2 :: a -> Value a -> Value a -> Value a
vApp2 f x y = VNeut f (Pipe (Pipe Id (EApp x)) (EApp y))

vApp3 :: a -> Value a -> Value a -> Value a -> Value a
vApp3 f x y z = VNeut f (Pipe (Pipe (Pipe Id (EApp x)) (EApp y)) (EApp z))

fbind1 :: a -> a -> (a , Value a)
fbind1 f x = (x , f `vApp` var x)

fbind2 :: a -> a -> a -> (a , a , Value a)
fbind2 f x y = (x , y , vApp2 f (var x) (var y))

fbind3 :: a -> a -> a -> a -> (a , a , a , Value a)
fbind3 f x y z = (x , y , z , vApp3 f (var x) (var y) (var z))

vElimUnit :: Eq a => (a , Value a) -> Value a -> a -> Value a
vElimUnit _P ptt u = rElimUnit (abs1 _P) ptt u

-- vElimBool :: String -> String -> String -> String -> Value
-- vElimBool _P pt pf b = rElimBool (fbind _P "b") (var pt) (var pf) (s2n b)

vElimPair :: Eq a => Value a -> (a , Value a) -> (a , Value a) -> (a , a , Value a) -> a -> Value a
vElimPair _A _B _P ppair ab = rElimPair _A (abs1 _B) (abs1 _P) (abs2 ppair) ab

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
