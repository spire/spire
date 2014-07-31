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

import PatternUnify.Context
import Spire.Options

----------------------------------------------------------------------

type Type = Value

type Nom  = Name Value
type Nom2 = (Nom , Nom)
type Nom3 = (Nom , Nom , Nom)
type Nom4 = (Nom , Nom , Nom , Nom)

type NomType = (Nom , Embed Type)

----------------------------------------------------------------------

data Value =
    VUnit | VBool | VString | VType
  | VEnum | VTag Value | VDesc Value

  | VPi  Value (Bind Nom Value)
  | VSg  Value (Bind Nom Value)

  | VFix Value Value Value
  | VEq  Value Value Value Value

  | VTT | VTrue | VFalse | VNil | VRefl | VHere
  | VThere Value | VEnd Value

  | VRec Value Value | VInit Value
  | VCons Value Value
  | VPair Value Value

  | VArg Value (Bind Nom Value)

  | VLam (Bind Nom Value)

  | VQuotes String
  | VNeut Nom Spine
  deriving Show

data Elim =
    EApp Value
  | EProj1 | EProj2

  | EEl Value (Bind Nom Value) Value

  | EElimBool (Bind Nom Value) Value Value
  | EElimEnum (Bind Nom Value) Value (Bind Nom3 Value)

  | ESubst (Bind Nom Value) Value
  | ECase Value (Bind Nom Value) Value
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
type UnifierCtx = [Entry]
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

isWildcard :: Nom -> Bool
isWildcard nm = name2String nm == wildcard

vName :: Nom
vName = s2n "x"

----------------------------------------------------------------------

freshMV :: Fresh m => String -> m Nom
freshMV suffix = fresh . s2n $ "?" ++ suffix

isMV :: Nom -> Bool
isMV nm = "?" `isPrefixOf` name2String nm

-- Return the non-'?' part of a mvars string.
mv2String :: Nom -> String
mv2String nm = case name2String nm of
  '?':suffix -> suffix
  _          -> error $ "mv2String: not an mvar: " ++ show nm

sbind x = bind (s2n x)
sbind3 x y z = bind (s2n x , s2n y , s2n z)

----------------------------------------------------------------------

vPi :: String -> Value ->  Value -> Value
vPi s x y = VPi x (bind (s2n s) y)

vBind :: (Value -> Value) -> Bind Nom Value
vBind f = bind vName (f (vVar vName))

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

rElimBool :: (Bind Nom Value) -> Value -> Value -> Nom -> Value
rElimBool _P pt pf b = VNeut b (Pipe Id (EElimBool _P pt pf))

rElimEnum :: (Bind Nom Value) -> Value -> (Bind Nom3 Value) -> Nom -> Value
rElimEnum _P pnil pcons xs = VNeut xs (Pipe Id (EElimEnum _P pnil pcons))

rBranches :: Nom -> Type -> Type
rBranches _E _P = VNeut _E (Pipe (Pipe Id (EElimEnum
  (sbind "E" (vPi "P" (VTag (var "E") `vArr` VType) VType))
  (vLam "P" VUnit)
  (sbind3 "l" "E" "ih" $ vLam "P" $
    vApp "P" VHere `vProd` vApp "ih" (vLam "t" ("P" `vApp` VThere (var "t")))
  )
  )) (EApp _P))

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
vApp f x = VNeut (s2n f) (Pipe Id (EApp x))

vApp2 :: String -> Value -> Value -> Value
vApp2 f x y = VNeut (s2n f) (Pipe (Pipe Id (EApp x)) (EApp y))

vApp3 :: String -> Value -> Value -> Value -> Value
vApp3 f x y z = VNeut (s2n f) (Pipe (Pipe (Pipe Id (EApp x)) (EApp y)) (EApp z))

fbind :: String -> String -> Bind Nom Value
fbind f x = sbind x $ vApp f (var x)

fbind3 :: String -> String -> String -> String -> Bind Nom3 Value
fbind3 f x y z = sbind3 x y z $ vApp3 f (var x) (var y) (var z)

vElimBool :: String -> String -> String -> String -> Value
vElimBool _P pt pf b = rElimBool (fbind _P "b") (var pt) (var pf) (s2n b)

vElimEnum :: String -> String -> String -> String -> Value
vElimEnum _P pnil pcons xs = rElimEnum
  (fbind _P "xs")
  (var pnil)
  (fbind3 pcons "x" "xs" "pxs")
  (s2n xs)

vCase :: String -> String -> String -> String -> Value
vCase _E _P cs t = rCase
  (var _E)
  (fbind _P "t")
  (var cs)
  (s2n t)

----------------------------------------------------------------------
