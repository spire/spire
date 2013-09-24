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
import PatternUnify.Context
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import Data.Traversable
import Data.List (isPrefixOf)
import Unbound.LocallyNameless hiding ( Spine )

----------------------------------------------------------------------

type Type = Value
type Nom = Name Value
type NomType = (Nom , Embed Type)

data Value =
    VUnit | VBool | VType 
  | VPi Value (Bind Nom Value)
  | VSg Value (Bind Nom Value)

  | VTT | VTrue | VFalse
  | VPair Value Value
  | VLam (Bind Nom Value)

  | VNeut Nom Spine
  deriving Show

data Elim =
    EApp Value
  | EProj1
  | EProj2
  | ECaseBool (Bind Nom Value) Value Value
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

data SpireR = SpireR { ctx :: Tel , env :: Env }
emptySpireR = SpireR { ctx = Empty , env = [] }
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

----------------------------------------------------------------------

freshMV :: Fresh m => m Nom
freshMV = fresh . s2n $ "?"

isMV :: Nom -> Bool
isMV nm = "?" `isPrefixOf` name2String nm

----------------------------------------------------------------------

vVar :: Nom -> Value
vVar nm = VNeut nm Id

eIf :: Value -> Value -> Value -> Elim
eIf _C ct cf = ECaseBool (bind (s2n wildcard) _C) ct cf

----------------------------------------------------------------------
