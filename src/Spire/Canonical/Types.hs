{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  #-}

module Spire.Canonical.Types where
import Control.Monad.Error
import Control.Monad.Reader
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

data Spine = Id | Pipe Spine Elim
  deriving Show

$(derive [''Value , ''Elim , ''Spine])
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

data Tel = Empty
  | Extend (Rebind NomType Tel)
  deriving Show

$(derive [''Tel])
instance Alpha Tel

snocTel :: Tel -> NomType -> Tel
snocTel Empty y = Extend (rebind y Empty)
snocTel (Extend (unrebind -> (x , xs))) y = Extend (rebind x (snocTel xs y))

----------------------------------------------------------------------

data VDef = VDef Nom Value Value
  deriving (Show , Eq)

type Env = [VDef]
type VProg = Env

----------------------------------------------------------------------

data SpireR = SpireR { ctx :: Tel , env :: Env }
emptySpireR = SpireR { ctx = Empty , env = [] }
type SpireM = ReaderT SpireR (ErrorT String FreshM)

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

vVar :: Nom -> Value
vVar nm = VNeut nm Id

eIf :: Value -> Value -> Value -> Elim
eIf _C ct cf = ECaseBool (bind (s2n wildcard) _C) ct cf

----------------------------------------------------------------------
