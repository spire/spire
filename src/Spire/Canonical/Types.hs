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
import Data.List
import Control.Monad.Error
import Control.Monad.Reader
import Unbound.LocallyNameless hiding ( Spine )

----------------------------------------------------------------------

type Type = Value
type Nom = Name Value
-- A decorated name. Any names in the decoration should not be bound,
-- so we Embed them.
type DecNom t = (Nom, Embed t)
type NomType = DecNom Type
-- A meta variable binder is a new-type so that we can hand code the
-- alpha instance to disequate all terms with meta variable binders.
newtype BindMeta a = BindMeta (Bind (DecNom (a, Maybe a)) a)
  deriving Show

data Value =
    VUnit | VBool | VType 
  | VPi Value (Bind Nom Value)
  | VSg Value (Bind Nom Value)

  | VTT | VTrue | VFalse
  | VPair Value Value
  | VLam (Bind Nom Value)

  | VBindMeta (BindMeta Value)

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

$(derive [''Value , ''Elim , ''Spine, ''BindMeta])
instance Alpha Value
instance Alpha Elim
instance Alpha Spine
-- Meta variable binders are existential quantifiers, so
-- alpha-equality does not necessarily make sense for them.
-- E.g. should
--
--   ?x:Nat.x =alpha= ?x:Nat.x
--
-- be true or false?  Note that they are equal for some choices of 'x'
-- and unequal for others. We choose to always make them unequal.
instance Alpha a => Alpha (BindMeta a) where
  aeq' _ _ _ = False

instance Eq Value where
  (==) = aeq
instance Eq Elim where
  (==) = aeq
instance Eq Spine where
  (==) = aeq
instance Alpha a => Eq (BindMeta a) where
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
isWildcard nm = isPrefixOf wildcard (name2String nm)

----------------------------------------------------------------------

vVar :: Nom -> Value
vVar nm = VNeut nm Id

eIf :: Value -> Value -> Value -> Elim
eIf _C ct cf = ECaseBool (bind (s2n wildcard) _C) ct cf

----------------------------------------------------------------------
