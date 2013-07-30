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
import Unbound.LocallyNameless

----------------------------------------------------------------------

type Type = Value
type Nom = Name Value
type NomType = (Nom , Embed Type)

data Value =
  {- Types -}
    VUnit | VType
  | VPi Value (Bind Nom Value)
  | VSg Value (Bind Nom Value)

  {- Values -}
  | VTT
  | VPair Value Value Value {- : Type -}
  | VLam Value {- : Type -} (Bind Nom Value)

  | Elim Nom [Elim]
  deriving Show

data Elim =
    EApp Value
  | EProj1
  | EProj2
  deriving Show

$(derive [''Value , ''Elim])
instance Alpha Value
instance Alpha Elim

instance Eq Value where
  (==) = aeq
instance Eq Elim where
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

var :: Nom -> Value
var nm = Elim nm []

----------------------------------------------------------------------
