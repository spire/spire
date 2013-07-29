{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Canonical.Types where
import Unbound.LocallyNameless hiding ( Subst , subst, substs )

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

----------------------------------------------------------------------

type Nom = Name Value
type Type = Value

data Value =
  {- Types -}
    VUnit | VType
  | VPi Value (Bind Nom Value)
  | VSg Value (Bind Nom Value)

  {- Values -}
  | VTT
  | VPair Value Value Value {- : Type -}
  | VLam Value {- : Type -} (Bind Nom Value)

  | VElim Nom [Elim]
  deriving Show

data Elim =
    EApp Value
  | EProj1
  | EProj2
  deriving Show

$(derive [''Value , ''Elim])
instance Alpha Value
instance Alpha Elim

----------------------------------------------------------------------

var :: String -> Value
var nm = VElim (s2n nm) []

lam :: String -> Type -> Value -> Value
lam nm _A b = VLam _A $ bind (s2n nm) b

----------------------------------------------------------------------
