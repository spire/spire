{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Expression.Types where
import Unbound.LocallyNameless
import Spire.Canonical.Types

----------------------------------------------------------------------

data Check =
    CLam (Bind Nom Check)
  | CPair Check Check
  | Infer Infer
  deriving Show

data Infer =
    ITT
  | IUnit | IType
  | IPi Check (Bind Nom Check)
  | ISg Check (Bind Nom Check)

  | IVar Nom
  | IProj1 Infer
  | IProj2 Infer
  | IApp Infer Check
  | IAnn Check Check
  deriving Show

$(derive [''Check , ''Infer])
instance Alpha Check
instance Alpha Infer

----------------------------------------------------------------------