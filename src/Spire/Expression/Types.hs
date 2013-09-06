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
    ITT | ITrue | IFalse

  | IUnit | IBool | IType
  | IPi Check (Bind Nom Check)
  | ISg Check (Bind Nom Check)

  | IVar Nom
  | IProj1 Infer
  | IProj2 Infer
  | IIf Check Infer Infer
  | ICaseBool (Bind Nom Check) Check Check Check
  | IApp Infer Check
  | IAnn Check Check
  deriving Show

$(derive [''Check , ''Infer])
instance Alpha Check
instance Alpha Infer

----------------------------------------------------------------------

data CDef = CDef Nom Check Check
  deriving Show

type CProg = [CDef]

----------------------------------------------------------------------
