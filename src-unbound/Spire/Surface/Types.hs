{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Surface.Types where
import Spire.Canonical.Types
import Unbound.LocallyNameless

----------------------------------------------------------------------

data Syntax =
    STT
  | SPair Syntax Syntax
  | SLam (Bind Nom Syntax)
  | SUnit | SBool | SType
  | SPi Syntax (Bind Nom Syntax)
  | SSg Syntax (Bind Nom Syntax)

  | SVar Nom
  | SProj1 Syntax
  | SProj2 Syntax
  | SApp Syntax Syntax
  | SAnn Syntax Syntax
 deriving Show

$(derive [''Syntax])
instance Alpha Syntax

----------------------------------------------------------------------

wildcard = "_"

sVar :: String -> Syntax
sVar nm = SVar (s2n nm)

sLam :: String -> Syntax -> Syntax
sLam nm x = SLam $ bind (s2n nm) x

sPi :: Syntax -> String -> Syntax -> Syntax
sPi x nm y = SPi x $ bind (s2n nm) y

sSg :: Syntax -> String -> Syntax -> Syntax
sSg x nm y = SSg x $ bind (s2n nm) y

----------------------------------------------------------------------