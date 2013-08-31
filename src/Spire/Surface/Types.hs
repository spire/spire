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
    STT | STrue | SFalse
  | SPair Syntax Syntax
  | SLam (Bind Nom Syntax)

  | SUnit | SBool | SType
  | SPi Syntax (Bind Nom Syntax)
  | SSg Syntax (Bind Nom Syntax)

  | SBindMeta (BindMeta Syntax)
  | SWildCard

  | SVar Nom
  | SProj1 Syntax
  | SProj2 Syntax
  | SApp Syntax Syntax
  | SIf Syntax Syntax Syntax
  | SCaseBool (Bind Nom Syntax) Syntax Syntax Syntax
  | SAnn Syntax Syntax
 deriving Show

$(derive [''Syntax])
instance Alpha Syntax

----------------------------------------------------------------------

data SDef = SDef Nom Syntax Syntax
  deriving Show

type SProg = [SDef]

----------------------------------------------------------------------

sVar :: String -> Syntax
sVar nm = SVar (s2n nm)

sLam :: String -> Syntax -> Syntax
sLam nm x = SLam $ bind (s2n nm) x

sBindMeta :: String -> Syntax -> Maybe Syntax -> Syntax -> Syntax
sBindMeta nm _T mt e = SBindMeta $ bindMeta (s2n nm) _T mt e

sPi :: Syntax -> String -> Syntax -> Syntax
sPi x nm y = SPi x $ bind (s2n nm) y

sSg :: Syntax -> String -> Syntax -> Syntax
sSg x nm y = SSg x $ bind (s2n nm) y

----------------------------------------------------------------------
