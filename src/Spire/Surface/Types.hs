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
    STT | STrue | SFalse | SNil | SRefl | SHere
  | SQuotes String
  | SThere Syntax | SEnd Syntax
  | SRec Syntax Syntax | SInit Syntax Syntax
  | SArg Syntax (Bind Nom Syntax)
  | SCons Syntax Syntax
  | SPair Syntax Syntax
  | SLam (Bind Nom Syntax)

  | SUnit | SBool | SString | SType
  | SList Syntax | STag Syntax | SDesc Syntax
  | SPi Syntax (Bind Nom Syntax)
  | SSg Syntax (Bind Nom Syntax)
  | SBranches Syntax (Bind Nom Syntax)
  | SEl Syntax (Bind Nom Syntax) Syntax
  | SFix Syntax Syntax Syntax
  | SEq Syntax Syntax

  | SWildCard

  | SVar Nom
  | SProj1 Syntax
  | SProj2 Syntax
  | SApp Syntax Syntax
  | SIf Syntax Syntax Syntax
  | SElimBool (Bind Nom Syntax) Syntax Syntax Syntax
  | SElimList (Bind Nom Syntax) Syntax (Bind (Nom , Nom , Nom) Syntax) Syntax
  | SCase (Bind Nom Syntax) Syntax Syntax
  | SSubst (Bind Nom Syntax) Syntax Syntax
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
sVar = SVar . s2n

sLam :: String -> Syntax -> Syntax
sLam nm x = SLam $ bind (s2n nm) x

sPi :: Syntax -> String -> Syntax -> Syntax
sPi x nm y = SPi x $ bind (s2n nm) y

sSg :: Syntax -> String -> Syntax -> Syntax
sSg x nm y = SSg x $ bind (s2n nm) y

----------------------------------------------------------------------
