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
import qualified Spire.Canonical.Builtins as B
import Unbound.LocallyNameless

----------------------------------------------------------------------

data Syntax =
    SRefl | SHere
  | SQuotes String
  | SThere Syntax | SEnd Syntax
  | SRec Syntax Syntax | SInit Syntax
  | SArg Syntax (Bind Nom Syntax)
  | SPair Syntax Syntax
  | SLam (Bind Nom Syntax)

  | SPi Syntax (Bind Nom Syntax)
  | SSg Syntax (Bind Nom Syntax)
  | SEq Syntax Syntax

  | SWildCard

  | SVar Nom
  | SApp Syntax Syntax
  | SIf Syntax Syntax Syntax
  | SAnn Syntax Syntax
 deriving Show

$(derive [''Syntax])
instance Alpha Syntax

----------------------------------------------------------------------

data SDecl =
    SDef Nom Syntax Syntax
  | SData String [(String , Syntax)] Syntax [(String , Syntax)]
  deriving Show

type SProg = [SDecl]

----------------------------------------------------------------------

sDef :: String -> Syntax -> Syntax -> SDecl
sDef nm = SDef (s2n nm)

sVar :: String -> Syntax
sVar = SVar . s2n

sString :: Syntax
sString = sVar B._String

sEnum :: Syntax
sEnum = sVar B._Enum

sTel :: Syntax
sTel = sVar B._Tel

sEmp :: Syntax
sEmp = sVar B._Emp

sExt :: Syntax -> Syntax -> Syntax
sExt _A _B = SApp (SApp (sVar B._Ext) _A) _B

sNil :: Syntax
sNil = sVar B.nil

sCons :: Syntax -> Syntax -> Syntax
sCons x xs = SApp (SApp (sVar B.cons) x) xs

sLam :: String -> Syntax -> Syntax
sLam nm x = SLam $ bind (s2n nm) x

sPi :: Syntax -> String -> Syntax -> Syntax
sPi x nm y = SPi x $ bind (s2n nm) y

sSg :: Syntax -> String -> Syntax -> Syntax
sSg x nm y = SSg x $ bind (s2n nm) y

----------------------------------------------------------------------
