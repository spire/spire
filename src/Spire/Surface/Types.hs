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

data Stmt =
    SDef Nom Syntax Syntax
  | SData String [(String , Syntax)] [(String , Syntax)] [(String , [Constr])]
  deriving Show

data Constr = Fix [Syntax] | Arg String Syntax
  deriving Show

type Stmts = [Stmt]
type SProg = Stmts

----------------------------------------------------------------------

sDef :: String -> Syntax -> Syntax -> Stmt
sDef nm = SDef (s2n nm)

sApps :: Syntax -> [Syntax] -> Syntax
sApps = foldl SApp

sVar :: String -> Syntax
sVar = SVar . s2n

sTT :: Syntax
sTT = sVar B.tt

sString :: Syntax
sString = sVar B._String

sType :: Syntax
sType = sVar B._Type

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

_Indices :: String -> Syntax
_Indices nm = SApp (sVar "Indices") $ sVar (nm ++ "P")

indices :: String -> Syntax -> Syntax
indices nm _I = sApps (sVar "indices") [sVar (nm ++ "P") , _I]

_Constrs :: String -> Syntax
_Constrs nm = sApps (sVar "Constrs") $
  [sVar (nm ++ "E") , sVar (nm ++ "P") , sVar (nm ++ "I")]

constrs :: String -> Syntax -> Syntax
constrs nm cs = sApps (sVar "constrs") $
  [sVar (nm ++ "E") , sVar (nm ++ "P") , sVar (nm ++ "I") , cs]

----------------------------------------------------------------------
