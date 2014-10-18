{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  #-}

module Spire.Surface.Types where
import qualified Spire.Canonical.Builtins as B

----------------------------------------------------------------------

type Ident = String

data Syntax =
    SRefl | SHere
  | SQuotes Ident
  | SThere Syntax | SEnd Syntax
  | SRec Syntax Syntax | SInit Syntax
  | SArg Ident Syntax Syntax
  | SPair Syntax Syntax
  | SLam Ident Syntax

  | SPi Ident Syntax Syntax
  | SSg Ident Syntax Syntax
  | SEq Syntax Syntax

  | SWildCard

  | SVar Ident
  | SApp Syntax Syntax
  | SIf Syntax Syntax Syntax
  | SAnn Syntax Syntax
 deriving (Show,Read,Eq,Ord)

----------------------------------------------------------------------

data Stmt =
    SDef String Syntax Syntax
  | SData String [(String , Syntax)] [(String , Syntax)] [(String , [Constr])]
  deriving (Show,Read,Eq,Ord)

data Constr = Fix [Syntax] | Arg String Syntax
  deriving (Show,Read,Eq,Ord)

type Stmts = [Stmt]
type SProg = Stmts

----------------------------------------------------------------------

wildcard = "_"

isWildcard :: String -> Bool
isWildcard nm = nm == wildcard

----------------------------------------------------------------------

sApps :: Syntax -> [Syntax] -> Syntax
sApps = foldl SApp

sTT :: Syntax
sTT = SVar B.tt

sString :: Syntax
sString = SVar B._String

sType :: Syntax
sType = SVar B._Type

sEnum :: Syntax
sEnum = SVar B._Enum

sTel :: Syntax
sTel = SVar B._Tel

sEmp :: Syntax
sEmp = SVar B._Emp

sExt :: Syntax -> Syntax -> Syntax
sExt _A _B = SApp (SApp (SVar B._Ext) _A) _B

sNil :: Syntax
sNil = SVar B.nil

sCons :: Syntax -> Syntax -> Syntax
sCons x xs = SApp (SApp (SVar B.cons) x) xs

----------------------------------------------------------------------

_Indices :: String -> Syntax
_Indices nm = SApp (SVar "Indices") $ SVar (nm ++ "P")

indices :: String -> Syntax -> Syntax
indices nm _I = sApps (SVar "indices") [SVar (nm ++ "P") , _I]

_Constrs :: String -> Syntax
_Constrs nm = sApps (SVar "Constrs") $
  [SVar (nm ++ "E") , SVar (nm ++ "P") , SVar (nm ++ "I")]

constrs :: String -> Syntax -> Syntax
constrs nm cs = sApps (SVar "constrs") $
  [SVar (nm ++ "E") , SVar (nm ++ "P") , SVar (nm ++ "I") , cs]

_Former :: String -> Syntax
_Former nm = sApps (SVar "Former") $
  [SVar (nm ++ "P") , SVar (nm ++ "I")]

nepic :: String -> String -> Syntax
nepic nm _N = sApps (SVar nm) $
  [SVar (_N ++ "N") , SVar (_N ++ "E") , SVar (_N ++ "P") ,
   SVar (_N ++ "I") , SVar (_N ++ "C")]

----------------------------------------------------------------------
