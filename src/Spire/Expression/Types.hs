{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , GeneralizedNewtypeDeriving
  , GADTs
  #-}

module Spire.Expression.Types where
import Data.Monoid
import Unbound.LocallyNameless
import Spire.Canonical.Types
import qualified Spire.Canonical.Builtins as B

----------------------------------------------------------------------

data Check =
    CLam (Bind Nom Check)
  | CPair Check Check
  | CRefl | CHere
  | CThere Check | CEnd Check
  | CRec Check Check | CInit Check
  | CArg Check (Bind Nom Check)
  | Infer Infer
  deriving Show

data Infer =
    IQuotes String

  | IPi Check (Bind Nom Check)
  | ISg Check (Bind Nom Check)
  | IEq Infer Infer

  | IVar Nom
  | IIf Check Infer Infer
  | IApp Infer Check
  | IAnn Check Check
  deriving Show

$(derive [''Check , ''Infer])
instance Alpha Check
instance Alpha Infer

----------------------------------------------------------------------

-- Here 'CDef f e' evs T' Tvs' corresponds to source program
--
--   f : T
--   f = e
--
-- where 'e' elaborates to 'e'' producing mvar bindings 'evs' and 'T'
-- elaborates to 'T'' producing mvar bindings 'Tvs'.
data CDef = CDef Nom Check Check
  deriving Show

type CProg = [CDef]

----------------------------------------------------------------------

cVar :: String -> Check
cVar = Infer . iVar

iVar :: String -> Infer
iVar = IVar . s2n

iApps :: Infer -> [Check] -> Infer
iApps = foldl IApp

----------------------------------------------------------------------
