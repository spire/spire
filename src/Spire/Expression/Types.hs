{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , GeneralizedNewtypeDeriving
  #-}

module Spire.Expression.Types where
import Data.Monoid
import Unbound.LocallyNameless
import Spire.Canonical.Types

----------------------------------------------------------------------

data Check =
    CLam (Bind Nom Check)
  | CPair Check Check
  | CNil
  | CCons Check Check
  | Infer Infer
  deriving Show

data Infer =
    ITT | ITrue | IFalse
  | IQuotes String

  | IUnit | IBool | IString | IType
  | IList Check
  | IPi Check (Bind Nom Check)
  | ISg Check (Bind Nom Check)

  | IVar Nom
  | IProj1 Infer
  | IProj2 Infer
  | IIf Check Infer Infer
  | IElimBool (Bind Nom Check) Check Check Check
  | IElimList (Bind Nom Check) Check (Bind (Nom , Nom , Nom) Check) Infer
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
data CDef = CDef Nom Check MVarDecls Check MVarDecls
  deriving Show

-- The 'MVarDecls' are delayed mvar declarations that change that
-- unification state.  We scope mvars to the decl that generated them,
-- so we don't run these declarations during elaboration, but rather
-- during elaboration of the associated def.
newtype MVarDecls = MkMVarDecls { unMVarDecls :: [SpireM ()] }
  deriving Monoid
instance Show MVarDecls where
  show _ = "<mvar decls>"

type CProg = [CDef]

----------------------------------------------------------------------
