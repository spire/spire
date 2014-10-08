{-# LANGUAGE
    DeriveFunctor
  #-}

module Spire.Expression.Types where
import Prelude.Extras
import Bound.Scope.Simple

import Spire.Bound hiding ( Bind )
import Spire.Canonical.Types

type Bind = Scope

----------------------------------------------------------------------

data Check a
  = CLam (Bind Nom Check a)
  | CPair (Check a) (Check a)
  | CRefl a | CHere a
  | CThere (Check a) | CEnd (Check a)
  | CRec (Check a) (Check a) | CInit (Check a)
  | CArg (Check a) (Bind Nom Check a)
  | Infer (Infer a)
  deriving (Show,Read,Eq,Ord,Functor)

data Infer a
  = IQuotes String
  | IVar a

  | IPi (Check a) (Bind Nom Check a)
  | ISg (Check a) (Bind Nom Check a)
  | IEq (Infer a) (Infer a)

  | IIf (Check a) (Infer a) (Infer a)
  | IApp (Infer a) (Check a)
  | IAnn (Check a) (Check a)
  deriving (Show,Read,Eq,Ord,Functor)

----------------------------------------------------------------------

instance Eq1   Check
instance Ord1  Check
instance Show1 Check
instance Read1 Check

----------------------------------------------------------------------

data CDef = CDef String (Check String) (Check String)
  deriving (Show,Read,Eq,Ord)

type CProg = [CDef]

----------------------------------------------------------------------

cVar :: a -> Check a
cVar = Infer . IVar

iApps :: Infer a -> [Check a] -> Infer a
iApps = foldl IApp

----------------------------------------------------------------------
