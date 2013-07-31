{-# LANGUAGE
    MultiParamTypeClasses
  , TemplateHaskell
  , ScopedTypeVariables
  , FlexibleInstances
  , FlexibleContexts
  , UndecidableInstances
  , ViewPatterns
  #-}

module Spire.Canonical.Types where
import Control.Monad.Error
import Control.Monad.Reader
import Unbound.LocallyNameless

----------------------------------------------------------------------

type Type = Value
type Nom = Name Value
type NomType = (Nom , Embed Type)

data Value =
    VUnit | VBool | VType 
  | VPi Value (Bind Nom Value)
  | VSg Value (Bind Nom Value)

  | VTT | VTrue | VFalse
  | VPair Value Value Value {- : Type -}
  | VLam Value {- : Type -} (Bind Nom Value)

  | Elim Nom [Elim]
  deriving Show

data Elim =
    EApp Value
  | EProj1
  | EProj2
  | EIf Value Value
  deriving Show

$(derive [''Value , ''Elim])
instance Alpha Value
instance Alpha Elim

instance Eq Value where
  (==) = aeq
instance Eq Elim where
  (==) = aeq

----------------------------------------------------------------------

data Tel = Empty
  | Extend (Rebind NomType Tel)
  deriving Show

$(derive [''Tel])
instance Alpha Tel

snocTel :: Tel -> NomType -> Tel
snocTel Empty y = Extend (rebind y Empty)
snocTel (Extend (unrebind -> (x , xs))) y = Extend (rebind x (snocTel xs y))

----------------------------------------------------------------------

data ContextR = ContextR { ctx :: Tel }
type SpireM = ReaderT ContextR (ErrorT String FreshM)

-- runReaderT :: ReaderT r m a -> r -> m a
-- runErrorT :: ErrorT e m a -> m (Either e a)
-- runFreshM :: FreshM a -> a

runSpireM :: SpireM a -> Either String a
runSpireM m = runFreshM $ runErrorT $ runReaderT m $ ContextR Empty

----------------------------------------------------------------------

vVar :: Nom -> Value
vVar nm = Elim nm []

----------------------------------------------------------------------
