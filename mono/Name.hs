{-# LANGUAGE TypeSynonymInstances
           , FlexibleInstances
           , FlexibleContexts
           , GeneralizedNewtypeDeriving
           , OverlappingInstances
           , MultiParamTypeClasses
           , UndecidableInstances
  #-}

module Name where

import Data.Set (Set)
import qualified Data.Set as S

import Data.Monoid

import Control.Monad.Reader
import qualified Control.Monad.State as St
import Control.Monad.Identity
import Control.Applicative (Applicative)

import Control.Monad.Trans.Cont
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.List
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State.Lazy as Lazy
import Control.Monad.Trans.State.Strict as Strict
import Control.Monad.Trans.Writer.Lazy as Lazy
import Control.Monad.Trans.Writer.Strict as Strict

import qualified Control.Monad.Cont.Class as CC
import qualified Control.Monad.Error.Class as EC
import qualified Control.Monad.State.Class as StC
import qualified Control.Monad.Reader.Class as RC
import qualified Control.Monad.Writer.Class as WC

----------------------------------------------------------------------

data Name a = Fr String Integer | Bn Integer
  deriving (Show,Read,Eq,Ord)

class Monad m => Fresh m where
  fresh :: Name a -> m (Name a)

newtype FreshMT m a = FreshMT { unFreshMT :: St.StateT Integer m a }
  deriving (Functor, Applicative, Monad, MonadPlus, MonadIO, MonadFix)

-- | Run a 'FreshMT' computation (with the global index starting at zero).
runFreshMT :: Monad m => FreshMT m a -> m a
runFreshMT m = contFreshMT m 0

-- | Run a 'FreshMT' computation given a starting index for fresh name
--   generation.
contFreshMT :: Monad m => FreshMT m a -> Integer -> m a
contFreshMT (FreshMT m) = St.evalStateT m

instance Monad m => Fresh (FreshMT m) where
  fresh (Fr s _) = FreshMT $ do
    n <- St.get
    St.put (n+1)
    return $ Fr s n

  fresh (Bn {}) = error "fresh encountered bound name! Please report this as a bug."

type FreshM = FreshMT Identity

runFreshM :: FreshM a -> a
runFreshM = runIdentity . runFreshMT

-- | Run a FreshM computation given a starting index.
contFreshM :: FreshM a -> Integer -> a
contFreshM m = runIdentity . contFreshMT m

----------------------------------------------------------------------

instance Fresh m => Fresh (ContT r m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ExceptT e m) where
  fresh = lift . fresh

instance Fresh m => Fresh (IdentityT m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ListT m) where
  fresh = lift . fresh

instance Fresh m => Fresh (MaybeT m) where
  fresh = lift . fresh

instance Fresh m => Fresh (ReaderT r m) where
  fresh = lift . fresh

instance Fresh m => Fresh (Lazy.StateT s m) where
  fresh = lift . fresh

instance Fresh m => Fresh (Strict.StateT s m) where
  fresh = lift . fresh

instance (Monoid w, Fresh m) => Fresh (Lazy.WriterT w m) where
  fresh = lift . fresh

instance (Monoid w, Fresh m) => Fresh (Strict.WriterT w m) where
  fresh = lift . fresh

instance MonadTrans FreshMT where
  lift = FreshMT . lift

instance CC.MonadCont m => CC.MonadCont (FreshMT m) where
  callCC c = FreshMT $ CC.callCC (unFreshMT . (\k -> c (FreshMT . k)))

instance EC.MonadError e m => EC.MonadError e (FreshMT m) where
  throwError = lift . EC.throwError
  catchError m h = FreshMT $ EC.catchError (unFreshMT m) (unFreshMT . h)

instance StC.MonadState s m => StC.MonadState s (FreshMT m) where
  get = lift StC.get
  put = lift . StC.put

instance RC.MonadReader r m => RC.MonadReader r (FreshMT m) where
  ask   = lift RC.ask
  local f = FreshMT . RC.local f . unFreshMT

instance WC.MonadWriter w m => WC.MonadWriter w (FreshMT m) where
  tell   = lift . WC.tell
  listen = FreshMT . WC.listen . unFreshMT
  pass   = FreshMT . WC.pass . unFreshMT

----------------------------------------------------------------------
