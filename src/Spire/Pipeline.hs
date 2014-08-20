{-# LANGUAGE ImplicitParams #-}
module Spire.Pipeline (checkInitEnv , elabProgram , checkProgram) where
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Unbound.LocallyNameless hiding ( Spine )

import Spire.Surface.Elaborator
import Spire.Surface.Types
import Spire.Expression.Checker
import Spire.Canonical.Checker
import Spire.Expression.Embedder
import Spire.Expression.Types
import Spire.Canonical.Embedder
import Spire.Canonical.Types
import Spire.Canonical.InitialEnv
import Spire.Options

----------------------------------------------------------------------

checkInitEnv :: (?conf::Conf) => Either String ()
checkInitEnv = runSpireM [] $ checkCanonM initEnv

elabProgram :: (?conf::Conf) => Env -> SProg -> Either String CProg
elabProgram env = runSpireM env . elabProg

checkProgram :: (?conf::Conf) => Env -> CProg -> Either String VProg
checkProgram env = runSpireM env . checkProgramM

checkProgramM :: CProg -> SpireM VProg
checkProgramM expression  = do
  canonical <- checkProg expression
  checkCanonM canonical
  return canonical

checkCanonM :: Env -> SpireM ()
checkCanonM canonical = do
  recheckProg canonical
  let surface' = runFreshM $ mapM (embedCDef <=< embedVDef) canonical
  expression'  <- elabProg surface'
  canonical'   <- checkProg expression'
  unless (canonical == canonical') $
    throwError "Embedding is unstable!"

----------------------------------------------------------------------

{-
runReaderT :: ReaderT r m a -> r -> m a
runExceptT :: ExceptT e m a -> m (Either e a)
runFreshM :: FreshM a -> a
-}

runSpireM :: (?conf::Conf) => Env -> SpireM a -> Either String a
runSpireM env = runFreshM 
          . runExceptT
          . flip runReaderT (emptySpireR{ conf = ?conf , env = initEnv ++ env })
          . flip evalStateT emptySpireS

----------------------------------------------------------------------
