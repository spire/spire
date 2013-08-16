module Spire.Pipeline where
import Control.Monad.Error
import Control.Monad.Reader
import Unbound.LocallyNameless hiding ( Spine )

import Spire.Surface.Elaborator
import Spire.Expression.Checker
import Spire.Canonical.Checker
import Spire.Canonical.Types
import Spire.Surface.Types

----------------------------------------------------------------------

checkProgram :: SProg -> Either String VProg
checkProgram = runSpireM . checkProgramM

checkProgramM :: SProg -> SpireM VProg
checkProgramM surface = do
  expression  <- elabProg surface
  canonical   <- checkProg expression
  ()          <- recheckProg canonical
  return canonical

----------------------------------------------------------------------

{-
runReaderT :: ReaderT r m a -> r -> m a
runErrorT :: ErrorT e m a -> m (Either e a)
runFreshM :: FreshM a -> a
-}

runSpireM :: SpireM a -> Either String a
runSpireM = runFreshM . runErrorT . runSpireR

runSpireR :: SpireM a -> ErrorT String FreshM a
runSpireR m = runReaderT m emptySpireR

----------------------------------------------------------------------