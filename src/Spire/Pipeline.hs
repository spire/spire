{-# LANGUAGE ImplicitParams #-}
module Spire.Pipeline where
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity

import Spire.Surface.Elaborator
import Spire.Surface.Types
import Spire.Expression.Checker
-- import Spire.Canonical.Checker
import Spire.Expression.Embedder
import Spire.Expression.Types
import Spire.Canonical.Embedder
import Spire.Canonical.Types
import Spire.Canonical.InitialEnv
import Spire.Options

----------------------------------------------------------------------

-- checkInitEnv :: (?conf::Conf) => Either String ()
-- checkInitEnv = runSpireM [] $ recheckCanon (paranoid ?conf) initEnv

elabProgram :: (?conf::Conf) => Env -> SProg -> Either String CProg
elabProgram env = runSpireM env . elabProg

checkProgram :: (?conf::Conf) => Env -> CProg -> Either String VProg
checkProgram env = runSpireM env .
  checkProg

-- checkAndRecheckProg :: Bool -> CProg -> SpireM VProg
-- checkAndRecheckProg paranoid expression  = do
--   canonical <- checkProg expression
--   recheckCanon paranoid canonical
--   return canonical

-- recheckCanon :: Bool -> Env -> SpireM ()
-- recheckCanon paranoid canonical = do
--   when paranoid $ do
--     recheckProg canonical
--     let surface' = runFreshM $ mapM (embedCDef <=< embedVDef) canonical
--     expression'  <- elabProg surface'
--     canonical'   <- checkProg expression'
--     unless (canonical == canonical') $
--       throwError "Embedding is unstable!"

----------------------------------------------------------------------

runSpireM :: (?conf::Conf) => Env -> SpireM a -> Either String a
runSpireM env =
            flip runReaderT (emptySpireR{ conf = ?conf , env = initEnv ++ env })
          . flip evalStateT emptySpireS

----------------------------------------------------------------------
