{-# OPTIONS_GHC -O0 #-}
module Spire.Debug (module Spire.Debug , Debug.Trace.trace) where

import Data.IORef
import Debug.Trace
import System.IO.Unsafe

----------------------------------------------------------------------

setDebugging :: Bool -> IO ()
setDebugging = writeIORef debuggingEnabledRef

infix 0 `debug`
debug :: a -> String -> a
debug x msg =
  if getDebugging ()
  then trace msg x
  else x

----------------------------------------------------------------------
-- Notes on 'unsafePermIO' hacks.
--
-- The 'debuggingEnabledRef' is a non-function, so it only gets
-- evaluated once.  This is important, because otherwise we'd allocate
-- a new ref each time and would lose any value set with
-- 'setDebugging'.
--
-- On the other hand, 'getDebugging' is a function, so that it gets
-- reevaluated every time it's called.  This is important, because if
-- 'setDebugging' were called multiple times, only the first value
-- read by 'getDebugging' would ever be returned.
--
-- Well, that's how it's supposed to work, but optimization (ghc -O)
-- makes it much less predictable than that.  Adding
--
--   {-# GHC_OPTIONS -O0 #-}
--
-- to the top of your source file is not sufficient in general; when
-- cabal building the Gundry unification code I needed to disable
-- optimization globally with '--disable-optimization' to get correct
-- output from all 'Debug.Trace.trace' calls. Disabling optimization
-- in the file was enough to make my global references work though.
--
-- See:
-- http://stackoverflow.com/questions/4461684/confusion-over-iorefs-to-make-a-counter
-- http://stackoverflow.com/questions/5920200/how-to-prevent-common-sub-expression-elimination-cse-with-ghc

{-# NOINLINE getDebugging #-}
getDebugging :: () -> Bool
getDebugging _ = unsafePerformIO . readIORef $ debuggingEnabledRef

{-# NOINLINE debuggingEnabledRef #-}
debuggingEnabledRef :: IORef Bool
debuggingEnabledRef = unsafePerformIO . newIORef $ False
