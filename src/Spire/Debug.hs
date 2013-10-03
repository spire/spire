module Spire.Debug where

import Data.IORef
import Debug.Trace
import System.IO.Unsafe

----------------------------------------------------------------------

setDebugging :: Bool -> IO ()
setDebugging = writeIORef debuggingEnabledRef

infix 0 `debug`
debug :: a -> String -> a
debug x msg =
  if getDebugging
  then trace msg x
  else x

----------------------------------------------------------------------

{-# NOINLINE getDebugging #-}
getDebugging :: Bool
getDebugging = unsafePerformIO . readIORef $ debuggingEnabledRef

{-# NOINLINE debuggingEnabledRef #-}
debuggingEnabledRef :: IORef Bool
debuggingEnabledRef = unsafePerformIO . newIORef $ False
