{-# LANGUAGE ImplicitParams #-}
module Spire.Prelude.Interface where

import System.Directory
import Spire.Debug
import Spire.Options
import Spire.Pipeline
import Spire.Canonical.Types
import Spire.Surface.Parser
import Spire.Surface.PrettyPrinter

----------------------------------------------------------------------

preludePath :: FilePath
preludePath = "/Users/larrytheliquid/src/spire/src/Spire/Prelude/Prelude.spire"

preludeiPath :: FilePath
preludeiPath = preludePath ++ "i"

writePrelude :: IO Env
writePrelude = do
  let ?conf = emptyConf
  case checkInitEnv of
    Left e -> do 
      error "Error in initial environment"
    Right () -> do
      code <- readFile preludePath
      case parseProgram preludePath code of
        Left e -> do
          error "Parse error in Prelude"
        Right p -> do
          case elabProgram [] p of
            Left e -> do
              error "Elaboration error in Prelude"
            Right p' -> do
              case checkProgram [] p' of
                Left e -> error "Type error in Prelude"
                Right p'' -> do
                  writeFile preludeiPath (show p'')
                  return p''

readPrelude :: IO Env
readPrelude = do
  preludeiExists <- doesFileExist preludeiPath
  if preludeiExists
  then return . read =<< readFile preludeiPath
  else writePrelude

----------------------------------------------------------------------