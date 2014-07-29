{-# LANGUAGE ImplicitParams #-}
module Spire.CLI where

import Spire.Debug
import Spire.Options
import Spire.Pipeline
import Spire.Surface.Parser
import Spire.Surface.PrettyPrinter

----------------------------------------------------------------------

run :: IO ()
run = runDebug =<< getOpts

-- Version of 'run' that does not use cmdargs.
--
-- The cmdargs package seems to mess up the ghci debugger; 'runDebug'
-- can be used instead of 'run' when debugging. E.g.
--
--   ghci -fbreak-on-error -isrc src/Spire/CLI.hs
--   :trace runDebug (emptyConf { file = "examples/MetaVars.spire" , metavars = True })
runDebug :: Conf -> IO ()
runDebug conf = do
  setDebugging . Spire.Options.debug $ conf
  -- http://www.haskell.org/ghc/docs/latest/html/users_guide/other-type-extensions.html#implicit-parameters
  let ?conf = conf
  checkFromFile (file conf)

----------------------------------------------------------------------

checkFromFile :: (?conf::Conf) => FilePath -> IO ()
checkFromFile file = do
  case checkInitEnv of
    Left error -> do 
      putStrLn "Error in initial environment:"
      putStrLn error
    Right () -> do
      code <- readFile file
      case parseProgram file code of
        Left error -> do
          putStrLn "Parse error:"
          putStrLn $ formatParseError error
      
        Right program -> do
          putStrLn $ "Parsed program:"
          putStrLn ""
          putStrLn $ prettyPrint program
          putStrLn ""
      
          case elabProgram program of
            Left error -> do
              putStrLn "Elaboration error:"
              putStrLn error
      
            Right program -> do
              putStrLn $ "Elaborated program:"
              putStrLn ""
              putStrLn $ prettyPrint program
              putStrLn ""
      
              case checkProgram program of
                Left error -> putStrLn error
                Right program' -> do
                  putStrLn "Well-typed!"
                  putStrLn $ "Evaluated program:"
                  putStrLn ""
                  putStrLn $ prettyPrint program'

----------------------------------------------------------------------

