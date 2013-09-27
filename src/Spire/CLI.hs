{-# LANGUAGE ImplicitParams #-}
module Spire.CLI where

import Spire.Options
import Spire.Pipeline
import Spire.Surface.Parser
import Spire.Surface.PrettyPrinter

----------------------------------------------------------------------

run :: IO ()
run = do
  conf <- getOpts
  -- http://www.haskell.org/ghc/docs/latest/html/users_guide/other-type-extensions.html#implicit-parameters
  let ?conf = conf
  checkFromFile (file conf)

----------------------------------------------------------------------

checkFromFile :: (?conf::Conf) => FilePath -> IO ()
checkFromFile file = do
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

