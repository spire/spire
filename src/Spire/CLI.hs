module Spire.CLI where
import System.Environment
import Spire.Surface.Parser
import Spire.Surface.PrettyPrinter
import Spire.Pipeline

----------------------------------------------------------------------

run :: IO ()
run = do
  args <- getArgs
  if null args
  then putStrLn "Please enter the name of the file to be checked."
  else checkFromFile (head args)

----------------------------------------------------------------------

checkFromFile :: FilePath -> IO ()
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

