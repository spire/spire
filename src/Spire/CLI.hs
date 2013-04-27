module Spire.CLI where
import Control.Monad.Error
import System.Environment
import Text.Printf
import Spire.Surface.Types
import Spire.Surface.Parsing
import Spire.Surface.Elaborating
import Spire.Surface.PrettyPrinting
import Spire.Expression.CheckingAndEvaluation
import Spire.Canonical.Types

run :: IO ()
run = do
  args <- getArgs
  if null args
  then putStrLn "Please enter the name of the file to be checked."
  else checkFromFile (head args)

checkFromFile :: FilePath -> IO ()
checkFromFile file = do
  source <- readFile file
  case parseProgram file source of
    Left error -> do
      putStrLn "Parse error:"
      putStrLn $ formatParseError error

    Right program -> do
      putStrLn $ "Parsed program:"
      forM_ program $ \(SDef l a aT) -> do
        putStrLn ""
        putStrLn $ l ++ " : " ++ prettyPrint aT
        putStrLn $ l ++ " = " ++ prettyPrint a
      putStrLn ""

      case elabS program of
        Left error -> putStrLn error
        Right program' -> case checkDefsStable program' of

          Left error -> putStrLn error
          Right program'' -> do
            putStrLn "Well-typed!"
            putStrLn $ "Evaluated program:\n"
            forM_ program'' $ \(l , a , aT) -> do
              putStrLn $ l ++ " : " ++ prettyPrint aT
              putStrLn $ l ++ " = " ++ prettyPrint a
              putStrLn ""
