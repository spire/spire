module Spire.CLI where
import Control.Monad.Error
import System.Environment
import Spire.Canonical.Types
import Spire.Surface.Types
import Spire.Surface.Parser
import Spire.Surface.Elaborator
import Spire.Expression.Checker
import Data.List

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
      putStrLn $ showProg program
      putStrLn ""

      case checkProgram program of
        Left error -> putStrLn error
        Right program' -> do
          putStrLn "Well-typed!"
          putStrLn $ "Evaluated program:"
          putStrLn ""
          putStrLn $ showProg program'

showProg :: Show a => [a] -> String
showProg xs = concat $ intersperse "\n" (map show xs) 

----------------------------------------------------------------------

