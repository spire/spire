module Spire.CLI where
import Control.Monad.Error
import System.Environment
import Spire.Canonical.Types
import Spire.Surface.Types
import Spire.Surface.Parser
import Spire.Surface.Elaborator
import Spire.Expression.Checker

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

    Right program@(a , _A) -> do
      putStrLn $ "Parsed type:"
      putStrLn $ show a
      putStrLn ""
      putStrLn $ "Parsed value:"
      putStrLn $ show _A
      putStrLn ""

      case checkDef program of
        Left error -> putStrLn error
        Right (a' , _A') -> do
          putStrLn "Well-typed!"
          putStrLn $ "Evaluated type:"
          putStrLn $ show _A'
          putStrLn ""
          putStrLn $ "Evaluated value:"
          putStrLn $ show a'


----------------------------------------------------------------------

checkDef :: (Syntax , Syntax) -> Either String (Value , Type)
checkDef = runSpireM . checkDefM

checkDefM :: (Syntax , Syntax) -> SpireM (Value , Type)
checkDefM (a , _A) = do
  let syn = SAnn a _A
  expr <- elabI syn
  val <- infer expr
  return val

----------------------------------------------------------------------