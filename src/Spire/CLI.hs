module Spire.CLI where
import Control.Monad.Error
import System.Environment
import Text.Printf
import Spire.Surface.Parsing
import Spire.Surface.PrettyPrinting
import Spire.Expression.CheckingAndEvaluation
import Spire.Canonical.Types

run :: IO ()
run = do
  args <- getArgs
  if null args
  then checkFromUser
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
      putStrLn $ show program
      putStrLn ""

      case checkDefsStable program of
        Left error -> do
          putStrLn error

        Right program' -> do
          putStrLn "Well-typed!"
          putStrLn $ "Evaluated program:\n"
          let -- print :: (Show t , Display t) => String -> String -> t -> IO ()
              print name sep x = do
                let prefix = printf "%s %s" name sep :: String
                putStrLn $ printf  "%s %s"  prefix             (show x)
                putStrLn $ printf "%*s %s"  (length prefix) "" (prettyPrint x)

          forM_ program $ \d@(l , a , aT) -> do
            print l ":" aT
            print l "=" a
            putStrLn ""

          -- Whole program, for checking that output of pretty printer
          -- is valid input to type checker.
          putStrLn "\nPretty printed:\n"
          mapM_ (putStrLn . (++"\n") . prettyPrint) program

checkFromUser :: IO ()
checkFromUser = do
  mtp <- typeCheck "type" VType
  case mtp of
    Nothing -> return ()
    Just tp -> do
      putStrLn ""
      typeCheck "value" tp
      return ()

typeCheck label tp = do
  putStrLn $ "Enter " ++ label ++ ":"
  input <- getLine
  putStrLn ""
  case parseTerm input of
    Left error -> do
      putStrLn "Parse error:"
      putStrLn $ show error
      return Nothing

    Right tm -> do
      putStrLn $ "Parsed " ++ label ++ ":"
      putStrLn $ show tm
      putStrLn ""

      case check [] tm tp of
        Left error -> do 
          putStrLn error
          return Nothing
        Right tm' -> do
          putStrLn "Well-typed!"
          putStrLn $ "Evaluated " ++ label ++ ":"
          putStrLn $ show tm'
          return $ Just tm'
