module Spire.CLI where
import Control.Monad.Error
import System.Environment
import Spire.Parser
import Spire.Surface
import Spire.Neutral

run :: IO ()
run = do
  args <- getArgs
  if null args
  then checkFromUser
  else checkFromFile (head args)

checkFromFile :: String -> IO ()
checkFromFile name = do
  source <- readFile name
  case parseProgram source of
    Left error -> do
      putStrLn "Parse error:"
      putStrLn $ show error

    Right program -> do
      putStrLn $ "Parsed program:"
      putStrLn $ show program
      putStrLn ""

      case infer [] program of
        Left error -> do
          putStrLn error

        Right (VDefs program' , VProg) -> do
          putStrLn "Well-typed!"
          putStrLn $ "Evaluated program:\n"
          mapM_ (\(tm , tp) ->
            putStrLn (show tm ++ " : " ++ show tp)
            ) program'

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
