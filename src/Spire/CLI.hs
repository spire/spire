module Spire.CLI where
import Control.Monad.Error
import Spire.Parser
import Spire.Surface
import Spire.Neutral

run :: IO ()
run = do
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
      putStrLn (show tm)
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
