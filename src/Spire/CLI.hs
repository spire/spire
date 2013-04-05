module Spire.CLI where
import Spire.Parser
import Spire.Surface
import Spire.Neutral

run :: IO ()
run = do
  mtp <- typeCheck "type" VType
  case mtp of
    Nothing -> return ()
    Just tp -> do
      typeCheck "value" tp
      return ()

typeCheck label tp = do
  putStrLn $ "Enter " ++ label ++ ":"
  tm <- getLine
  case parseTerm tm of
    Left error -> do
      putStrLn "Parse error:"
      putStrLn (show error)
      return Nothing

    Right tm' -> do
      putStrLn $ "Parsed " ++ label ++ ":"
      putStrLn (show tm')
      putStrLn ""

      case check [] tm' tp of
        Left error -> do 
          putStrLn error
          return Nothing
        Right () -> do
          putStrLn "Well-typed!"
          putStrLn $ "Evaluated " ++ label ++ ":"
          let tm'' = evalC tm'
          putStrLn (show tm'')
          return $ Just tm''
