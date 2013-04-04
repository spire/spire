module Spire.CLI where
import Spire.Parser
import Spire.Surface
import Spire.Neutral

run :: IO ()
run = do
  putStrLn $ "Enter type: "
  tp <- getLine
  putStrLn (show tp)
  -- case parseTerm tp of
  --   Left error -> putStrLn "fail"
  --   Right tp' -> putStrLn "success"

  -- putStrLn $ "Enter term: "
  -- tm <- getLine
  -- case checkType (read tp) (read tm) of
  --    Left (tp' , tm') -> do
  --      putStrLn "Well typed!"
  --      putStrLn $ "=> " ++ show tm' ++ " : " ++ show tp'
  --    Right (Left (tp' , msg)) -> do
  --         putStrLn "Type is ill typed!"
  --         putStrLn $ show tp' ++ " " ++ msg
  --    Right (Right (tm' , msg)) -> do
  --         putStrLn "Term is ill typed!"
  --         putStrLn $ show tm' ++ " " ++ msg

