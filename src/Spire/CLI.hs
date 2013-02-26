module Spire.CLI where
import Spire.SurfaceTerm as T

type TypeChecker = Type -> Term -> Either Term (Term , String)

run :: TypeChecker -> IO ()
run checkType = do
  putStrLn $ "Enter type: "
  tp <- getLine
  putStrLn $ "Enter term: "
  tm <- getLine
  case checkType (read tp) (read tm) of
     Left val -> do
       putStrLn "Well typed!"
       putStrLn $ "=> " ++ show val
     Right (ill , msg) -> do
          putStrLn "Ill typed!"
          putStrLn $ show ill ++ " " ++ msg

