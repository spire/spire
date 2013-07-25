module Spire.Test where
import Data.List
import System.Directory
import System.Environment
import System.FilePath
import Test.HUnit
import Text.Parsec.Error
import Spire.Canonical.Types
import Spire.Canonical.HereditarySubstitution
import Spire.Surface.Parsing
import Spire.Surface.Elaborating
import Spire.Expression.CheckingAndEvaluation

----------------------------------------------------------------------

unitTests :: Test
unitTests = TestList [

  context "Weakening" [
  
    weakenVal0 (Neut (NVar (NomVar ("x", 0))))
    ~?= Neut (NVar (NomVar ("x", 1)))
    ,

    weakenVal0 (VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 0)))))))
    ~?= VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 0))))))
    ,

    weakenVal0 (VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 1)))))))
    ~?= VLam VUnit (Bound ("x",Neut (NVar (NomVar ("x",2)))))

    ]
  ,
  
  context "FreeVarsDB" [

    freeVarsDB0 (Neut (NVar (NomVar ("x", 0))))
    ~?= [NomVar ("x", 0)]
    ,

    freeVarsDB0 (VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 0)))))))
    ~?= []
    ,

    freeVarsDB0 (VLam VUnit (Bound ("x" , (Neut (NVar (NomVar ("x", 1)))))))
    ~?= [NomVar ("x",0)]

    ]

  ]

----------------------------------------------------------------------

context :: String -> [Test] -> Test
context l ts = l ~: TestList ts

----------------------------------------------------------------------

integrationTests :: FilePath -> IO Test
integrationTests directory = do
  allFiles <- getDirectoryContents directory
  let testFileNames = filter (isSuffixOf ".spire") allFiles
  let testFiles = map (directory </>) testFileNames
  tests <- mapM testFile testFiles
  return $ TestList tests

testFile :: FilePath -> IO Test
testFile file = do
  code <- readFile file
  return $ TestLabel file (TestCase (assertWellTyped file code))

assertWellTyped :: FilePath -> String -> Assertion
assertWellTyped file code = case parseProgram file code of
  Left  error     -> assertFailure ("Parse error:\n" ++ formatParseError error)
  Right syntax    -> case elabS syntax of
    Left  error   -> assertFailure ("Elaboration error:\n" ++ error)
    Right program -> case checkDefsStable program of
      Left  error -> assertFailure ("Type error:\n" ++ error)
      Right _     -> return ()

----------------------------------------------------------------------

runUnitTests :: IO Counts
runUnitTests = do
  putStrLn "Unit tests:"
  runTestTT unitTests

runIntegrationTests :: FilePath -> IO Counts
runIntegrationTests directory = do
  putStrLn "Integration tests:"
  runTestTT =<< integrationTests directory

runAllTests :: IO Counts
runAllTests = do
  args <- getArgs
  if null args
  then runUnitTests
  else do
    runUnitTests
    runIntegrationTests (head args)

main :: IO ()
main = runAllTests >> return ()

----------------------------------------------------------------------