{-# LANGUAGE ImplicitParams #-}
module Spire.Test where
import Data.List
import System.Directory
import System.Environment
import System.FilePath
import Test.HUnit
import Text.Parsec (parse)
import Spire.Canonical.Types
import Spire.Prelude.Interface
import Spire.Surface.Parser
import Spire.Options
import Spire.Pipeline
import Unbound.LocallyNameless

----------------------------------------------------------------------

unitTests :: Test
unitTests = TestList [ alpha , parsing ] where
  alpha = "Alpha-equality" ~: [ t1 ] where
    t1 = test $ assertBool "Universal quantifiers have alpha"
                           (e1 == e2) where
      e1 = id "x"
      e2 = id "y"
      id x =  VLam (bind (s2n x) $ VNeut (s2n x) Id)
  -- Our equality is defined to disequate all terms with mvar binders,
  -- so we can't compare the terms here :P
  parsing = "Parsing" ~: [ t1 ] where
    p = show . parse parseSyntax ""
    t1 = test $ assertEqual s (p s) ps where
      s  = "\\ _ -> _"
      ps = "Right (SLam (<_> SWildCard))"

----------------------------------------------------------------------

context :: String -> [Test] -> Test
context l ts = l ~: TestList ts

----------------------------------------------------------------------

integrationTests :: FilePath -> IO Test
integrationTests directory = do
  allFiles <- getDirectoryContents directory
  let testFileNames = filter (isSuffixOf ".spire") allFiles
  let testFiles = map (directory </>) testFileNames
  prelude <- readPrelude
  tests <- mapM (testFile prelude) testFiles
  return $ TestList (testInitEnv : tests)

testFile :: Env -> FilePath -> IO Test
testFile env file = do
  code <- readFile file
  return $ TestLabel file (TestCase (assertFileWellTyped env file code))

testInitEnv :: Test
testInitEnv = TestLabel "Initial environment" $
  TestCase assertInitEnvWellTyped

assertInitEnvWellTyped :: Assertion
assertInitEnvWellTyped = case checkInitEnv of
  Left error -> assertFailure ("Error in initial environment:\n" ++ error)
  Right ()   -> return ()
  where ?conf = emptyConf

assertFileWellTyped :: Env -> FilePath -> String -> Assertion
assertFileWellTyped env file code = case parseProgram file code of
  Left  error     -> assertFailure ("Parse error:\n" ++ formatParseError error)
  Right syntax    -> case elabProgram env syntax of
    Left  error   -> assertFailure ("Elab error:\n" ++ error)
    Right program -> case checkProgram env program of
      Left error  -> assertFailure ("Check error:\n" ++ error)
      Right _     -> return ()
  where ?conf = emptyConf

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