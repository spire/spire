module Spire.Test where
import Data.List
import System.Directory
import System.Environment
import System.FilePath
import Test.HUnit
import Text.Parsec.Error
import Text.Parsec (parse)
import Spire.Canonical.Types
import Spire.Canonical.Evaluator
import Spire.Surface.Parser
import Spire.Surface.Elaborator
import Spire.Expression.Checker
import Spire.Pipeline
import Unbound.LocallyNameless

----------------------------------------------------------------------

unitTests :: Test
unitTests = TestList [ alpha , parsing ] where
  alpha = "Alpha-equality" ~: [ t1 , t2 ] where
    t1 = test $ assertBool "Universal quantifiers have alpha"
                           (e1 == e2) where
      e1 = id "x"
      e2 = id "y"
      id x =  VLam (bind (s2n x) $ VNeut (s2n x) Id)
    t2 = test $ assertBool "Existential quantifiers don't have alpha"
                           (not $ e1 == e1) where
      e1 = VMeta (BindMeta (bind (s2n "x" , Embed (VType , Nothing))
                                 (VNeut (s2n "x") Id)))
  -- Our equality is defined to disequate all terms with mvar binders,
  -- so we can't compare the terms here :P
  parsing = "Parsing" ~: [ t1 , t2 ] where
    p = show . parse parseSyntax ""
    t1 = test $ assertEqual s (p s) ps where
      s  = "? x : Type = Type . x"
      ps = "Right (SBindMeta (BindMeta (<(x,{(SType,Just SType)})> SVar 0@0)))"
    t2 = test $ assertEqual s (p s) ps where
      s  = "? x : _ . _"
      ps = "Right (SBindMeta (BindMeta (<(x,{(SWildCard,Nothing)})> SWildCard)))"

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
  Right syntax    -> case elabProgram syntax of
    Left  error   -> assertFailure ("Elab error:\n" ++ error)
    Right program -> case checkProgram program of
      Left error  -> assertFailure ("Check error:\n" ++ error)
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