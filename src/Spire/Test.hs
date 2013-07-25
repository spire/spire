module Spire.Test where
import Test.HUnit
import Spire.Canonical.Types
import Spire.Canonical.HereditarySubstitution

----------------------------------------------------------------------

tests :: Test
tests = TestList [

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

runTests :: IO Counts
runTests = runTestTT tests

main = runTests

----------------------------------------------------------------------