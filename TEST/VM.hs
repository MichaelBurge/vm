module TEST.VM(tests) where
import Test.HUnit
import VM

doesEmptyProgramRun = 
    TestCase (assertEqual "Empty program changed the context: "
                           (defaultContext [])
                           (runProgram [])
             )
intentionalFail = TestCase (assertFailure "aoeu")

tests = 
    TestList [TestLabel "Does the empty program run?" doesEmptyProgramRun,
              TestLabel "Intentionally failing" intentionalFail
             ]

main = runTestTT tests