import System.Exit (exitFailure, exitSuccess)
import Test.HUnit
import TEST.VM

runTests ts = 
    runTestTT ts >>= \x ->
        if (failures x + errors x) > 0
        then exitFailure
        else exitSuccess

main = do
  runTests TEST.VM.tests