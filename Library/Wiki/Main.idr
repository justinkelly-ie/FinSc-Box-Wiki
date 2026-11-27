module Wiki.Main

import Data.List
import System
import Wiki.BoxCoreSpec
import Wiki.BoxPropertySpec
import Wiki.BoxSterlingSpec
import Wiki.BoxBench

%default total

covering
main : IO ()
main = do
  args <- getArgs
  if elem "--bench" args
    then runBoxBenchmarks
    else do
      putStrLn "========================================================"
      putStrLn "  FINSC-BOX FOUNDATION WIKI SUITE                       "
      putStrLn "========================================================"
      putStrLn "  [FinSc-Box] Core Foundation & Sterling Definitions: compile-time QTT 0 Refl proofs verified."
      let p1 = checkBoxCodecAndZoomSuite
      putStrLn ("  [BoxCoreSpec] Codec round-trip, peel-work ordering & BlackRedZoom identities: " ++ show p1)
      p2 <- auditBoxProperties
      if p1 && p2
        then putStrLn "✨ ALL FINSC-BOX SPECIFICATIONS & QUICKCHECK PASSED ✨"
        else do
          putStrLn "❌ FINSC-BOX SUITE FAILED"
          exitFailure
