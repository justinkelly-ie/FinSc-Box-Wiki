module Wiki.Main

import Wiki.BoxCoreSpec
import Wiki.BoxPropertySpec

%default total

main : IO ()
main = do
  putStrLn "========================================================"
  putStrLn "  FINSC-BOX FOUNDATION WIKI SUITE                       "
  putStrLn "========================================================"
  putStrLn "  [FinSc-Box] Core Foundation: compile-time QTT 0 Refl proofs verified."
  p2 <- auditBoxProperties
  if p2
    then putStrLn "✨ ALL FINSC-BOX SPECIFICATIONS & QUICKCHECK PASSED ✨"
    else do
      putStrLn "❌ FINSC-BOX SUITE FAILED"
