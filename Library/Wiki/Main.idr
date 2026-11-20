module Wiki.Main

import Wiki.BoxCoreSpec
import Wiki.BoxPropertySpec

%default total

main : IO ()
main = do
  putStrLn "========================================================"
  putStrLn "  FINSC-BOX FOUNDATION WIKI SUITE                       "
  putStrLn "========================================================"
  p1 <- auditBoxCoreProof
  p2 <- auditBoxProperties
  if p1 && p2
    then putStrLn "✨ ALL FINSC-BOX SPECIFICATIONS & QUICKCHECK PASSED ✨"
    else do
      putStrLn "❌ FINSC-BOX SUITE FAILED"
