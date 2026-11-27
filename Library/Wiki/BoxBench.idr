module Wiki.BoxBench

import Data.List
import System.Clock
import FinScBox

%default total

--------------------------------------------------------------------------------
-- MONOTONIC NANOSECOND BENCHMARK HARNESS FOR `Box`, `Maxel`, & `HereditaryMSet`
--------------------------------------------------------------------------------

elapsedUs : Clock Monotonic -> Clock Monotonic -> Integer
elapsedUs t0 t1 =
  let d = timeDifference t1 t0
  in seconds d * 1000000 + nanoseconds d `div` 1000

formatMs : Integer -> String
formatMs us =
  let ms = us `div` 1000
      fr = (us `mod` 1000) `div` 10
      pad = if fr < 10 then "0" else ""
  in show ms ++ "." ++ pad ++ show fr ++ " ms"

covering
benchOp : String -> Nat -> (() -> BoxInt) -> IO ()
benchOp label iters fn = do
  let sink0 = fn ()
  t0 <- clockTime Monotonic
  let acc = loop iters sink0
  t1 <- clockTime Monotonic
  let us = elapsedUs t0 t1
      perIter = if iters == 0 then 0 else us `div` cast iters
  putStrLn ("  " ++ label ++ " | total=" ++ formatMs us ++
            " (" ++ show iters ++ "x, " ++ show perIter ++ " us/iter, chk=" ++ show acc ++ ")")
  where
    loop : Nat -> BoxInt -> BoxInt
    loop Z     s = s
    loop (S k) s = loop k (s + fn ())

--------------------------------------------------------------------------------
-- DETERMINISTIC BENCHMARK FIXTURES (DOMAIN-FREE)
--------------------------------------------------------------------------------

natCoord : Nat -> SignedCoord
natCoord Z     = ZeroZ
natCoord (S k) = PosZ k

mkSiteMSet2 : SignedCoord -> SignedCoord -> PureMultiset
mkSiteMSet2 x y =
  let a0 = scalarKeyHMSet 1
      a1 = scalarKeyHMSet 2
  in MkHMSet (setBox a1 (cast y) (setBox a0 (cast x) BoxLeaf))

mkGridPure2 : Nat -> Nat -> Box BoxInt PureMultiset
mkGridPure2 w h = goW w BoxLeaf
  where
    goH : Nat -> SignedCoord -> Nat -> Box BoxInt PureMultiset -> Box BoxInt PureMultiset
    goH _ _ Z     acc = acc
    goH xn x (S y) acc =
      let yy   = natCoord y
          wVal = MkBoxInt (cast xn + cast y + 1)
      in goH xn x y (setBox (mkSiteMSet2 x yy) wVal acc)

    goW : Nat -> Box BoxInt PureMultiset -> Box BoxInt PureMultiset
    goW Z     acc = acc
    goW (S x) acc = goW x (goH x (natCoord x) h acc)

mkGridSpace2 : Nat -> Nat -> Box BoxInt (Space 2)
mkGridSpace2 w h = goW w BoxLeaf
  where
    goH : Nat -> SignedCoord -> Nat -> Box BoxInt (Space 2) -> Box BoxInt (Space 2)
    goH _ _ Z     acc = acc
    goH xn x (S y) acc =
      let yy   = natCoord y
          wVal = MkBoxInt (cast xn + cast y + 1)
      in goH xn x y (setBox [x, yy] wVal acc)

    goW : Nat -> Box BoxInt (Space 2) -> Box BoxInt (Space 2)
    goW Z     acc = acc
    goW (S x) acc = goW x (goH x (natCoord x) h acc)

mkSymLatticeSpace2 : Nat -> Nat -> Maxel BoxInt (Space 2) (Space 2) SymForm
mkSymLatticeSpace2 w h = goW w emptyMaxel
  where
    goH : Nat -> SignedCoord -> Nat -> Maxel BoxInt (Space 2) (Space 2) SymForm -> Maxel BoxInt (Space 2) (Space 2) SymForm
    goH _ _ Z     acc = acc
    goH xn x (S y) acc =
      let yy = natCoord y
          p0 = the (Space 2) [x, yy]
          px = the (Space 2) [x + 1, yy]
          py = the (Space 2) [x, yy + 1]
          v  = MkBoxInt ((cast xn + cast y + 3) * 100)
      in goH xn x y (setMaxelEdge p0 py v (setMaxelEdge p0 px v (setMaxelEdge p0 p0 (v * 2) acc)))

    goW : Nat -> Maxel BoxInt (Space 2) (Space 2) SymForm -> Maxel BoxInt (Space 2) (Space 2) SymForm
    goW Z     acc = acc
    goW (S x) acc = goW x (goH x (natCoord x) h acc)

mkSymLatticePure2 : Nat -> Nat -> Maxel BoxInt PureMultiset PureMultiset SymForm
mkSymLatticePure2 w h = goW w emptyMaxel
  where
    goH : Nat -> SignedCoord -> Nat -> Maxel BoxInt PureMultiset PureMultiset SymForm -> Maxel BoxInt PureMultiset PureMultiset SymForm
    goH _ _ Z     acc = acc
    goH xn x (S y) acc =
      let yy = natCoord y
          p0 = mkSiteMSet2 x yy
          px = mkSiteMSet2 (x + 1) yy
          py = mkSiteMSet2 x (yy + 1)
          v  = MkBoxInt ((cast xn + cast y + 3) * 100)
      in goH xn x y (setMaxelEdge p0 py v (setMaxelEdge p0 px v (setMaxelEdge p0 p0 (v * 2) acc)))

    goW : Nat -> Maxel BoxInt PureMultiset PureMultiset SymForm -> Maxel BoxInt PureMultiset PureMultiset SymForm
    goW Z     acc = acc
    goW (S x) acc = goW x (goH x (natCoord x) h acc)

mkSparseGeneralNat : Nat -> Maxel BoxInt Nat Nat GeneralForm
mkSparseGeneralNat n = go n emptyMaxel
  where
    go : Nat -> Maxel BoxInt Nat Nat GeneralForm -> Maxel BoxInt Nat Nat GeneralForm
    go Z     acc = acc
    go (S k) acc =
      let m1 = setMaxelEdge k k (MkBoxInt 2) acc
          m2 = setMaxelEdge k (S k) (MkBoxInt 1) m1
          m3 = setMaxelEdge (S k) k (MkBoxInt (-1)) m2
          m4 = setMaxelEdge k (k + 2) (MkBoxInt 3) m3
      in go k m4

stencilSpace2 : Box BoxInt (Space 2)
stencilSpace2 =
  addAtKeyBox [0, -1] 1 $
  addAtKeyBox [0, 1]  1 $
  addAtKeyBox [-1, 0] 1 $
  singletonBox [1, 0] (MkBoxInt 1)

stencilPure2 : Box BoxInt PureMultiset
stencilPure2 =
  addAtKeyBox (mkSiteMSet2 0 (-1)) 1 $
  addAtKeyBox (mkSiteMSet2 0 1)    1 $
  addAtKeyBox (mkSiteMSet2 (-1) 0) 1 $
  singletonBox (mkSiteMSet2 1 0) (MkBoxInt 1)

--------------------------------------------------------------------------------
-- RUNNER
--------------------------------------------------------------------------------

export
covering
runBoxBenchmarks : IO ()
runBoxBenchmarks = do
  putStrLn "================================================================"
  putStrLn "  FINSC-BOX MICROBENCHMARK SUITE (Box / Maxel / HereditaryMSet) "
  putStrLn "================================================================"
  let bSpA   = mkGridSpace2 25 25              -- 625 entries (Space 2)
      bSpB   = mapBox (\p => combine p [3, 3]) bSpA
      bPmA   = mkGridPure2 20 20               -- 400 entries (PureMultiset)
      bPmB   = mapBox (\p => combine p (mkSiteMSet2 3 3)) bPmA
      mSpSym = mkSymLatticeSpace2 15 15        -- ~675 entries (SymForm Space 2)
      mPmSym = mkSymLatticePure2 10 10         -- ~300 entries (SymForm PureMultiset)
      mGen80 = mkSparseGeneralNat 80           -- ~320 entries (80x80 banded GeneralForm)
      z12    = spreadZHMSet 12
      hmBigA = MkHMSet bPmA
      hmBigB = MkHMSet (setBox (mkSiteMSet2 0 0) 999 bPmA)

  benchOp "1. Box build 25x25 (Space 2)           " 20  (\() => totalMassBox (mkGridSpace2 25 25))
  benchOp "2. Box build 20x20 (PureMultiset)      " 10  (\() => totalMassBox (mkGridPure2 20 20))
  benchOp "3. Box lookup 625x (Space 2)           " 50  (\() => foldBox (\k, _, acc => acc + lookupBox k bSpA) 0 bSpA)
  benchOp "4. Box lookup 400x (PureMultiset)      " 20  (\() => foldBox (\k, _, acc => acc + lookupBox k bPmA) 0 bPmA)
  benchOp "5. Box Eq (equal 625 Space 2)          " 50  (\() => if bSpA == bSpA then 1 else 0)
  benchOp "6. Box Eq (diff-1st 625 Space 2)       " 200 (\() => if bSpA == bSpB then 1 else 0)
  benchOp "7. Box unionBox (625+625 Space 2)      " 20  (\() => totalMassBox (unionBox bSpA bSpB))
  benchOp "8. Box unionBox (400+400 PureMultiset) " 10  (\() => totalMassBox (unionBox bPmA bPmB))
  benchOp "9. Box hadamardBox (625 Space 2)       " 20  (\() => totalMassBox (hadamardBox bSpA bSpB))
  benchOp "10. Box scaleDivPrune (625 Space 2)    " 30  (\() => totalMassBox (scaleDivPruneBox 3 5 bSpA))
  benchOp "11. Box scaleDivPrune (400 PureMSet)   " 15  (\() => totalMassBox (scaleDivPruneBox 3 5 bPmA))
  benchOp "12. Box filterBox (625 Space 2)        " 30  (\() => totalMassBox (filterBox (\_ => True) bSpA))
  benchOp "13. Maxel shiftConvolve (675 Space 2)  " 10  (\() => sumStoredMaxel (shiftConvolveMaxel mSpSym stencilSpace2))
  benchOp "14. Maxel shiftConvolve (300 PureMSet) " 5   (\() => sumStoredMaxel (shiftConvolveMaxel mPmSym stencilPure2))
  benchOp "15. Maxel scaleDivPrune (675 Space 2)  " 20  (\() => sumStoredMaxel (scaleDivPruneMaxel 32 100 mSpSym))
  benchOp "16. Maxel composeMaxel (80x80 General) " 5   (\() => sumStoredMaxel (composeMaxel mGen80 mGen80))
  benchOp "17. HMSet compare (diff-1st 400-node)  " 50  (\() => if hmBigA == hmBigB then 1 else 0)
  benchOp "18. HMSet mulHMSet (Z_12 * Z_12)       " 20  (\() => sumHMSet (z12 * z12))
  putStrLn "================================================================"
