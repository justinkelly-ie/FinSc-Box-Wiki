# FinSc-Box Core Literate Specification

This literate specification tests the pure, minimal, refactored foundation of **FinSc-Box**:
the height-cached AVL tree `Box c k`, `HereditaryMSet c`, and Wildberger's rational rotations.

```idris
module Wiki.BoxCoreSpec

import FinScBox

%default total
```

## 1. Zero Annihilation & Canonical Vacuum

The empty vacuum multiset is identically canonical and norm zero:

```idris
public export
0 prfBoxCoreEmptyNormZero : sumHMSet (the PureMultiset (MkHMSet BoxLeaf)) = intToBoxInt 0
prfBoxCoreEmptyNormZero = Refl

public export
0 prfBoxCoreEmptyCanonical : isCanonicalHMSet (the PureMultiset (MkHMSet BoxLeaf)) = True
prfBoxCoreEmptyCanonical = Refl
```

## 2. Wildberger Equilateral Triple Spread Invariant

The 3 valence quark edges form an equilateral triangle with exact rational spread $s = 3/4$,
satisfying Wildberger's Triple Spread Formula with zero transcendental functions:
$$(s_1 + s_2 + s_3)^2 = 2(s_1^2 + s_2^2 + s_3^2) + 4 s_1 s_2 s_3$$

```idris
public export
0 prfWikiTripleSpread :
  (let sNum = 3
       sDen = 4
       lhs = (3 * sNum) * (3 * sNum) * (sDen * sDen)
       rhs1 = 2 * (3 * (sNum * sNum)) * (sDen * sDen)
       rhs2 = 4 * (sNum * sNum * sNum) * sDen
   in lhs == rhs1 + rhs2) = True
prfWikiTripleSpread = prfTripleSpreadEquilateral
```

## 3. Canonical Multiset Codec & Black/Red Zoom Laws

The promoted `Stage1.MultisetCodec` and `Stage1.BlackRedZoom` modules preserve canonical serialization parity and exact wrap/unwrap & Laurent-shift round-trips at `QTT 0`:

```idris
public export
0 prfBoxCoreCodecRoundTrip :
  (let b1 = Stage0.HereditaryMSet.scalarKeyHMSet 1
   in case Stage1.MultisetCodec.parsePureMultiset
             (Stage1.MultisetCodec.renderPureMultiset b1) of
        Just m  => m == b1
        Nothing => False) = True
prfBoxCoreCodecRoundTrip = Refl

public export
0 prfBoxCoreZoomSpaceRoundTrip :
  (zoomSpace (redShift 1) (zoomSpace (blackShift 1) Stage1.BlackRedZoom.sampleUnitPairMSet)
   == Stage1.BlackRedZoom.sampleUnitPairMSet) = True
prfBoxCoreZoomSpaceRoundTrip = Refl

public export
0 prfBoxCoreExternalLensNonPerturbing :
  Stage1.Lenses.applyExternalLens
    (MkExternalLens (\m => m) (blackShift 1) Stage1.BlackRedZoom.zeroShift (RetroTime 1) (\m => m))
    Stage1.BlackRedZoom.sampleUnitPairMSet
  = zoomSpace (blackShift 1) Stage1.BlackRedZoom.sampleUnitPairMSet
prfBoxCoreExternalLensNonPerturbing = prfExternalLensSpaceZoomMatches

public export
0 prfBoxCoreTdivPosAndOdd :
  (Stage0.BoxInt.tdivPosBox (MkBoxInt (-73)) 25 == MkBoxInt (-2) &&
   Stage0.BoxInt.tdiv2Box (MkBoxInt (-14)) == MkBoxInt (-7) &&
   Stage0.BoxInt.isOddBox (MkBoxInt (-7)) &&
   not (Stage0.BoxInt.isOddBox (MkBoxInt 24))) = True
prfBoxCoreTdivPosAndOdd = Refl

public export
0 prfBoxCoreAntisymEdgeZeroSum :
  (let e = Stage0.Box.mkAntisymEdge (intToSigned 1) (intToSigned 2) (MkBoxInt 9)
   in (Stage0.Box.totalMassBox e == MkBoxInt 0) && Stage0.Box.isAntisymBox e) = True
prfBoxCoreAntisymEdgeZeroSum = Refl

public export
0 prfBoxCoreLaurentStencil4 :
  (let st = Stage0.Box.laurentStencil4 (PosZ 0, ZeroZ) (ZeroZ, PosZ 0)
       p  = Stage0.Box.singletonBox (intToSigned 3, intToSigned (-2)) (MkBoxInt 5)
       c  = Stage0.Box.convolveStencil p st
   in (Stage0.Box.lookupBox (intToSigned 4, intToSigned (-2)) c == MkBoxInt 5) &&
      (Stage0.Box.lookupBox (intToSigned 2, intToSigned (-2)) c == MkBoxInt 5) &&
      (Stage0.Box.lookupBox (intToSigned 3, intToSigned (-1)) c == MkBoxInt 5) &&
      (Stage0.Box.lookupBox (intToSigned 3, intToSigned (-3)) c == MkBoxInt 5) &&
      (Stage0.Box.totalMassBox c == MkBoxInt 20)) = True
prfBoxCoreLaurentStencil4 = Refl

public export
0 prfBoxCoreRotatePythParam7 :
  (let r  = Stage1.ProjectiveRotation.rotatePythParam (MkBoxInt 7) (MkBoxInt 100) (MkBoxInt (-43)) (MkBoxInt 80)
       a1 = unwrapBox r.valA
       b1 = unwrapBox r.valB
       u1 = unwrapBox r.valU
       e0 = 2 * (100 * 100 + (-43) * (-43)) + 80 * 80
       e1 = 2 * (a1 * a1 + b1 * b1) + u1 * u1
   in (a1 + b1 == 57) && (e1 <= e0)) = True
prfBoxCoreRotatePythParam7 = Refl

public export
0 prfBoxCoreRdivPosBox :
  (Stage0.BoxInt.rdivPosBox (MkBoxInt 13) 25 == MkBoxInt 1 &&
   Stage0.BoxInt.rdivPosBox (MkBoxInt (-13)) 25 == MkBoxInt (-1) &&
   Stage0.BoxInt.rdivPosBox (MkBoxInt 12) 25 == MkBoxInt 0) = True
prfBoxCoreRdivPosBox = Refl

public export
0 prfBoxCoreLaurentGreen1 :
  (let st = Stage0.Box.laurentStencil4 (PosZ 0, ZeroZ) (ZeroZ, PosZ 0)
       p  = Stage0.Box.singletonBox (ZeroZ, ZeroZ) (MkBoxInt 16)
       g  = Stage0.Box.laurentGreenSeries combine 1 4 1 st p
   in (Stage0.Box.lookupBox (ZeroZ, ZeroZ) g == MkBoxInt 16) &&
      (Stage0.Box.lookupBox (PosZ 0, ZeroZ) g == MkBoxInt 4) &&
      (Stage0.Box.totalMassBox g == MkBoxInt 32)) = True
prfBoxCoreLaurentGreen1 = Refl

public export
0 prfBoxCoreRotatePythSymmetry :
  (let rPos = Stage1.ProjectiveRotation.rotatePythParam (MkBoxInt 7) (MkBoxInt 100) (MkBoxInt (-43)) (MkBoxInt 80)
       rNeg = Stage1.ProjectiveRotation.rotatePythParam (MkBoxInt 7) (MkBoxInt (-100)) (MkBoxInt 43) (MkBoxInt (-80))
   in (rNeg.valA == negBox rPos.valA) &&
      (rNeg.valB == negBox rPos.valB) &&
      (rNeg.valU == negBox rPos.valU)) = True
prfBoxCoreRotatePythSymmetry = Refl

public export
0 prfBoxCoreMaxelHalfStorage :
  (let a  = (ZeroZ, ZeroZ)
       b  = (PosZ 0, ZeroZ)
       c  = (ZeroZ, PosZ 0)
       ae = Stage0.Box.singletonMaxelEdge {form = AntisymForm} b a (MkBoxInt 7)
       sq = ae .*. ae
       st = Stage0.Box.laurentStencil4 (PosZ 0, ZeroZ) (ZeroZ, PosZ 0)
       sp = Stage0.Box.convolveMaxelStencil combine sq st
       dg = Stage0.Box.diagEmbedMaxel (Stage0.Box.singletonBox a (MkBoxInt 5))
       sy = Stage0.Box.addMaxel dg (Stage0.Box.singletonMaxelEdge b a (MkBoxInt 3))
       syA = sy .*. ae
       gn  = Stage0.Box.toGeneralMaxel sy .*. ae
       da  = Stage0.Box.addMaxel
               (Stage0.Box.singletonMaxelEdge {form = DiagAntisymForm} a a (MkBoxInt 5))
               (Stage0.Box.singletonMaxelEdge b a (MkBoxInt 7))
       daSt = Stage0.Box.convolveMaxelStencil combine da st
       pB = Stage0.Box.addAtKeyBox b (MkBoxInt 2) (Stage0.Box.singletonBox a (MkBoxInt 1))
       sB = Stage0.Box.singletonBox a (MkBoxInt 1)
       bx = Stage0.Box.singletonBox b (MkBoxInt 4)
       hm = Stage0.HereditaryMSet.scalarKeyHMSet 3
       (pY, pN) = Stage0.Box.partitionBox (== a) pB
   in (Stage0.Box.lookupMaxel b a ae == MkBoxInt 7) &&
      (Stage0.Box.lookupMaxel a b ae == MkBoxInt (-7)) &&
      (Stage0.Box.maxelNodeCount ae == 1) &&
      (Stage0.Box.traceMaxel ae == MkBoxInt 0) &&
      (Stage0.Box.transposeMaxel ae == Stage0.Box.negateMaxel ae) &&
      (Stage0.Box.lookupMaxel a b sq == MkBoxInt 49) &&
      (Stage0.Box.lookupMaxel b a sq == MkBoxInt 49) &&
      (Stage0.Box.maxelNodeCount sq == 1) &&
      (Stage0.Box.transposeMaxel sq == sq) &&
      Stage0.Box.isSymBox (Stage0.Box.toGeneralMaxel sq).rawMaxelBox &&
      (Stage0.Box.maxelNodeCount sp == 4) &&
      (Stage0.Box.lookupMaxel b (intToSigned 2, ZeroZ) sp == MkBoxInt 49) &&
      (Stage0.Box.traceMaxel dg == MkBoxInt 5) &&
      ((sy <.> sy) == (Stage0.Box.toGeneralMaxel sy <.> Stage0.Box.toGeneralMaxel sy)) &&
      ((ae <.> ae) == (Stage0.Box.toGeneralMaxel ae <.> Stage0.Box.toGeneralMaxel ae)) &&
      (Stage0.Box.toGeneralMaxel syA == gn) &&
      (Stage0.Box.lookupMaxel b a syA == MkBoxInt 21) &&
      (Stage0.Box.lookupMaxel a b syA == MkBoxInt (-21)) &&
      ((Stage0.Interfaces.scaleM (MkBoxInt 2) sy <.> sy) == MkBoxInt 86) &&
      ((Stage0.Interfaces.subM sy sy == Stage0.Interfaces.zeroM)) &&
      ((Stage0.Interfaces.addM bx (Stage0.Interfaces.negM bx) == Stage0.Interfaces.zeroM)) &&
      ((bx <.> bx) == MkBoxInt 16) &&
      ((hm <.> hm) == MkBoxInt 9) &&
      (Stage0.Interfaces.subM (Stage0.Interfaces.addM hm hm) hm == hm) &&
      ((sy <.> Stage0.Box.singletonMaxelEdge c a (MkBoxInt 1)) == MkBoxInt 0) &&
      (Stage0.Box.lookupMaxel a a da == MkBoxInt 5) &&
      (Stage0.Box.lookupMaxel b a da == MkBoxInt 7) &&
      (Stage0.Box.lookupMaxel a b da == MkBoxInt (-7)) &&
      (Stage0.Box.traceMaxel da == MkBoxInt 5) &&
      (Stage0.Box.maxelNodeCount da == 2) &&
      (Stage0.Box.transposeMaxel (Stage0.Box.transposeMaxel da) == da) &&
      (Stage0.Box.toGeneralMaxel (Stage0.Box.transposeMaxel da) ==
         Stage0.Box.transposeMaxel (Stage0.Box.toGeneralMaxel da)) &&
      ((da <.> da) == MkBoxInt 123) &&
      ((da <.> da) == (Stage0.Box.toGeneralMaxel da <.> Stage0.Box.toGeneralMaxel da)) &&
      (Stage0.Box.toGeneralMaxel (da .*. da) == (Stage0.Box.toGeneralMaxel da .*. Stage0.Box.toGeneralMaxel da)) &&
      (Stage0.Box.toGeneralMaxel (sy .*. da) == (Stage0.Box.toGeneralMaxel sy .*. Stage0.Box.toGeneralMaxel da)) &&
      (Stage0.Box.toGeneralMaxel (ae .*. da) == (Stage0.Box.toGeneralMaxel ae .*. Stage0.Box.toGeneralMaxel da)) &&
      (Stage0.Box.maxelNodeCount daSt == 8) &&
      (Stage0.Box.lookupMaxel b b daSt == MkBoxInt 5) &&
      (Stage0.Box.lookupMaxel b (intToSigned 2, ZeroZ) daSt == MkBoxInt (-7)) &&
      (Stage0.Box.diagBox da == Stage0.Box.singletonBox a (MkBoxInt 5)) &&
      (pY == sB) &&
      (Stage0.Box.maskOutBox sB pB == pN) &&
      (Stage0.Box.maskByBox pB sB == sB) &&
      (Stage0.Box.supportBox pB == Stage0.Box.setBox b (MkBoxInt 1) sB)) = True
prfBoxCoreMaxelHalfStorage = Refl

public export
runPaceCycle : Nat -> Integer -> Integer -> BoxInt -> (Nat, Nat, BoxInt)
runPaceCycle n budget load initBal = go n initBal 0 0
  where
    go : Nat -> BoxInt -> Nat -> Nat -> (Nat, Nat, BoxInt)
    go Z bal y s = (y, s, bal)
    go (S k) bal y s =
      case paceStreamStep budget load bal of
        (StreamYield (), nxt) => go k nxt (S y) s
        (StreamSkip,     nxt) => go k nxt y (S s)
        (StreamDone,     nxt) => go k nxt y s

public export
0 prfBoxCorePaceStreamLaws :
  (paceStreamStep 7 0 (MkBoxInt 0) == (StreamYield (), MkBoxInt 0) &&
   paceStreamStep 0 99 (MkBoxInt 5) == (StreamYield (), MkBoxInt 0) &&
   fst (paceStreamStep 2 3 (MkBoxInt 0)) == StreamSkip &&
   runPaceCycle 5 2 3 (MkBoxInt 0) == (2, 3, MkBoxInt 0) &&
   runPaceCycle 5 3 2 (MkBoxInt 0) == (3, 2, MkBoxInt 0) &&
   runPaceCycle 8 7 1 (MkBoxInt 0) == (7, 1, MkBoxInt 0) &&
   paceStreamStep 4 0 (MkBoxInt (-9)) == (StreamYield (), MkBoxInt 0)) = True
prfBoxCorePaceStreamLaws = Refl
```

## 4. Dynamic Verification Suite

```idris
public export
auditBoxCoreProof : IO Bool
auditBoxCoreProof = do
  putStrLn "  [FinSc-Box] Core Foundation:"
  let normZero = sumHMSet (the PureMultiset emptyHMSet) == intToBoxInt 0
  let isCan = isCanonicalHMSet (the PureMultiset emptyHMSet)
  let spreadOk = equilateralSpreadNum == 3 && equilateralSpreadDen == 4
  let txt = renderPureMultiset sampleUnitPairMSet
  let codecOk = txt == show sampleUnitPairMSet &&
                (case parsePureMultiset txt of
                   Just m' => m' == sampleUnitPairMSet
                   Nothing => False)
  let zoomOk = zoomSpace (redShift 1) (zoomSpace (blackShift 1) sampleUnitPairMSet) == sampleUnitPairMSet
  let lensOk = applyExternalLens (MkExternalLens (\m => m) (blackShift 1) zeroShift (RetroTime 1) (\m => m)) sampleUnitPairMSet
                 == zoomSpace (blackShift 1) sampleUnitPairMSet
  let tdivOk = tdivPosBox (MkBoxInt (-73)) 25 == MkBoxInt (-2) &&
               rdivPosBox (MkBoxInt 13) 25 == MkBoxInt 1 &&
               rdivPosBox (MkBoxInt (-13)) 25 == MkBoxInt (-1) &&
               tdiv2Box (MkBoxInt (-14)) == MkBoxInt (-7) &&
               isOddBox (MkBoxInt (-7)) &&
               not (isOddBox (MkBoxInt 24))
  let a      = (ZeroZ, ZeroZ)
  let b      = (PosZ 0, ZeroZ)
  let edge   = mkAntisymEdge a b (MkBoxInt 9)
  let ae     = singletonMaxelEdge {form = AntisymForm} b a (MkBoxInt 7)
  let sq     = ae .*. ae
  let sy     = addM (diagEmbedMaxel (singletonBox a (MkBoxInt 5))) (singletonMaxelEdge b a (MkBoxInt 3))
  let syA    = sy .*. ae
  let da     = addM (singletonMaxelEdge {form = DiagAntisymForm} a a (MkBoxInt 5))
                    (singletonMaxelEdge b a (MkBoxInt 7))
  let st4    = laurentStencil4 (PosZ 0, ZeroZ) (ZeroZ, PosZ 0)
  let sp     = convolveMaxelStencil combine sq st4
  let conv   = convolveStencil (singletonBox (intToSigned 3, intToSigned (-2)) (MkBoxInt 5)) st4
  let green  = laurentGreenSeries combine 1 4 1 st4 (singletonBox (ZeroZ, ZeroZ) (MkBoxInt 16))
  let r7     = rotatePythParam (MkBoxInt 7) (MkBoxInt 100) (MkBoxInt (-43)) (MkBoxInt 80)
  let algOk  = totalMassBox edge == MkBoxInt 0 && isAntisymBox edge &&
               lookupMaxel b a ae == MkBoxInt 7 && lookupMaxel a b ae == MkBoxInt (-7) &&
               lookupMaxel a b sq == MkBoxInt 49 && lookupMaxel b a sq == MkBoxInt 49 &&
               (sy <.> sy) == (toGeneralMaxel sy <.> toGeneralMaxel sy) &&
               (ae <.> ae) == (toGeneralMaxel ae <.> toGeneralMaxel ae) &&
               toGeneralMaxel syA == (toGeneralMaxel sy .*. ae) &&
               lookupMaxel a a da == MkBoxInt 5 && lookupMaxel b a da == MkBoxInt 7 && lookupMaxel a b da == MkBoxInt (-7) &&
               traceMaxel da == MkBoxInt 5 && (da <.> da) == MkBoxInt 123 &&
               toGeneralMaxel (da .*. da) == (toGeneralMaxel da .*. toGeneralMaxel da) &&
               toGeneralMaxel (sy .*. da) == (toGeneralMaxel sy .*. da) &&
               diagBox da == singletonBox a (MkBoxInt 5) &&
               maxelNodeCount ae == 1 && maxelNodeCount sp == 4 &&
               lookupMaxel b (intToSigned 2, ZeroZ) sp == MkBoxInt 49 &&
               isSymBox (toGeneralMaxel sq).rawMaxelBox &&
               totalMassBox conv == MkBoxInt 20 &&
               totalMassBox green == MkBoxInt 32 &&
               unwrapBox r7.valA + unwrapBox r7.valB == 57
  let paceOk = paceStreamStep 7 0 (MkBoxInt 0) == (StreamYield (), MkBoxInt 0) &&
               paceStreamStep 0 99 (MkBoxInt 5) == (StreamYield (), MkBoxInt 0) &&
               fst (paceStreamStep 2 3 (MkBoxInt 0)) == StreamSkip &&
               runPaceCycle 5 2 3 (MkBoxInt 0) == (2, 3, MkBoxInt 0) &&
               runPaceCycle 5 3 2 (MkBoxInt 0) == (3, 2, MkBoxInt 0) &&
               runPaceCycle 8 7 1 (MkBoxInt 0) == (7, 1, MkBoxInt 0) &&
               paceStreamStep 4 0 (MkBoxInt (-9)) == (StreamYield (), MkBoxInt 0)
  let pass = normZero && isCan && spreadOk && codecOk && zoomOk && lensOk && tdivOk && algOk && paceOk
  putStrLn ("  - Vacuum norm=0, canonical=True, spread=3/4, codec=" ++ show codecOk ++ ", zoom=" ++ show zoomOk ++ ", lens=" ++ show lensOk ++ ", tdiv=" ++ show tdivOk ++ ", alg=" ++ show algOk ++ ", pace=" ++ show paceOk ++ " -> pass=" ++ show pass)
  pure pass
```
