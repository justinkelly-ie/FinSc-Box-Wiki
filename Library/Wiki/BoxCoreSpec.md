# FinSc-Box Core Literate Specification

This literate specification tests the pure, minimal foundation of **FinSc-Box**:
the height-cached AVL tree `Box c k`, `HereditaryMSet c`, `Maxel` half-storage, streaming peel-work views, and conservative quadratic exchanges.

```idris
module Wiki.BoxCoreSpec

import FinScBox

%default total
```

## 1. Zero Annihilation & Canonical Vacuum

The empty vacuum multiset is identically canonical and norm zero:

```idris
public export
0 prfBoxCoreEmptyNormZero : sumHMSet (the PureMultiset (MkHMSet BoxLeaf)) = MkBoxInt 0
prfBoxCoreEmptyNormZero = Refl

public export
0 prfBoxCoreEmptyCanonical : isCanonicalHMSet (the PureMultiset (MkHMSet BoxLeaf)) = True
prfBoxCoreEmptyCanonical = Refl
```

## 2. Wildberger Equilateral Triple Spread Invariant

Three symmetric edges of equal rational spread $s = 3/4$ satisfy Wildberger's Triple Spread Formula with zero transcendental functions:
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
prfWikiTripleSpread = Refl
```

## 3. Canonical Multiset Codec & Black/Red Zoom Laws

The `FinScBox.MultisetCodec` and `FinScBox.BlackRedZoom` modules preserve canonical serialization parity and exact wrap/unwrap & Laurent-shift round-trips at `QTT 0`:

```idris
public export
0 prfBoxCoreCodecRoundTrip :
  (let b1 = FinScBox.HereditaryMSet.scalarKeyHMSet 1
   in case FinScBox.MultisetCodec.parsePureMultiset
             (FinScBox.MultisetCodec.renderPureMultiset b1) of
        Just m  => m == b1
        Nothing => False) = True
prfBoxCoreCodecRoundTrip = Refl

public export
0 prfBoxCoreZoomSpaceRoundTrip :
  (zoomSpace (redShift 1) (zoomSpace (blackShift 1) FinScBox.BlackRedZoom.sampleUnitPairMSet)
   == FinScBox.BlackRedZoom.sampleUnitPairMSet) = True
prfBoxCoreZoomSpaceRoundTrip = Refl

public export
0 prfBoxCoreExternalLensNonPerturbing :
  FinScBox.Lenses.applyExternalLens
    (FinScBox.Lenses.zoomedPureLens (blackShift 1) FinScBox.HereditaryMSet.emptyHMSet (\m => m))
    FinScBox.BlackRedZoom.sampleUnitPairMSet
  = zoomSpace (blackShift 1) FinScBox.BlackRedZoom.sampleUnitPairMSet
prfBoxCoreExternalLensNonPerturbing = prfExternalLensSpaceZoomMatches

public export
0 prfBoxCoreTdivPosAndOdd :
  (FinScBox.BoxInt.tdivPosBox (MkBoxInt (-73)) 25 == MkBoxInt (-2) &&
   FinScBox.BoxInt.tdiv2Box (MkBoxInt (-14)) == MkBoxInt (-7) &&
   FinScBox.BoxInt.isOddBox (MkBoxInt (-7)) &&
   not (FinScBox.BoxInt.isOddBox (MkBoxInt 24))) = True
prfBoxCoreTdivPosAndOdd = Refl

public export
checkEuclidCase : Integer -> Integer -> Integer -> Integer -> Bool
checkEuclidCase a b q r =
  (FinScBox.BoxInt.divBox (MkBoxInt a) (MkBoxInt b) == MkBoxInt q) &&
  (FinScBox.BoxInt.modBox (MkBoxInt a) (MkBoxInt b) == MkBoxInt r)

public export
0 prfBoxCoreEuclidDivMod :
  (checkEuclidCase 7 3 2 1 &&
   checkEuclidCase (-7) 3 (-3) 2 &&
   checkEuclidCase 7 (-3) (-2) 1 &&
   checkEuclidCase (-7) (-3) 3 2 &&
   checkEuclidCase (-6) 3 (-2) 0 &&
   checkEuclidCase 6 (-3) (-2) 0 &&
   checkEuclidCase (-6) (-3) 2 0 &&
   checkEuclidCase 7 0 0 0) = True
prfBoxCoreEuclidDivMod = Refl

public export
0 prfBoxCoreIntegralDivMod :
  (div (MkBoxInt (-7)) (MkBoxInt 3), mod (MkBoxInt (-7)) (MkBoxInt 3))
  = (MkBoxInt (-3), MkBoxInt 2)
prfBoxCoreIntegralDivMod = Refl

public export
0 prfBoxCoreAntisymEdgeZeroSum :
  (let e = FinScBox.Box.singletonMaxelEdge {form = AntisymForm} (the (Space 1) [1]) [2] (MkBoxInt 9)
   in (FinScBox.Box.sumStoredMaxel (FinScBox.Box.toGeneralMaxel e) == MkBoxInt 0) &&
      FinScBox.Box.isAntisymMaxel e) = True
prfBoxCoreAntisymEdgeZeroSum = Refl

public export
0 prfBoxCoreUnitAxes2D :
  (let axes2 = the (Box MultisetBit (Fin 2)) (FinScBox.Box.setBox (FS FZ) OneBit (FinScBox.Box.singletonBox FZ OneBit))
       st    = the (Box BoxInt (Space 2)) (FinScBox.Box.unitStencilBox (unitSpace {n = 2}) axes2)
       p     = FinScBox.Box.singletonBox (the (Space 2) [3, -2]) (MkBoxInt 5)
       c     = FinScBox.Box.mulBoxWith p st
   in (FinScBox.Box.lookupBox (the (Space 2) [4, -2]) c == MkBoxInt 5) &&
      (FinScBox.Box.lookupBox (the (Space 2) [2, -2]) c == MkBoxInt 5) &&
      (FinScBox.Box.lookupBox (the (Space 2) [3, -1]) c == MkBoxInt 5) &&
      (FinScBox.Box.lookupBox (the (Space 2) [3, -3]) c == MkBoxInt 5) &&
      (FinScBox.Box.totalMassBox c == MkBoxInt 20)) = True
prfBoxCoreUnitAxes2D = Refl

public export
0 prfBoxCoreExchangeQuadratic7 :
  (let r  = FinScBox.QuadraticExchange.exchangeQuadratic (MkBoxInt 7) (MkBoxInt 100) (MkBoxInt (-43)) (MkBoxInt 80)
       a1 = unwrapBox r.valA
       b1 = unwrapBox r.valB
       u1 = unwrapBox r.valU
       e0 = 2 * (100 * 100 + (-43) * (-43)) + 80 * 80
       e1 = 2 * (a1 * a1 + b1 * b1) + u1 * u1
   in (a1 + b1 == 57) && (e1 <= e0)) = True
prfBoxCoreExchangeQuadratic7 = Refl

public export
0 prfBoxCoreRdivPosBox :
  (FinScBox.BoxInt.rdivPosBox (MkBoxInt 13) 25 == MkBoxInt 1 &&
   FinScBox.BoxInt.rdivPosBox (MkBoxInt (-13)) 25 == MkBoxInt (-1) &&
   FinScBox.BoxInt.rdivPosBox (MkBoxInt 12) 25 == MkBoxInt 0) = True
prfBoxCoreRdivPosBox = Refl

public export
0 prfBoxCoreActMaxelR :
  (let m = the (Maxel BoxInt (Fin 2) (Fin 2) GeneralForm)
             (FinScBox.Box.singletonMaxelEdge FZ FZ (MkBoxInt 2) <+>
              FinScBox.Box.singletonMaxelEdge FZ (FS FZ) (MkBoxInt (-3)) <+>
              FinScBox.Box.singletonMaxelEdge (FS FZ) FZ (MkBoxInt 5))
       v = the (Box BoxInt (Fin 2)) (FinScBox.Box.setBox (FS FZ) (MkBoxInt 4) (FinScBox.Box.singletonBox FZ (MkBoxInt 10)))
       r = FinScBox.Box.actMaxelR m v
   in (FinScBox.Box.lookupBox FZ r == MkBoxInt 8) &&
      (FinScBox.Box.lookupBox (FS FZ) r == MkBoxInt 50)) = True
prfBoxCoreActMaxelR = Refl

public export
0 prfBoxCoreExchangeQuadraticSymmetry :
  (let rPos = FinScBox.QuadraticExchange.exchangeQuadratic (MkBoxInt 7) (MkBoxInt 100) (MkBoxInt (-43)) (MkBoxInt 80)
       rNeg = FinScBox.QuadraticExchange.exchangeQuadratic (MkBoxInt 7) (MkBoxInt (-100)) (MkBoxInt 43) (MkBoxInt (-80))
   in (rNeg.valA == negBox rPos.valA) &&
      (rNeg.valB == negBox rPos.valB) &&
      (rNeg.valU == negBox rPos.valU)) = True
prfBoxCoreExchangeQuadraticSymmetry = Refl

public export
0 prfBoxCoreMaxelHalfStorage :
  (let a     = the (Space 2) [0, 0]
       b     = the (Space 2) [1, 0]
       c     = the (Space 2) [0, 1]
       axes2 = the (Box MultisetBit (Fin 2)) (FinScBox.Box.setBox (FS FZ) OneBit (FinScBox.Box.singletonBox FZ OneBit))
       ae    = FinScBox.Box.singletonMaxelEdge {form = AntisymForm} b a (MkBoxInt 7)
       sq    = ae .*. ae
       st    = the (Box BoxInt (Space 2)) (FinScBox.Box.unitStencilBox (unitSpace {n = 2}) axes2)
       sp    = FinScBox.Box.shiftConvolveMaxel sq st
       dg    = FinScBox.Box.diagEmbedMaxel (FinScBox.Box.singletonBox a (MkBoxInt 5))
       sy    = dg <+> FinScBox.Box.singletonMaxelEdge b a (MkBoxInt 3)
       syA   = sy .*. ae
       gn    = FinScBox.Box.toGeneralMaxel sy .*. ae
       da    = FinScBox.Box.singletonMaxelEdge {form = DiagAntisymForm} a a (MkBoxInt 5) <+>
               FinScBox.Box.singletonMaxelEdge b a (MkBoxInt 7)
       daSt  = FinScBox.Box.shiftConvolveMaxel da st
       pB    = FinScBox.Box.addAtKeyBox b (MkBoxInt 2) (FinScBox.Box.singletonBox a (MkBoxInt 1))
       sB    = FinScBox.Box.singletonBox a (MkBoxInt 1)
       bx    = FinScBox.Box.singletonBox b (MkBoxInt 4)
       hm    = FinScBox.HereditaryMSet.scalarKeyHMSet 3
       (pY, pN) = FinScBox.Box.partitionBox (== a) pB
   in (FinScBox.Box.lookupMaxel b a ae == MkBoxInt 7) &&
      (FinScBox.Box.lookupMaxel a b ae == MkBoxInt (-7)) &&
      (FinScBox.Box.maxelNodeCount ae == 1) &&
      (FinScBox.Box.traceMaxel ae == MkBoxInt 0) &&
      (FinScBox.Box.transposeMaxel ae == FinScBox.Interfaces.negM ae) &&
      (FinScBox.Box.lookupMaxel a b sq == MkBoxInt 49) &&
      (FinScBox.Box.lookupMaxel b a sq == MkBoxInt 49) &&
      (FinScBox.Box.maxelNodeCount sq == 1) &&
      (FinScBox.Box.transposeMaxel sq == sq) &&
      FinScBox.Box.isSymMaxel sq &&
      (FinScBox.Box.maxelNodeCount sp == 4) &&
      (FinScBox.Box.lookupMaxel b (the (Space 2) [2, 0]) sp == MkBoxInt 49) &&
      (FinScBox.Box.traceMaxel dg == MkBoxInt 5) &&
      ((sy <.> sy) == (FinScBox.Box.toGeneralMaxel sy <.> FinScBox.Box.toGeneralMaxel sy)) &&
      ((ae <.> ae) == (FinScBox.Box.toGeneralMaxel ae <.> FinScBox.Box.toGeneralMaxel ae)) &&
      (FinScBox.Box.toGeneralMaxel syA == gn) &&
      (FinScBox.Box.lookupMaxel b a syA == MkBoxInt 21) &&
      (FinScBox.Box.lookupMaxel a b syA == MkBoxInt (-21)) &&
      ((FinScBox.Interfaces.scaleM (MkBoxInt 2) sy <.> sy) == MkBoxInt 86) &&
      ((FinScBox.Interfaces.subM sy sy == FinScBox.Interfaces.zeroM)) &&
      ((FinScBox.Interfaces.addM bx (FinScBox.Interfaces.negM bx) == FinScBox.Interfaces.zeroM)) &&
      ((bx <.> bx) == MkBoxInt 16) &&
      ((hm <.> hm) == MkBoxInt 9) &&
      (FinScBox.Interfaces.subM (FinScBox.Interfaces.addM hm hm) hm == hm) &&
      ((sy <.> FinScBox.Box.singletonMaxelEdge c a (MkBoxInt 1)) == MkBoxInt 0) &&
      (FinScBox.Box.lookupMaxel a a da == MkBoxInt 5) &&
      (FinScBox.Box.lookupMaxel b a da == MkBoxInt 7) &&
      (FinScBox.Box.lookupMaxel a b da == MkBoxInt (-7)) &&
      (FinScBox.Box.traceMaxel da == MkBoxInt 5) &&
      (FinScBox.Box.maxelNodeCount da == 2) &&
      (FinScBox.Box.transposeMaxel (FinScBox.Box.transposeMaxel da) == da) &&
      (FinScBox.Box.toGeneralMaxel (FinScBox.Box.transposeMaxel da) ==
         FinScBox.Box.transposeMaxel (FinScBox.Box.toGeneralMaxel da)) &&
      ((da <.> da) == MkBoxInt 123) &&
      ((da <.> da) == (FinScBox.Box.toGeneralMaxel da <.> FinScBox.Box.toGeneralMaxel da)) &&
      (FinScBox.Box.toGeneralMaxel (da .*. da) == (FinScBox.Box.toGeneralMaxel da .*. FinScBox.Box.toGeneralMaxel da)) &&
      (FinScBox.Box.toGeneralMaxel (sy .*. da) == (FinScBox.Box.toGeneralMaxel sy .*. FinScBox.Box.toGeneralMaxel da)) &&
      (FinScBox.Box.toGeneralMaxel (ae .*. da) == (FinScBox.Box.toGeneralMaxel ae .*. FinScBox.Box.toGeneralMaxel da)) &&
      (FinScBox.Box.maxelNodeCount daSt == 8) &&
      (FinScBox.Box.lookupMaxel b b daSt == MkBoxInt 5) &&
      (FinScBox.Box.lookupMaxel b (the (Space 2) [2, 0]) daSt == MkBoxInt (-7)) &&
      (FinScBox.Box.diagBox da == FinScBox.Box.singletonBox a (MkBoxInt 5)) &&
      (pY == sB) &&
      (FinScBox.Box.maskOutBox sB pB == pN) &&
      (FinScBox.Box.maskByBox pB sB == sB) &&
      (FinScBox.Box.supportBox pB == FinScBox.Box.setBox b (MkBoxInt 1) sB)) = True
prfBoxCoreMaxelHalfStorage = Refl

public export
0 prfBoxCoreConsolidatedAlgebra :
  (let axM = FinScBox.Box.setBox (FinScBox.HereditaryMSet.scalarKeyHMSet 2) OneBit
               (FinScBox.Box.singletonBox (FinScBox.HereditaryMSet.scalarKeyHMSet 1) OneBit)
       uM  = the (Box BoxInt PureMultiset) (FinScBox.Box.unitStencilBox id axM)
       ch  = FinScBox.Views.splitChannels FinScBox.BlackRedZoom.sampleUnitPairMSet
       out = FinScBox.HereditaryMSet.outerHMSet (FinScBox.HereditaryMSet.scalarKeyHMSet 2) (FinScBox.HereditaryMSet.scalarKeyHMSet 3)
   in (FinScBox.Box.totalMassBox uM == MkBoxInt 4) &&
      FinScBox.Views.disjointDualSupports ch &&
      (FinScBox.Views.interactChannels ch == FinScBox.BlackRedZoom.sampleUnitPairMSet) &&
      (FinScBox.HereditaryMSet.sumHMSet out == MkBoxInt 6)) = True
prfBoxCoreConsolidatedAlgebra = Refl

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

public export
0 prfBoxCoreGohSpreadPolyAlgebra :
  (let z2   = FinScBox.HereditaryMSet.spreadZHMSet 2
       z4   = FinScBox.HereditaryMSet.spreadZHMSet 4
       psi4 = FinScBox.HereditaryMSet.divExactPolyHMSet z4 z2
   in (psi4 == (FinScBox.HereditaryMSet.polyX - 2) * (FinScBox.HereditaryMSet.polyX - 2)) &&
      (FinScBox.HereditaryMSet.gohPsiFactor 2 == 4 - FinScBox.HereditaryMSet.polyX) &&
      (z2 * psi4 == z4) &&
      (FinScBox.HereditaryMSet.evalPolyHMSetAt z2 z2 == z4)) = True
prfBoxCoreGohSpreadPolyAlgebra = Refl

public export
0 prfMSetSupportIdempotent :
  let z2 : PureMultiset
      z2 = FinScBox.HereditaryMSet.spreadZHMSet 2
      s2 : PureMultiset
      s2 = FinScBox.HereditaryMSet.castSupportHMSet z2
      px = FinScBox.HereditaryMSet.polyX
  in ((the PureMultiset (FinScBox.HereditaryMSet.castSupportHMSet (the PureMultiset FinScBox.HereditaryMSet.emptyHMSet)) ==
         FinScBox.HereditaryMSet.emptyHMSet) &&
      (FinScBox.HereditaryMSet.castSupportHMSet s2 == s2) &&
      (FinScBox.HereditaryMSet.castSupportHMSet (FinScBox.HereditaryMSet.negHMSet z2) == s2) &&
      (the PureMultiset (FinScBox.HereditaryMSet.castSupportHMSet (3 * px - 5 * px * px)) ==
         FinScBox.HereditaryMSet.castSupportHMSet (px + px * px))) = True
prfMSetSupportIdempotent = Refl

public export
0 prfStreamPeelWorkLaws :
  (let k1  = FinScBox.HereditaryMSet.scalarKeyHMSet 1
       nk1 = FinScBox.HereditaryMSet.negHMSet k1
       smp = FinScBox.BlackRedZoom.sampleUnitPairMSet
   in (FinScBox.Views.streamPeelWorkHMSet (the PureMultiset FinScBox.HereditaryMSet.emptyHMSet) ==
         MkStreamWorkReport 0 0 0) &&
      (FinScBox.Views.fastPeelWorkHMSet smp ==
         (FinScBox.Views.streamPeelWorkHMSet smp).workSteps) &&
      (snd (FinScBox.Views.streamMergeWorkHMSet k1 nk1) ==
         MkStreamWorkReport 2 1 0)) = True
prfStreamPeelWorkLaws = Refl

public export
0 prfCarrierBitsAndQuadraticMonoid :
  (let sbPos  = FinScBox.HereditaryMSet.singletonHMSet FinScBox.HereditaryMSet.emptyHMSet PosBit
       sbNeg  = FinScBox.HereditaryMSet.singletonHMSet FinScBox.HereditaryMSet.emptyHMSet NegBit
       mbOne  = FinScBox.HereditaryMSet.singletonHMSet FinScBox.HereditaryMSet.emptyHMSet OneBit
       z2     = FinScBox.HereditaryMSet.spreadZHMSet 2
       mbRel  = the (HereditaryMSet MultisetBit) (FinScBox.HereditaryMSet.castSupportHMSet z2)
       g7     = FinScBox.QuadraticExchange.pythGeneratorTriple (MkBoxInt 7)
       a      = (ZeroZ, ZeroZ)
       b      = (PosZ 0, ZeroZ)
       mDa    = FinScBox.Box.singletonMaxelEdge {form = DiagAntisymForm} a a (MkBoxInt 6) <+>
                FinScBox.Box.singletonMaxelEdge b a (MkBoxInt 8)
       mOff   = FinScBox.Box.offDiagMaxel mDa
       mClp   = FinScBox.Box.mapPruneMaxel (\w => if w == MkBoxInt 6 then MkBoxInt 0 else w) mDa
       v3     = the (Space 3) [3, -2, 1]
   in ((sbPos <+> sbNeg) == FinScBox.HereditaryMSet.emptyHMSet) &&
      (snd (FinScBox.Views.streamMergeWorkHMSet sbPos sbNeg) == MkStreamWorkReport 2 1 0) &&
      ((mbOne <+> mbOne) == FinScBox.HereditaryMSet.emptyHMSet) &&
      (FinScBox.HereditaryMSet.castSupportHMSet mbRel == the PureMultiset (FinScBox.HereditaryMSet.castSupportHMSet z2)) &&
      (FinScBox.Views.fastPeelWorkHMSet mbRel == (FinScBox.Views.streamPeelWorkHMSet mbRel).workSteps) &&
      ((neutral <+> g7) == FinScBox.QuadraticExchange.pythPowerTriple 1 (MkBoxInt 7)) &&
      ((g7 <+> g7) == FinScBox.QuadraticExchange.pythPowerTriple 2 (MkBoxInt 7)) &&
      FinScBox.Box.isAntisymMaxel mOff &&
      (mClp == mOff) &&
      (FinScBox.Box.sumStoredMaxel mOff == MkBoxInt (-8)) &&
      ((FinScBox.Interfaces.combine v3 (FinScBox.Interfaces.inverse v3)) == FinScBox.Interfaces.origin {k = Space 3}) &&
      (FinScBox.Interfaces.indexSpace (FS FZ) (FinScBox.Interfaces.unitSpace {n = 3} (FS FZ)) == PosZ 0)) = True
prfCarrierBitsAndQuadraticMonoid = Refl
```
