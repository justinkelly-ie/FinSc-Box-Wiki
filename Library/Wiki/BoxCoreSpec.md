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
  let pass = normZero && isCan && spreadOk && codecOk && zoomOk && lensOk
  putStrLn ("  - Vacuum norm=0, canonical=True, spread=3/4, codec=" ++ show codecOk ++ ", zoom=" ++ show zoomOk ++ ", lens=" ++ show lensOk ++ " -> pass=" ++ show pass)
  pure pass
```
