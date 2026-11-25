# FinSc-Box QuickCheck Property Specification

This literate specification tests invariants of **FinSc-Box** across hundreds of pseudo-randomly
generated scalars, coordinates, and hereditary multisets.

```idris
module Wiki.BoxPropertySpec

import QuickCheck
import FinScBox

%default total
```

## 1. QuickCheck Invariants

### Property 1: BoxInt Ring Inverse Cancellation
For any integer scalar $a$, $a + (-a) \equiv 0$:

```idris
public export
prop_boxIntNegCancel : Integer -> Bool
prop_boxIntNegCancel a =
  let b = MkBoxInt a
  in (b + negate b) == MkBoxInt 0
```

### Property 2: Conservative Quadratic Exchange Invariants
For any state `(pA, pB, u)` and derived generator $m = 2 + |p_A + p_B| \ge 2$, `exchangeQuadratic` conserves the linear sum `pA + pB` identically and monotonically bounds `2 * (pA^2 + pB^2) + u^2`:

```idris
public export
prop_quadraticExchangeConserves : Integer -> Integer -> Integer -> Bool
prop_quadraticExchangeConserves pA pB u =
  let m  = MkBoxInt (2 + abs (pA + pB))
      r  = exchangeQuadratic m (MkBoxInt pA) (MkBoxInt pB) (MkBoxInt u)
      a1 = unwrapBox r.valA
      b1 = unwrapBox r.valB
      u1 = unwrapBox r.valU
      q0 = 2 * (pA * pA + pB * pB) + u * u
      q1 = 2 * (a1 * a1 + b1 * b1) + u1 * u1
  in (a1 + b1 == pA + pB) && (q1 <= q0)
```

### Property 3: Canonical Multiset Codec Parity & Round-Trip
For any signed scalar Laurent shift $n$, `renderPureMultiset` matches `Show` verbatim, passes the total `Dec` text recognizer, and parses back to the identical canonical `PureMultiset`:

```idris
public export
prop_codecScalarRoundTrip : Integer -> Bool
prop_codecScalarRoundTrip n =
  let m   = scalarKeyHMSet n
      txt = renderPureMultiset m
  in (txt == show m) &&
     isValidPureMultisetText txt &&
     (case parsePureMultiset txt of
        Just m' => m' == m
        Nothing => False)
```

### Property 4: Black/Red Zoom Time & Space Exact Round-Trip
For bounded Black/Red shifts $k \bmod 5$, opposite shifts annihilate to `[]` and both `zoomTime` and `zoomSpace` invert cleanly back to `sampleUnitPairMSet`:

```idris
public export
mod5 : Nat -> Nat
mod5 (S (S (S (S (S k))))) = mod5 k
mod5 r                     = r

public export
prop_blackRedZoomRoundTrip : Nat -> Bool
prop_blackRedZoomRoundTrip n =
  let k = mod5 n
  in (addHMSet (blackShift k) (redShift k) == emptyHMSet) &&
     (zoomTime  (redShift k) (zoomTime  (blackShift k) sampleUnitPairMSet) == sampleUnitPairMSet) &&
     (zoomSpace (redShift k) (zoomSpace (blackShift k) sampleUnitPairMSet) == sampleUnitPairMSet)
```

### Property 5: Homogenized PureMultiset Spread Polynomial Matches Exact Pythagorean Powers
For any generator $m \ge 2$ and power $y \in \{1..5\}$, the $y$-th Pythagorean triple $(A_y, B_y, R_y) = (A_1 + i B_1)^y$ satisfies $A_y^2 + B_y^2 = R_y^2$ and $R_1^{2y} Z_y(4 B_1^2 / R_1^2) = 4 B_y^2$:

```idris
public export
prop_spreadPolyPythPower : Integer -> Nat -> Bool
prop_spreadPolyPythPower mRaw n =
  let y                       = S (mod5 n)
      m                       = MkBoxInt (if mRaw < 0 then 2 - mRaw else 2 + mRaw)
      MkQuadraticTriple _ b1 r1  = pythPowerTriple 1 m
      MkQuadraticTriple ay by ry = pythPowerTriple y m
  in (ay * ay + by * by == ry * ry) &&
     (evalHomogPolyHMSet y (spreadZHMSet y) (4 * b1 * b1) (r1 * r1) == 4 * by * by)
```

## 2. Dynamic Execution Suite

```idris
public export
auditBoxProperties : IO Bool
auditBoxProperties = do
  putStrLn "  [FinSc-Box-QuickCheck] Core Properties:"
  let r1 = qc prop_boxIntNegCancel
  let r2 = qc3 prop_quadraticExchangeConserves
  let r3 = qc prop_codecScalarRoundTrip
  let r4 = qc prop_blackRedZoomRoundTrip
  let r5 = qc2 prop_spreadPolyPythPower
  let pass = (r1.pass == Just True) &&
             (r2.pass == Just True) &&
             (r3.pass == Just True) &&
             (r4.pass == Just True) &&
             (r5.pass == Just True)
  putStrLn ("  - NegCancel, QuadraticExchangeConserves, CodecRoundTrip, BlackRedZoom, SpreadPolyPythPower (100 tests each) -> pass=" ++ show pass)
  pure pass
```
