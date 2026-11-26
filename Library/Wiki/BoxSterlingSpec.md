# Sterling Definitions in `FinSc-Box`

`FinSc-Box` is the **Layer 1** algebraic core of the stack: a domain-free Idris 2 library providing balanced signed/ternary/parity multiplicity weights (`BoxInt`, `SignedBit`, `MultisetBit`), coordinate-indexed height-cached AVL containers (`Box c k`), recursive hereditary multisets (`HereditaryMSet c` and `PureMultiset`), symmetry-compressed 2-index matrices (`Maxel c a b form`), conservative quadratic triples (`QuadraticTriple`), streaming peel-work views (`AntiBoxView`, `DualChannelView`), and horizon freeze-out types (`Time`, `GohBound`, `SolidifiedStream`).

Following Norman J. Wildberger's standard in *Rebuilding Pure Mathematics*, a mathematical definition is **sterling** when every candidate object supplies:
1. **Recognition** — an explicit terminating procedure deciding whether a finite expression is a legitimate representative (for example, AVL balance, strict BST key order, zero-pruning, or half-storage bounds), and
2. **Equality** — an explicit terminating procedure (`Eq`) deciding whether two admissible expressions represent the same mathematical object (independent of insertion history or internal tree rotation).

```idris
module Wiki.BoxSterlingSpec

import FinScBox

%default total
```

## Sterling Definition Audit Table (`FinSc-Box`)

| Type | Module & Definition | Sterling? | Recognition, Equality & Rationale |
| :--- | :--- | :--- | :--- |
| `BoxInt` | `FinScBox.BoxInt` — `record BoxInt (value : Integer)` | **Yes** | Every `Integer` is valid (`True`); `Eq BoxInt` compares `value` directly. |
| `SignedBit` | `FinScBox.Interfaces` — `ZeroBit \| PosBit \| NegBit` | **Yes** | Finite 3-constructor inductive type; structural `Eq SignedBit`. |
| `MultisetBit` | `FinScBox.Interfaces` — `EmptyBit \| OneBit` | **Yes** | Finite 2-constructor inductive type ($\mathbb{Z}_2$ support); structural `Eq MultisetBit`. |
| `SignedCoord` | `FinScBox.Interfaces` — `ZeroZ \| PosZ Nat \| NegZ Nat` | **Yes** | Canonical unique zero (`ZeroZ`); structural `Eq SignedCoord`. |
| `Space n` | `FinScBox.Interfaces` — `Nil \| (::) SignedCoord (Space n)` | **Yes** | Length-indexed vector of `SignedCoord`; componentwise `Eq (Space n)`. |
| `Box c k` | `FinScBox.Box` — `BoxLeaf \| BoxNode Nat (Box c k) k c (Box c k)` | **Yes** | **Recognition:** `checkBoxBoundsBy` (non-zero weights, exact height cache, AVL balance, strict key order). **Equality:** `structuralBoxTreeEqual` (`BoxZipper` in-order scan ignoring tree shape). |
| `MaxelForm a b` | `FinScBox.Box` — `GeneralForm \| SymForm \| AntisymForm \| DiagAntisymForm` | **Yes** | Finite 4-constructor symmetry family; `eqMaxelForm` / `Eq (MaxelForm a b)`. |
| `MaxelFormTag form` | `FinScBox.Box` — singleton runtime witness for `MaxelForm` | **Yes** | Indexed singleton for known `form`; `Eq (MaxelFormTag form)`. |
| `Maxel c a b form` | `FinScBox.Box` — `record Maxel (rawMaxelBox : Box c (a, b))` | **Yes** | **Recognition:** `isCanonicalMaxel` (`checkBoxBoundsBy` + half-storage `x <= y` or `x < y`). **Equality:** `Eq (Maxel c a b form)` on canonical half-storage. |
| `HereditaryMSet c` (`PureMultiset`) | `FinScBox.HereditaryMSet` — `MkHMSet (Box c (HereditaryMSet c))` | **Yes** | **Recognition:** `isCanonicalHMSet` / `recognizeCanonicalHMSet`, plus `recognizePureMultisetText` for bracket syntax. **Equality:** recursive depth-bounded `compareHMSet`. |
| `GohBound cap` | `FinScBox.HereditaryMSet` — `record GohBound (boundSteps : Nat)` | **Yes** | Finite `Nat` yield bound; `Eq (GohBound cap)`. |
| `AnyGohBound` | `FinScBox.HereditaryMSet` — `MkAnyGohBound (cap : Nat) (bound : GohBound cap)` | **Yes** | Dependent pair of finite `Nat` values; `Eq AnyGohBound`. |
| `SupportStats` | `FinScBox.HereditaryMSet` — `(nnz, totalMass, maxDeg : Nat)` | **Yes** | Triple of `Nat` metrics; structural `Eq SupportStats`. |
| `Time` | `FinScBox.HereditaryMSet` — 6-way horizon classifier | **Yes** | Finite sum over `BoxInt`/`Nat` bounds; `Eq Time`. |
| `StreamStep a` | `FinScBox.HereditaryMSet` — `StreamDone \| StreamSkip \| StreamYield a` | **Yes** | Sterling whenever `a` has `Eq` (`Eq a => Eq (StreamStep a)`). |
| `StreamFreezeReason` | `FinScBox.HereditaryMSet` — 3-way freeze outcome | **Yes** | Finite 3-constructor enumeration; `Eq StreamFreezeReason`. |
| `SolidifiedStream t cap a` | `FinScBox.HereditaryMSet` — 7-field static freeze relic | **Yes** | Sterling whenever `a` has `Eq`: all 7 fields checked in `Eq` (`remainingYield` & `remainingSteps` included). |
| `AntiBoxView c` | `FinScBox.Views` — `EmptyVacuum \| PopBlackBox \| PopRedBox` | **Yes** | Tagged view over `HereditaryMSet c`; `MultisetWeight c => Eq (AntiBoxView c)`. |
| `DualChannelView c` | `FinScBox.Views` — `(posChannel, negChannel : HereditaryMSet c)` | **Yes** | **Recognition:** `isCanonicalDualChannels` (canonical + `disjointDualSupports`). **Equality:** `Eq (DualChannelView c)`. |
| `StreamWorkReport` | `FinScBox.Views` — `(workSteps, annihilations, residualL1 : Nat)` | **Yes** | Triple of `Nat` counters; `Eq StreamWorkReport`. |
| `QuadraticPairResult` | `FinScBox.QuadraticExchange` — `(valA, valB, valU : BoxInt)` | **Yes** | Triple of `BoxInt` values; `Eq QuadraticPairResult`. |
| `QuadraticTriple` | `FinScBox.QuadraticExchange` — `(qtA, qtB, qtR : BoxInt)` | **Yes** | **Recognition:** `isQuadraticTriple` (`qtR > 0 && qtA^2 + qtB^2 == qtR^2`). **Equality:** componentwise `Eq QuadraticTriple`. |
| `TimeStream t a` | `FinScBox.HereditaryMSet` — `(startTick : Nat, stepAt : Nat -> StreamStep a)` | **No (Procedure)** | Wraps an unbounded generating procedure `Nat -> StreamStep a`; extensional equality over all `Nat` is not finitely decidable until frozen into a `SolidifiedStream`. |
| `ExternalLens src out` | `FinScBox.Lenses` — `(focus, spaceShift, timeShift, project)` | **No (Procedure)** | Bundles projection functions `src -> PureMultiset` and `PureMultiset -> out`. |
| `PureObservation uIn out` | `FinScBox.Lenses` — linear `1 uOut` witness with `0 same` | **No (Linear Handle)** | QTT `1` linear non-interference wrapper certifying read-only inspection (`uOut = uIn`); equality applies to its extracted value `val : out`. |

## Compile-Time `QTT 0` Sterling Verification

The checks below run during typechecking (`QTT 0`) and confirm recognition, tree-shape independence of `Eq (Box c k)`, rejection of ill-formed half-storage `Maxel`s and non-Pythagorean triples, and sensitivity of `Eq SolidifiedStream` to `remainingSteps`:

```idris
public export
0 prfBoxSterlingSuite :
  (let bOrder1 : Box BoxInt Nat
       bOrder1 = setBox 2 5 (setBox 1 3 (setBox 3 7 BoxLeaf))
       bOrder2 : Box BoxInt Nat
       bOrder2 = setBox 3 7 (setBox 1 3 (setBox 2 5 BoxLeaf))
       mGood   = singletonMaxelEdge {form = AntisymForm} (the Nat 3) 1 (MkBoxInt 9)
       mBad    = MkMaxel {form = AntisymForm} (singletonBox (the Nat 3, the Nat 1) (MkBoxInt 9))
       qtGood  = pythGeneratorTriple 7
       qtBad   = MkQuadraticTriple 2 3 4
       smp     = sampleUnitPairMSet
       dc      = splitChannels smp
       s1      = MkSolidifiedStream {frozenTime = StaticTime 0 1, cap = 1}
                   (MkBoxInt 1) NaturalCompletion 1 0 1 (MkGohBound 1) 4
       s2      = MkSolidifiedStream {frozenTime = StaticTime 0 1, cap = 1}
                   (MkBoxInt 1) NaturalCompletion 1 0 1 (MkGohBound 1) 5
   in (bOrder1 == bOrder2) &&
      isJust (checkBoxBoundsBy (\_ => True) bOrder1) &&
      isCanonicalMaxel mGood &&
      not (isCanonicalMaxel mBad) &&
      isQuadraticTriple qtGood &&
      not (isQuadraticTriple qtBad) &&
      isCanonicalHMSet smp &&
      isCanonicalDualChannels dc &&
      (interactChannels dc == smp) &&
      (viewAsAntiBox smp == viewAsAntiBox smp) &&
      not (s1 == s2)) = True
prfBoxSterlingSuite = Refl
```
