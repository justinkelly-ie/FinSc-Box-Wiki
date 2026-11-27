# FinSc-Box-Wiki

**Literate Idris 2 specifications, QuickCheck property tests, and `QTT 0` proofs for [`FinSc-Box`](../FinSc-Box).**

## Pages

- [`BoxSterlingSpec.md`](Library/Wiki/BoxSterlingSpec.md) — Overview of `FinSc-Box` and full Sterling Definition Audit (Recognition + Equality across every `data`/`record` type).
- [`BoxCoreSpec.md`](Library/Wiki/BoxCoreSpec.md) — Compile-time `QTT 0 Refl` verification of hereditary multisets, AVL `Box`, `Maxel` half-storage, `QuadraticExchange`, codec, `GohBound`, and `paceStreamStep`.
- [`BoxPropertySpec.md`](Library/Wiki/BoxPropertySpec.md) — QuickCheck property suite over `BoxInt` cancellation, quadratic exchange conservation, codec round-trips, Black/Red zoom laws, and spread polynumbers.
- [`BoxBench.idr`](Library/Wiki/BoxBench.idr) — Monotonic microbenchmark suite (`--bench`) covering `Box`, `Maxel`, and `HereditaryMSet` hot paths.

## Building & Running

```bash
cd FinSc-Box-Wiki
idris2 --build FinSc-Box-Wiki.ipkg
./build/exec/finsc-box-wiki           # Full QTT 0 + QuickCheck suite
./build/exec/finsc-box-wiki --bench   # Monotonic Box/Maxel/HereditaryMSet microbenchmarks
```

## License

Released under the MIT License.
