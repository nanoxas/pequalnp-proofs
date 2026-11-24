# Reusing Lean's import header

The pinned Lean 4.36.0 build successfully saved and reused an import-only
snapshot. This let the generalized finite-circuit engine reach ordinary proof
diagnostics, after earlier runs had exhausted their limits while importing.
The corrected engine and its two-input XOR example both passed local Lean
checks, including inline axiom audits.

## Recorded results

| Step | Result | Wall time |
|---|---|---:|
| Save the exact six-import header | PASS | 17.932 s |
| Check the original generic draft with the snapshot | Ordinary elaboration errors: missing equality decisions | 6.143 s |
| Check the corrected generic engine with the snapshot | PASS, object produced | 13.671 s |
| First dependent smoke attempt | Ordinary error in the local equality proof's parameterized constructor case | 9.588 s |
| Corrected dependent smoke | PASS, object produced | 2.421 s |

Every child process completed and was reaped. The initial experiment had a
600-second total deadline. The two corrected checks and the intermediate
smoke attempt each used a 180-second bound. Only one compiler ran at a time.
The bounded wrapper's maximum was deliberately extended from 180 to 600
seconds for this experiment; the ordinary default remains 45 seconds.

The final `cost`, `cost_countP`, `cost_oneNot`, `xor_lower`, and `xor_upper`
axiom lists are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The current hashes and logs are in the
[generic verification record](../../finite-circuit-certificates/generic-verification.json).
The [sanitized experiment record](verification.json) retains prior failures as
history. The separate, earlier five-input synthetic theorem's axiom-audit
timeout remains recorded in its own verification file.

## Source changes

`cost_countP` now takes an explicit `DecidableEq GateOp` parameter. Its Boolean
count agrees with the existing `isNot` count by cases on the gate operation.
The smoke module supplies a local computable structural equality, including
natural-number equality for the `mod` constructor. The executable search,
256-bit samples, main `cost` interface, and XOR circuit witness are unchanged.

The checked smoke uses two inputs and a budget of two NOT gates. It proves
that XOR needs at least four gates and exhibits four gates using one NOT.
This validates the new arity and budget parameters in a concrete example.
Every future generated theorem still needs its own completed check.

## Reproduction

In the workspace layout expected by `bounded_check.py`, create the cache from
the supplied import-only file:

```sh
python3 infra-lean/bounded_check.py \
  infra-lean/header-reuse/ImportHeader.lean \
  --seconds 600 --label HeaderSave --import-workers 1 \
  --incr-header-save infra-lean/header-reuse/six-imports.snap
```

Check the generic engine using that cache:

```sh
python3 infra-lean/bounded_check.py \
  finite-circuit-certificates/GenericCore.lean \
  --seconds 180 --label GenericCoreCachedFixed --import-workers 1 \
  --incr-load infra-lean/header-reuse/six-imports.snap --object
```

After the core passes, check the dependent example:

```sh
python3 infra-lean/bounded_check.py \
  finite-circuit-certificates/GenericSmoke.lean \
  --seconds 180 --label GenericSmokeFixed2 --import-workers 1 --object
```

`GenericSmoke` has a different import header, so its check imports the produced
`GenericCore` object normally. The original one-off coordinator is retained
as `run_experiment.py`; its guards require a fresh prepared state and it stops
at the first failed stage. The commands above reproduce the corrected checks.

## Cache assumptions and interpretation

The cache contains the post-import environment. The source's first six import
lines match `ImportHeader.lean` byte for byte. Keep the snapshot and its `.deps`
companion together, and retain the same pinned Lean build, dependency objects,
plugin configuration, search paths, and relevant options. Recreate the cache
after those or the import header change. Header matching includes source
information, so changing leading text or import positions can invalidate reuse.

The snapshot was 127,090,577 bytes; its SHA256 was
`4a4cd895d91e057d533593f17a94ecff4e3b89ab5354d6f9b75700558a5d8929`.
The binary snapshot, dependency-path manifest, compiled objects, and raw
process/environment inventories are omitted from this public update.

Lean labels the snapshot flags experimental. Its implementation describes
initializer-reexecution assumptions. No runtime inconsistency was observed,
and proof errors were reported normally. Local checking remains separate
from the project's official checker and acceptance process.

These are different runs with different cache states. Their timings establish
a working reuse path, without isolating an exact speedup or identifying the
historical cause of memory or page-cache pressure.

## Pinned implementation references

- [Header snapshot save/load and main-module rebinding](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Lean/Elab/Frontend.lean)
- [Header comparison and truncation](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Lean/Language/Lean.lean)
- [Initializer reuse](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/Lean/Compiler/InitAttr.lean)
