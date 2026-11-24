# Lean import bottleneck

The [run summary](import-evidence.json) records bounded local tests. Default
startup finished in 1.622 s; a Finset import in 7.073 s; the reduced six-import
smoke in 6.403 s; and the representative BitVec/simp/omega/aesop smoke in 2.931 s.
The complete synthetic certificate proof passed in 161.956 s, with 155 s spent
on imports. Its separate axiom audit and an initial GenericCore run each reached
their 180-second limits during imports and were terminated and reaped.

The pinned Lean loader maps main `.olean`, `.olean.server`, `.olean.private`,
and IR parts. Counting main objects alone understates its workload. One
reduced-import observation mapped about 3.08 GiB of these parts and held more
than 2.4 GiB resident. RSS and address-space rlimits were unlimited; the sandbox
did not mount cgroup controls, so their ceilings could not be inspected.

Slow runs had large physical-read and major-fault counters while ordinary
read-call byte counts remained much smaller. That is consistent with demand
paging of mapped files. The measurements do not identify a precise historical
cause of cache pressure. Host MemAvailable is not proof of a process limit.

Use the smallest sufficient permitted imports, one Lean worker, profiling,
source hashes, and explicit deadlines. Preserve proof-check and axiom-audit
statuses separately. Inline axiom queries in a check-only copy can avoid a
second import. Keep the contribution source fixed during checking.

`bounded_check.py` records telemetry and supports a stop-file request, allowing
the compiler to be terminated and reaped before the slot is reused. This public
summary omits process inventories and operational account information.

Pinned implementation references:

- [Module loader](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/library/module.cpp)
- [Compacted-region reader](https://github.com/leanprover/lean4/blob/611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9/src/runtime/compact.cpp)

## Subsequent successful header reuse

The [focused follow-up](header-reuse/REPORT.md) saved an import-only snapshot
in 17.932 seconds. The corrected generic engine then passed with this cache
in 13.671 seconds, and the dependent two-input example passed in 2.421 seconds
by normal import of the produced object. All five inline axiom audits listed
only the standard axioms. The earlier incomplete runs remain historical
records; the current generic status is PASS. The cache preserves a working
local check path without establishing a historical memory cause.
