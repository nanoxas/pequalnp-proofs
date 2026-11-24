# P vs NP research checkpoint

This branch preserves supporting research, reproducible computations, and local
Lean checks from the collaboration. Official theorem acceptance is recorded by
the [upstream proof repository](https://github.com/brilliant-hq/pequalnp-proofs)
through its proof pull requests and checker verdicts. No accepted upstream
theorem is attributed to this checkpoint.

The [update manifest](research-checkpoints/public-update-manifest.json) records
exact published file hashes. Earlier work remains documented in the
[historical report](research-checkpoints/README.txt).

## Verification status

| Work | Result | Scope |
|---|---|---|
| L-meta-1422 | All ten tables exhausted in the audited circuit model | Solver evidence and full witness evaluation; no formal UNSAT certificate |
| L-meta-1031 | 19 solver cases and two explicit witness audits completed | Restricted small-graph models; the general theorem remains unproved here |
| Five-input certificate pipeline | Complete synthetic AND-of-five theorem passed Lean | Whole generated source checked; separate axiom audit timed out during imports |
| GenericCore and GenericSmoke | Both passed Lean with inline axiom audits | Arbitrary input count and NOT-budget theorem; two-input XOR example; standard axioms only |
| Our L-meta-1421 assembly | Stopped, unverified, and superseded | Another contributor's upstream PR2958 was accepted and merged |

Task-specific work stopped when the corresponding assignments became inactive.
Those stop events alone do not identify a public settlement or its cause.
Operational assignment identifiers and private service links are excluded.

## Completed five-input search: L-meta-1422

Each of the ten tables has a monotone circuit of size M and a definitive UNSAT
result for the full 32-row model with at most one NOT and at most M-1 gates.
In posted order, the sizes are **8, 6, 8, 9, 8, 7, 7, 4, 7, 6**. All 320 witness
rows were independently evaluated. The encoding covers free constants, equal
fanins, unused gates, and the documented complete ordering symmetry.

- [Results and witnesses](main-1422/results-ordered.json)
- [Encoder](main-1422/search.py) and [completeness argument](main-1422/completeness-notes.txt)
- [Exhaustion manifest and independent audit](main-1422/exhaustion-manifest.json)

These computational results support the no-saving conclusion and provide
evidence against the posted negative search claim. Their UNSAT answers do not
carry a Lean or DRAT/LRAT replay. Timestamped status files preserve observations
from the search and make no claim about a current assignment.

## Reusable finite-circuit certificate pipeline

The [package](finite-circuit-certificates/README.md) combines monotone witness
generation, two independently checked Python evaluators, and a generator that
preserves an explicitly supplied public theorem statement.

Its complete synthetic five-input AND theorem, with a four-gate witness and
rejection bound three, passed Lean 4.36.0 with exit 0 in 161.956 seconds. Imports
accounted for 155 seconds. The separate axiom audit stopped at its 180-second
limit before producing an axiom list. Exact hashes and logs are in the
[verification record](finite-circuit-certificates/smoke/lean-verification.json).
Every newly generated target file still requires its own completed Lean check.

The [generic extension](finite-circuit-certificates/GENERIC.md) parameterizes
input count and NOT budget. Its corrected core passed in 13.671 seconds; the
two-input XOR example with a NOT budget of two passed in 2.421 seconds. All
five audited theorems use exactly `propext`, `Classical.choice`, and `Quot.sound`.
The [verification record](finite-circuit-certificates/generic-verification.json)
preserves earlier import timeouts and ordinary elaboration errors as history.
The five-input generator and its separate axiom-audit status remain unchanged.

The five-input engine preserves the accepted L-meta-1445 proof body, which
credits L-meta-1007. The package retains its Apache-2.0 license, attribution,
notices, and exact source hashes.

## Ownership diagnostics: L-meta-1031

The [stopped-research report](main-1031/STOP_REPORT.md) records all 19 completed
solver cases and two direct witness audits. Its model restrictions are
explicit. A four-gate path example shows that an edge may be critical for a
gate without being owned by it. The missing general step is a size-preserving
exchange controlling empty or nonstar ownership in minimum circuits.

The later compact public snapshot still listed the problem as open. That
observation does not establish why the assignment ended. No task proof was
submitted from this research.

## Upstream acceptance and local drafts

Our L-meta-1421 candidate never completed its Lean check. The independent
[upstream PR2958](https://github.com/brilliant-hq/pequalnp-proofs/pull/2958),
by Vkuparin, was accepted and merged on 24 November 2026 at 00:17:59 UTC. The
[acceptance comment](https://github.com/brilliant-hq/pequalnp-proofs/pull/2958#issuecomment-7117912128)
and merged PR establish the settlement. Our [local status](main-1421/STATUS.json)
remains superseded and unverified.

Earlier L-meta-1407 work yielded six checked reusable components. Its full
assembly remained unfinished. Another contributor's
[upstream PR2889](https://github.com/brilliant-hq/pequalnp-proofs/pull/2889)
had already been accepted. Our closed
[fork draft](https://github.com/nanoxas/pequalnp-proofs/pull/1)
did not trigger the official checker or an Actions run.

## Import bottleneck

The [import note](infra-lean/IMPORT_BOTTLENECK.md) and
[run evidence](infra-lean/import-evidence.json) distinguish module loading from
proof work. Reduced imports completed quickly in several generic tests; later
complete checks spent most or all of their limits loading mapped files. The
evidence does not establish a precise historical memory-limit cause.

A subsequent [header-reuse experiment](infra-lean/header-reuse/REPORT.md) saved
the import-only environment in 17.932 seconds and successfully reused it for
the generic proof check. The exact-header and fixed-dependency assumptions,
commands, source fixes, and bounded-run history are recorded. Binary caches
and raw process details are excluded from this public update.

## Earlier preserved work

The historical checkpoint also records the completed L-meta-1418 computational
search; Lean-checked ladder support, first-dirty-AND witnesses, dyadic inverter
semantics, and clean-count components; and finite audits of several structural
constructions. Their assumptions and formalization boundaries remain explicit.
None is claimed to resolve P versus NP.

## One-NOT refund research: L-meta-997

The [research checkpoint](main-997/README.md) now contains twenty-six kernel-checked
modules with standard-axiom audits. Nine additional modules establish the
deficiency budget: directed separation leaves at most two deficient private
classes, and OR compensation plus private AND counts pays their deficits.
The exact inequality follows when the heavy excess Eplus is at most 4|Y|−3
for |Y|≥3; the earlier SmallWindow theorem covers |Y|≤2. All seventeen
previously published Lean source files remain unchanged. The unrestricted
L-meta-997 statement remains unproved here.

The [reviewed small-surplus argument](main-997/saturation-small-surplus-audit.txt)
extends the paper sufficient criterion to Q≤H+k+e+2 for every k=|Y|≥2,
including pair outputs. Its complete gate classification is not yet a Lean
theorem. The earlier PG(2,4) audit remains preserved.

The thirteen-input family has a complete Python baseline/data audit and a
reviewed support-based exclusion; it also meets checked sufficient criteria.
The exceptional-support and deficiency notes identify the checked chain
through Eplus≤4|Y|−3 and retain the stronger global OR/AND dichotomy as paper
research. A new [overlap audit](main-997/overlap-audit/selection-obstruction.txt)
checks four circuits on all 128 input rows each: raw partial-charge overlap
can exceed whole-target refunds, while minimum quota selections are disjoint
in these examples. Their full L-meta-997 inequalities hold.

The sole 49-gate finite solver query remains INTERRUPTED_UNKNOWN; no candidate
or UNSAT result was observed, and its original child cleanup is unconfirmed.
Corrected runner cleanup passed five dummy-only lifecycle checks.

The [checkpoint status](main-997/checkpoint-status.json) separates these
results. A fresh public-text comparison and checked definitional equality
also preserve the exact guarded refund predicate after correcting a failed
helper transcription. No target-specific theorem was submitted from this
checkpoint.
