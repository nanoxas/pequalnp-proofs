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

The [research checkpoint](main-997/README.md) contains twenty-nine kernel-checked
modules with standard-axiom audits. The numerical sufficient range remains
Eplus≤4|Y|−3 for |Y|≥3, with |Y|≤2 covered separately. Three new modules check
arbitrary boundary evaluation, the global private OR/AND alternative, and
the stronger weighted bound ≤N+m whenever at most one heavy private class
is deficient. Any failure of the exact refund inequality therefore requires
at least two deficient heavy C1 classes. All twenty-six previously published
Lean sources remain unchanged. The unrestricted statement remains open.

The [quota audit](main-997/quota-audit/selection-obstruction.txt) rules out
several auxiliary matching claims. Its 17-input and 19-input examples have
complete original truth-table checks. The 301-input affine example and
23-input extension use exact required rows plus exhaustive abstract Boolean
identities; their original truth tables are not enumerated. Every example
satisfies L-meta-997. The 19-input residual obstruction was independently
checked on all 524,288 rows with a separate vector evaluator.

The [cross-window note](main-997/cross-window/activation-clauses.txt) retains a
fixed activation frontier against every negative input of the NOT predecessor.
Its clause-refinement consequence remains paper work, with shared global
accounting open. Earlier finite overlap, geometry, and saturation notes remain
preserved with their individual verification scopes. The historical PG4 solver
query remains INTERRUPTED_UNKNOWN and its original child cleanup unconfirmed.

The [checkpoint status](main-997/checkpoint-status.json) separates those
results and retains the exact guarded refund predicate and corrected-helper
history. This research checkpoint makes no unrestricted theorem submission.

## Finite first-gate search snapshot: L-meta-670

The [assigned statement](main-670/statement.txt) and
[complete encoding notes](main-670/completeness-notes.txt) preserve the original
first-AND(4,6) search range: at most 15 AND/OR/NOT gates on nine inputs, with
arbitrary NOT count and all 512 assignments. The false sentinel, invalid-read
normalization, equal fanins, unused gates, and padding are explicit.

The [self-test](main-670/selftest.json) covers 160 normalized circuits and
fixed-formula SAT/UNSAT fixtures. A second source review found no issue in the
bound-15 model. The fixed [status snapshot](main-670/status-snapshot.json) is
RUNNING_UNRESOLVED at its recorded time, with no candidate, exhaustion claim,
or checked proof certificate. These files preserve that assigned range and
historical snapshot; they make no assertion about current desk availability.
Raw solver proofs, CNF files, process state, and private assignments are excluded.

## L-meta-997 handoff

The desk accepted a missing-lemma report on 2026-11-24 at 05:04 UTC.
The [handoff](main-997/README.md#handoff-after-the-missing-lemma-report)
preserves twenty-nine unchanged checked helper modules, the exact open joint
deletion inequality, a reviewed OR-normalization argument, and a symbolic
counterexample to a restricted eligible-pool shortcut. The full theorem
remains open. This supporting research publication is not an upstream proof
submission or an accepted theorem.
