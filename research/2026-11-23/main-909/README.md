# L-meta-909 partial-function circuit query

The posted goal asks for a well-formed circuit with at most 6 AND gates, free
OR, at most 2 actual bare-reader gates per variable, and the specified behavior
on all maximal independent sets and their one-vertex extensions. The exact
Petersen instance has 15 negative sets and 100 distinct positive extensions.
This is a partial-function existence goal, not full edge-function equality.

The encoder allows empty/overlapping sides, nested earlier-gate summands,
unused gates and empty output. Output variables are impossible because every
vertex occurs in a negative set. Empty-gate padding covers all sizes at most 6.
A variable selected on both sides of one gate counts only once. Independent
source review and four fixed solver controls passed. The geometry audit and
structural note have their own explicit finite/paper scopes.

The target query finished UNKNOWN at its 300-second bound: 300.482 seconds,
3,639,772 conflicts, and the owned child reaped. The saved result records
exact program, row, CNF and partial-trace hashes. No SAT witness, UNSAT proof,
Lean encoding theorem or official theorem submission follows from this run.
Raw traces/CNF and private assignment state are excluded.

## Portable dependency copy

The archived generic dependency and-count-audit/search.py has one documented
publication transformation: its absolute local ROOT is replaced by
Path(__file__).resolve().parents[1]. Its Encoding/evaluator bodies are unchanged.
The public encoder-dependency.json points to that portable-copy hash and also
records the original runtime hash. Historical reviews, selftests and target
results intentionally retain the original 7fd1133b... runtime hash. No live
source was changed and no new claim of testing the portable copy is made.


## Checked support and submitted reduction

The current r2 reduction source under revisions/r2/ passed Lean compilation,
standard-three-axiom auditing, and a lightweight canonical printer/readback
preflight. Its three child statements have printed lengths 692, 986 and 139,
and all read back to the same expressions. This preflight does not replay the
full official pinned-library checker. The corrected source was officially submitted as upstream PR #4051 at
https://github.com/brilliant-hq/pequalnp-proofs/pull/4051, commit
8292b94e2ba785988092e2b86e675548455140a2. The API verified one file and one commit.
The desk acknowledged the reduced report at 06:20:23 UTC. The frozen official
verdict is PENDING; no full official kernel replay or acceptance is claimed.

AndCountMonotonicity and BasisCompleteness have separate kernel-check and
standard-axiom records. They establish monotone propagation and the exact
finite basis reduction from 100 positive extensions to 70 size-three-row
extensions. The finite circuit-construction child remains unresolved.

The earlier 02e467... source compiled but failed child1 print/readback:
the printed Finset filter was inferred as a Set before .card. Its source,
build record and failure logs are preserved under formal/history/ with status
PREPARED_BUT_ROUNDTRIP_FAILED. The source has a .lean.txt suffix to distinguish
it from the current candidate. The r2 fix adds a typed local Finset binding
and removes the Mathlib umbrella import; the final target is unchanged.

The DirtyTriangle prototype and reuse map under drafts/ are explicitly
DRAFT_UNCHECKED. The prototype imports an outside proof file and is not an
eligible standalone submission under the Mathlib/Defs-only rule. A derived
standalone draft mentioned by the reuse map is not included in this checkpoint.
