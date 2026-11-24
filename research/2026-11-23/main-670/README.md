# L-meta-670 finite circuit research

This directory preserves the original assigned first-AND(4,6) range and later
conditional reductions to a least global 14-gate witness. It does not prove
the full L-meta-670 statement or report range exhaustion.

## Four checked structural helpers

FirstGateReduction, ReaderShape, DegreeThreeShape and RawGateShape passed
local Lean compilation and standard-axiom audits. Their sources, logs and
verification records are in formal/. The exact accepted lower bounds
L-meta-1007 and L-meta-517 are explicit premises. The accepted source terms
were compared, but those dependencies were not locally recompiled/instantiated
in these helpers. The SAT encoding and full scheduling/orbit normalization
remain separately reviewed mathematical/code bridges.

## Completed strengthened query

The all-512-row, arbitrary-NOT query finished UNKNOWN at its 1,800-second wall
bound: 1,801.288 seconds including finalization and 5,798,841 conflicts. The
owned child was reaped. Its result and completed public snapshot retain the
program/CNF hashes and partial-trace hash. The partial trace is not an UNSAT
certificate; raw proofs and CNF files are excluded from this checkpoint.
The earlier frozen running snapshot remains historical.

## Reduced-row follow-up

The frozen CEGAR source retains every reviewed structural clause and begins
with 60 actual rows (3,809 variables; 53,474 clauses). Every sampled-row SAT
model is checked on all 512 inputs before it can be called a witness. Violated
rows are added and a new solver/CNF/proof phase is constructed. Static direct
assignment checks, three fixed solver controls, and exact full-row CNF byte
identity all passed. The root source review passed as well.

The handoff JSON and design note preserve their preparation-time states.
A target CEGAR run was subsequently authorized and started on 2026-11-24 at
05:59:54 UTC. Its live output is deliberately outside this frozen checkpoint;
no result from that ongoing run is asserted here. Sources and control records
are unchanged. See global14-strengthened-public-completeness.txt for exact
premises, orbit/greedy normalization and control scopes.

## Completed reduced-row query

The previously running CEGAR follow-up finished UNKNOWN at its 1,800-second
bound: 1,800.233 seconds, 15,279,371 conflicts, and its owned child reaped.
It remained on the initial 60 rows and produced no sampled SAT candidate or
refinement. The completed snapshot and exact row/phase records retain the
source, row and CNF hashes. Its 1,428,349,151-byte temporary partial trace was
not copied because doing so would breach the configured disk reserve; no
saved trace hash or certificate is claimed. No further solver was started.

The historical preparation/running records above remain unchanged. This
UNKNOWN result does not establish range exhaustion or the parent theorem.

## Separate official reader-profile reduction

The [reader-profile reduction](reduction/README.md) has four closed children
and the exact parent statement as conclusion. Its source, passing local build,
standard-axiom audit, lightweight child readback and independent review are
preserved separately from the finite searches. Official PR provenance and
its pending verdict are recorded in submission/. The remaining children
are not proved by this assembly file.
