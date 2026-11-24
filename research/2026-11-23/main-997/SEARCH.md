# Exact finite counterexample search for L-meta-997

The search fixes a public linear set family, a nonempty set `y`, and a gate
count. It searches for a violation of the exact posted weighted inequality.
It does not claim a proof of the universal theorem or exhaustive coverage
outside its explicitly recorded cases.

The single recorded PG(2,4) query was interrupted and remains **UNKNOWN**.
It produced no candidate and no UNSAT verdict. The final record is
`pg4-run-record.json`: 53,227 variables, 2,437,625 clauses, 272 input rows,
and 1,340,097 conflicts in the last saved solver state. The original runner
did not finalize its cleanup record, so that child's reaping is explicitly
unconfirmed. The subsequent paper argument is independent of this search.

## Current diagnostic case

`pg4-case.json` specifies the 21 lines of the projective plane over GF(4),
viewed as five-element subsets of 21 point inputs. Three collinear points form
`y`. The independent geometry audit is in `pg4/audit.json`; a second count and
truth-vector audit is in `independent-pg4-and-vectors.json`.

There are 13 targets meeting `y` and eight disjoint targets. The posted left
side is `13*3 + 8*5 = 79`. At 49 gates, a violation requires at most eight
refunds. Every disjoint target has a distinct internal output gate satisfying
both refund predicates, so every genuine circuit has at least eight refunds.

This case tests 49 gates only. No 48-gate query or broader family search has
been launched by this script's current run. Earlier candidate families were
removed from consideration by separate mathematical arguments before any
target synthesis runs; those arguments are not assumptions in this encoding.

## Circuit model

Each gate has one of four encoded forms: binary AND, binary OR, unary NOT, or
a costed constant-true gate represented by an empty-input AND. Equal fan-ins
are allowed. Constant false is a free invalid-wire read, matching the posted
list-circuit semantics; it is decoded to an index beyond the entire circuit.
An empty OR is represented by an AND of this false wire with itself. Unary
AND/OR gates use equal fan-ins, and an empty NOT uses the false wire. These
translations preserve each gate's value and the number of NOT gates.

Dead gates and arbitrary output-gate choices are allowed. Every nontrivial
target has size at least two, so its OR function cannot be an input wire or
an invalid output read. The model therefore chooses each output among the
internal gate wires without excluding any circuit for the recorded family.

The model has exactly one NOT. For nonempty `y`, the posted threshold and
false-at-`y` conditions imply that the distinguished gate really is a NOT:
without a preceding NOT the distinguished wire would be monotone, whereas
it is true on the empty input and false at `y`. The premise permits NOTs
only at that distinguished index.

AND/OR fan-ins are ordered. The default model also orders gates by their
largest fan-in index. Any finite DAG can be placed in this order by repeatedly
choosing a ready gate with smallest largest fan-in: previously ready gates
have no smaller key, and newly ready gates read the just-created, larger wire.
The NOT index and output indices are renamed with the gates. Gate functions
and the refund multiset are preserved. `--unordered` disables this second
ordering if an independent comparison is needed.

## Refunds

For every gate, the encoder forms two independent disjunctions:

1. Its singleton-input signature equals one of the target sets.
2. Its signature on `y ∪ {p}`, for `p` outside `y`, equals one of the targets
   disjoint from `y`.

The two matching target indices may differ. A gate is refunded exactly when
both disjunctions hold. No false-at-`y` condition is added to the second
predicate. This matters when a heavy target equals the complement of `y`:
a light output already true at `y` can also satisfy that shifted signature.
The forced-circuit sanity tests include this case and verify two refunds.

Every auxiliary equality is encoded in both directions, and a cardinality
constraint enforces the exact allowable refund count.

The public statement explicitly parenthesizes the complete biconditional
after the implication: `p ∉ y → (value = true ↔ p ∈ S i)`. A fresh public-row
comparison and balanced-parenthesis audit are preserved in
`refund-parse-public-row.json`. This grouping matches the encoder. A helper
transcription briefly omitted the grouping; the posted statement and this
encoder were unchanged.

## Counterexample-guided input rows

The PG(2,4) run starts with 272 assignments:

- All 232 inputs of weight below three.
- The assignment `y`.
- The complements of all 21 target sets.
- The 18 shifted assignments `y ∪ {p}` outside `y`.

All singleton and refund rows are therefore included from the start. A SAT
candidate is evaluated independently on all `2^21 = 2,097,152` inputs using
Python integer bitvectors, with one bit per assignment. A candidate counts
only if all outputs, the NOT window, and the exact refund inequality pass.
Otherwise up to 16 violated output rows are added to the existing SAT solver.

UNSAT at any stage is sound for the complete truth-table problem because
the sampled constraints are necessary conditions. UNKNOWN, interruption,
or a resource limit is recorded separately and is never called exhaustion.

The full truth-vector implementation is checked against a separate scalar
evaluator on small forced circuits. It also verified an 87-gate PG(2,4)
baseline on every input in about 0.17 seconds. The CEGIS sanity test pins a
circuit that passes its initial sample but fails later; adding a discovered
row changes its SAT status to UNSAT.

## Reproduction and lifecycle

```sh
python3 main-997/search.py --sanity
python3 main-997/run_bounded.py --case-file main-997/pg4-case.json --seconds 300
```

Run a task-specific query only while the task remains authorized and active.
The outer process checks the local inactive state every five seconds, enforces
the wall-clock bound, and records its termination/reaping result on closure
or interruption. It never renews or changes a lease. The child uses one CaDiCaL
solver and a two-GiB virtual-memory limit.

The corrected runner isolates the child process group, accepts an explicit
`--stop-file`, and terminates then waits for the child in a `finally` block.
It preserves a full traceback if the runner itself raises. Its separate
dummy-only lifecycle test passed natural exit, stop-file interruption,
SIGINT, an intentional runner exception, and deadline cases, with the child
reaped in every case. The test is `test_runner_lifecycle.py`, and its record
is `wrapper-lifecycle-tests.json`. These later tests do not establish cleanup
of the earlier interrupted PG(2,4) child.

`solver-progress.json` contains interim clause, variable and search counts.
`pg4-case-bounded.json` records lifecycle and memory observations.
`results-pg4-case-cegis.json`, when produced, distinguishes SAT, UNSAT and
UNKNOWN and contains any fully validated circuit. The source, input and
geometry hashes are recorded in the corresponding manifests and audit files.
