# Finite circuit certificates

This package prepares a standalone Lean proof for an explicitly supplied public
desk row about removing one NOT gate from a finite family of five-input
monotone Boolean functions. It combines a monotone upper-witness generator,
two independently audited live-wire search evaluators, and a source generator
that retains the row's exact Lean statement.

The package uses Python's standard library. It does not fetch assignments,
manage leases, submit files, or invoke Lean. The caller supplies the current
public row and verifies that the work is authorized and still eligible.

## Status

The generic Lean body is copied **byte-for-byte** from the accepted
L-meta-1445 contribution through its `cost` theorem. That accepted source
credits L-meta-1007. The generic-body SHA256 is pinned in the generator:

```text
19a0ec27e0a5f2a6010436f261f4b74e7db8a4e454af7e6a253e5a691c5fd527
```

The minimized six-import header and complete generated synthetic AND-of-five
proof passed Lean 4.36.0 with exit code 0 in 161.956 seconds. This check includes
the entire generic engine, both rejection certificates, the explicit upper
witness, and the final singleton theorem. Only linter and deprecation warnings
were emitted. A separate axiom audit reached its 180-second deadline while
importing the checked object and produced no axiom list; that audit remains
incomplete. Exact source/object hashes, logs, and status are recorded in
`smoke/lean-verification.json`.

Every newly generated target file is labeled `GENERATED_UNCHECKED` with
`kernel_check_status: "not_run"`. A successful Python audit establishes that the
computational inputs are suitable; the project's actual Lean checker must
validate that exact emitted proof before submission.

## Use

Start with an explicit public positive row, including its `id`, `module`,
`statement`, and permitted `imports`. The generator supports the finite-family
five-input one-NOT-removal sentence used by the desk. It rejects other statement
forms instead of changing the theorem. If working through a posted opposite
twin, supply that twin's exact positive public row after confirming eligibility.

Generate monotone witnesses:

```sh
python3 finite-circuit-certificates/pipeline.py witnesses \
  --row public-row.json \
  --output witnesses.json
```

Audit the witnesses, generate sample signatures where omitted, and emit the
standalone proof in a fresh directory:

```sh
python3 finite-circuit-certificates/pipeline.py build \
  --row public-row.json \
  --certificates witnesses.json \
  --out prepared-proof
```

To perform the same prerequisite checks without emitting Lean source, replace
`build` with `audit`. An existing source file in the output directory causes an
explicit `OUTPUT_EXISTS` failure; use a fresh directory for a new run.

The default rejection-search limits are 120 seconds and two million computed
states **per evaluator and NOT count**, with a 100,000-entry memoization cache.
Change these using `--seconds`, `--max-states`, and `--cache-size`. Reaching a
limit yields `UNKNOWN_SEARCH_STATUS` and produces no new Lean source.

The formula generator accepts `--max-formula-cost` and `--seconds`. If its
bounded search stops, it retains a fully evaluated monotone DNF witness. This
can be larger than the minimum circuit, so a later rejection search may return
true. Improve the witness with further synthesis and rerun the pipeline.

## Certificate JSON

The input is either a list of records or an object with a `tables` list. Every
posted truth table needs one record, in the posted index order:

```json
{
  "index": 0,
  "truth_table": "0x80000000",
  "lower_s": 3,
  "gates": [
    {"op": "and", "inputs": [0, 1]},
    {"op": "and", "inputs": [2, 5]},
    {"op": "and", "inputs": [3, 6]},
    {"op": "and", "inputs": [4, 7]}
  ],
  "output": 8
}
```

This example is the synthetic AND-of-five function. It is not a desk assignment.
Input wires are numbered 0 through 4; gate j produces wire 5+j. The witness
must use AND or OR, at most two earlier input wires per gate, and a valid output
wire. Zero-input constants and one-input aliases are supported. Every witness
is evaluated independently on all 32 rows.

`lower_s` defaults to the witness size minus one. An explicit value must match
that quantity. `raw` is optional; if supplied, it must be a list of five
`[positive_bits, negative_bits]` pairs, with each component an unsigned 256-bit
integer or hexadecimal string.

When `raw` is omitted, the generator pairs every positive row with every
negative row. The number of pairs is at most 256. It repeats the sequence to
fill all 256 columns. It then checks the label of every column, signature
distinctness, and the essential-variable condition used by `cost`.

Optional cached `search_results` or `searches` records must all report
`status: "COMPLETE"` and `result: false` wherever those fields are present.
They are still recomputed by both evaluators. Unknown cached results cause an
explicit failure rather than being treated as rejection evidence.

## Failure behavior

Failures exit with status 2 and print a JSON record to standard error. For
`build` and `audit`, the same record is saved as `failed-status.json`.

| Failure code | Meaning |
|---|---|
| `UNSUPPORTED_STATEMENT` | The exact supplied sentence is outside the supported template. |
| `CLOSED_ROW` | The supplied public row is already marked checked or withdrawn. |
| `TABLE_ORDER_MISMATCH` | The certificate family does not match the posted tables. |
| `NONMONOTONE_TABLE` | A truth table fails monotonicity. |
| `NONESSENTIAL_VARIABLES` | A table does not depend on all five variables; the current `cost` interface needs a different argument. |
| `INVALID_WITNESS` / `WRONG_WITNESS_TABLE` | A gate reference, operation, fan-in, output, or truth table is invalid. |
| `WRONG_REJECTION_BOUND` | The rejection bound differs from witness size minus one. |
| `BAD_SAMPLE_LABEL` | A positive or negative sample has the wrong label. |
| `DUPLICATE_RAW_SIGNATURE` | Two sampled input signatures are identical. |
| `NONESSENTIAL_SAMPLED_VARIABLE` | The supplied sample columns do not establish that every input is required. |
| `UNKNOWN_SEARCH_STATUS` | A search is incomplete, exhausted its resource budget, or supplied unknown cached evidence. |
| `SEARCH_RETURNED_TRUE` | The live-wire search accepts at the proposed bound. This alone does not supply a verified counterexample circuit. |
| `EVALUATOR_DISAGREEMENT` | The optimized and reference evaluators disagree on their recursive expansion. |
| `ENGINE_BODY_CHANGED` / `IMPORT_HEADER_CHANGED` | The pinned proof core or agreed header has changed. |

No failure status is called exhaustion. In particular, returning true at the
zero-NOT bound usually means the supplied monotone witness can be improved.

## Outputs and checking boundary

A successful build emits:

- `L_meta_N.lean`: the standalone proof with the exact posted theorem statement,
  accepted generic core, attribution, separate zero-NOT and one-NOT rejection
  lemmas, sample checks, and verified monotone witnesses.
- `certificates.json`: normalized sample and witness data.
- `audit.json`: both evaluator results, timings, cache statistics, and unrolled
  recursive call counts.
- `manifest.json`: input, engine, and source hashes, with the explicit pending
  Lean status.
- `audit-progress.json`: completion state for interrupted-work diagnosis.

The unrolled call count includes repeated subtrees hidden by Python memoization.
It counts calls to `search`; actual Lean normalization also performs arithmetic
and list reductions. The source uses `decide +kernel` for every finite
certificate and never substitutes a Python verdict for a Lean proof.

The exact minimized header is:

```lean
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext
import PEqualNP.Defs
```

## Tests

Run the target-neutral Python checks:

```sh
python3 finite-circuit-certificates/selftest.py
```

The recorded self-test checks 480 random evaluator comparisons, 240 coverage
formula frontiers, known positive and negative semantic cases, synthetic
five-input AND/OR certificates, 19 monotone upper-witness tables, exact source
statement preservation, and the requested failure paths. It uses no real desk
assignment and runs no Lean compiler. Results are in `selftest-results.json`.

`make_smoke.py` additionally emits a complete standalone synthetic proof for
AND-of-five, using an explicit four-gate chain and rejection bound three:

```sh
python3 finite-circuit-certificates/make_smoke.py
```

Its final theorem is `PEqualNP.Outside.FiniteCertificateSmoke`, and the source is
`smoke/Smoke.lean`. The script does not invoke Lean. Its manifest records
`synthetic: true` and `desk_task: null`; a separate bounded Lean run and axiom
audit must establish its checking status. Regenerating it resets its manifest
to unchecked.

## Package files

The separate `GenericCore.lean` extension and `GenericSmoke.lean` interface
test also passed Lean, including inline axiom audits. They parameterize the
input count and allowed NOT count while keeping the 256-bit sample width.
The five-input generator remains unchanged. See `GENERIC.md` and
`generic-verification.json` for the general theorem interface and exact
checking evidence.

- `formula_upper.py`: bounded formula dynamic programming, DNF baseline,
  semantic sharing, and full witness evaluation.
- `live_checker.py`: the audited optimized search and independent direct-coverage
  reference search, with explicit resource-limit reporting.
- `pipeline.py`: public-row validation, prerequisite checks, audit, and Lean
  source assembly.
- `engine/GenericBody.lean.inc`: unchanged accepted generic body.
- `engine/imports.txt` and `engine/provenance.json`: minimal imports and origin
  hashes.
- `NOTICE.md`: attribution and reuse information.

The package contains no credentials, lease data, or held-task state.
