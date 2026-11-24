# General input counts and NOT budgets

**Draft status:** the GenericCore check ended at its 180-second import limit;
GenericSmoke was not compiled. No generic theorem or axiom audit is claimed checked.

`GenericCore.lean` is a separate prototype. The checked five-input source
generator and its pinned accepted body are preserved unchanged.

The prototype uses namespace `PEqualNP.FiniteCircuitCertificates.Generic`.
It keeps the executable search and the 256-bit signature width, while
parameterizing truth-table evaluation and input sampling by `n : ℕ`.

## Main interface

`cost_countP` has the following mathematical content. Fix an input count `n`,
truth table `T`, candidate lower bound `s`, and allowed NOT count `b`.
Supply a list `raw` of input signatures satisfying:

1. Reading its entries at the `n` input positions reconstructs the list.
2. Every positive sample evaluates to true and every negative sample to false.
3. The input signatures are distinct.
4. Removing any input signature leaves some positive–negative pair unseparated.
5. `search s t raw = false` for every `t ≤ b`.

Then every fan-in-two AND/OR/NOT circuit computing `T`, whose gate list has
at most `b` NOT operations, contains more than `s` gates.

The NOT-count hypothesis is explicit:

```lean
C.gates.countP (fun g => decide (g.op = GateOp.not)) ≤ b
```

The finite rejection family is indexed by `Fin (b + 1)`. The `cost` theorem
uses the equivalent internal Boolean predicate `isNot`; `cost_oneNot` is a
compatibility corollary for the existing unique-NOT formulation.

No monotonicity hypothesis is needed for these lower-bound theorems. The
sample labels must be valid for the specified function, and every input
must satisfy the stated necessity condition. Fixed sample width does not
assert that all positive–negative pairs of an arbitrary-arity function fit
in the representation.

## Proof structure

The existing extraction theorem gives a live-wire derivation with at most
the circuit's gate count and at most its NOT count. The necessity condition
forces its initial live frontier to contain every input signature. If the
circuit had at most `s` gates, the unchanged search-completeness theorem
would make one of the rejected searches return true. This contradiction
proves the lower bound.

`necessary` already depended only on a signature list, so it is exposed
without an artificial input-count parameter. An explicit `raw.length = n`
hypothesis is unnecessary: the reconstruction identity already forces the
correct list length.

## Files and validation

- `GenericCore.lean` contains the general interfaces and inline axiom queries
  for `cost`, `cost_countP`, and `cost_oneNot`.
- `GenericSmoke.lean` proposes a check of the new interface on two-input XOR
  with a budget of two NOT gates. Its intended conclusions require at least
  four gates and exhibit a four-gate circuit using one NOT. Its three rejection searches take one,
  one, and three recursive calls in the independent Python audit.

The completed run status is recorded in `generic-verification.json`: the
core timed out during imports, and the generic smoke was not run. Both files
remain prototypes.
The existing `smoke/lean-verification.json` concerns the preserved five-input
generator and does not establish the new generic theorems.
