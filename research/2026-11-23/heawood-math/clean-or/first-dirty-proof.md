# First true AND gates have small supported witnesses

This is a generic local theorem about the actual
`PEqualNP.CircuitLowerBounds.Circuit` semantics. It has no graph-specific
hypothesis and is not a project submission.

## Formal statements

`FirstDirtyWitness.first_and_small_witness` assumes every gate is AND or OR
with at most two inputs. If an AND gate is true on input x, it produces a
possibly different AND gate and a finite set S such that:

* S has cardinality at most two;
* every variable in S is true in x;
* the produced AND gate is true on the input supported exactly on S.

`FirstDirtyWitness.independent_small_witness` adds any binary relation R and
the hypothesis that x's support contains no R-related pair. The resulting S
also contains no R-related pair. Taking R to be graph adjacency yields the
first-dirty-AND reduction.

`FirstDirtyWitness.clean_of_small_clean` is the direct contrapositive: if every
AND rejects every independent support of cardinality at most two, every AND
rejects every independent input.

The conclusion is existential over AND gates. A later AND can itself need
more than two true variables; the proof finds the first AND that is true on
the original input.

## Proof

Choose the first AND that evaluates to true on x. All earlier ANDs are false
on x. Induction on the wire index shows that any earlier true wire has a
singleton witness contained in x's support. At an input, choose that input.
An earlier AND cannot be the true wire. A true OR has a true operand, to which
the induction hypothesis applies.

Choose one singleton witness for each actual entry of the first AND's input
list and take their finite union. Its cardinality is at most the input-list
length, hence at most two. Monotonicity preserves each operand's truth when
the singleton input is enlarged to this union. All operands, and therefore
the AND, are true on the resulting input.

## Boundary cases

Nullary AND is true and receives the empty witness. A unary AND receives at
most one witness. Repeated operands or repeated witness variables only reduce
the cardinality of the finite union. The proof also allows zero input
variables.

Wire references at or beyond the current wire-list length evaluate to false
in the root model. A true AND therefore has no such referenced operand. The
formal wire lemmas account for these references directly, and later gates
cannot alter earlier wire values.

## Files and reproduction

The proof file is `FirstDirtyWitness.lean`. It imports the actual narrow
`PEqualNP.Defs.CircuitLowerBounds` module and `Mathlib.Data.Finset.Card`.
There is no copied-model bridge in that file. Basic wire lemmas are adapted
from the checked `L_meta_970` source, with no import of its outside proof.

From `/workspace/scratch/91448c28ebe7`, run:

```sh
python3 heawood-math/clean-or/check_lean.py heawood-math/clean-or/FirstDirtyInlineAudit.lean
```

The helper uses the pinned Lean 4.36.0 binary, one worker, and the existing
package build directories. It does not run a dependency build or access the
network. Each check writes a neighboring `.check.log` file. The separate
inline audit contains the exact source of `FirstDirtyWitness.lean`, followed
only by three axiom-printing commands; it avoids requiring object emission.

The complete inline audit returned exit 0 with no warnings. Each of the three
principal theorems depends only on `propext`, `Classical.choice`, and
`Quot.sound`. The exact output is in `FirstDirtyInlineAudit.check.log`.
