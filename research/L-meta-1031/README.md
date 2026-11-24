# Quadratic rigidity at one surplus gate, and relative forest equality

This package contains two auxiliary results developed while working on
L-meta-1031. The complete proof chains have passed Lean. The file
`OneSurplusQuadraticAndForest.lean` is a dependency-pruned standalone
version for the project's pinned Lean/Mathlib environment. It passed its
independent Lean check unchanged: exit code 0, 7.95 seconds.

The package establishes bounded circuit structure and relative forest
rigidity. The full L-meta-1031 ownership normal form remains open in this
research work.

## 1. Raw-input quadratic rigidity

The main theorem is

`PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit.one_surplus_accepted_pair`.

Let `C` be a monotone AND/OR circuit on `n > 0` primary inputs. Assume:

1. It uses at most `n` gates.
2. It rejects every singleton input.
3. Every primary input belongs to an accepted pair input.

Then every accepted input contains two distinct true coordinates whose
pair input is accepted. Monotonicity supplies the converse, so the
computed function is the OR of its accepted quadratic terms. In
particular, it has no prime implicant of degree greater than two.

The given circuit need not be minimum, clean, or a formula. The theorem
uses the original project circuit semantics, where gates may have fewer
than two operands and invalid wire reads default to false. It passes to
an equivalent minimum circuit and proves the required normalization.

### Structural argument

Every primary input is essential: compare its accepted pair with the
partner singleton. In a clean live binary circuit with `g` gates, the
number of input ports is `2g`, while the number of nonoutput source wires
is `n+g−1`. At `g≤n`, either every source has one reader or exactly one
source has two readers and all others have one.

The proof unfolds the actual circuit into expressions. It records the
original gate positions used by each expression and proves that distinct
branches have disjoint used-gate sets after cutting the shared wire. An
exact incoming-port identity then bounds the leaf occurrences.

The result is either a read-once expression or a disjoint substitution of
a read-once inner expression into an outer expression with at most two
occurrences of one atom. The semantic argument shows that singleton
rejection and quadratic activity at every variable force all minterms to
have size two. The final theorem converts these finite-set minterms back
to the original `Fin n` inputs and circuit evaluator.

## 2. Equality in a relative forest sandwich

The second main theorem is

`PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit.relative_forest_small_circuit_equality`.

Write `F_H` for the Boolean edge function of a graph `H`, `m(H)` for its
edge count, and `τ(H)` for its minimum vertex-cover size. Let `G` be an
acyclic ambient graph on the `n > 0` primary inputs. Suppose every vertex
is incident to an edge of the critical graph `H`, and a monotone circuit
computes `F` satisfying

\[
F_H \le F \le F_G.
\]

If the circuit has `g` gates and

\[
g+1\le m(H)+\tau(H),\qquad g\le n,
\]

then `F=F_H` on every input. The first inequality is the canonical budget
`g≤m(H)+τ(H)−1` in subtraction-free form. The circuit need not be minimum.

### Accepted-pair equality is a separate result

The intermediate theorem `relative_forest_exact_pairs` does not require
`g≤n`, active vertices, or circuit leastness. It proves that at the
canonical budget every accepted distinct pair is already an `H` edge.

Define `K` as the graph of all accepted distinct pairs. Monotonicity gives
`F_K≤F`; the sandwich gives `H≤K≤G`. The checked relative forest lower
bound implies

\[
m(K)+\tau(K)\le g+1\le m(H)+\tau(H).
\]

Both edge count and cover number are monotone under graph inclusion, so
the finite edge sets of `H` and `K` must coincide. The raw-input theorem
then removes all possible higher minterms under the additional `g≤n`
condition, proving equality of the whole functions.

Ambient acyclicity is an explicit hypothesis. Assuming only that `H` is
acyclic does not meet the theorem's premises.

## Lean source and verification

The package source imports only Mathlib modules and
`PEqualNP.Defs.MetaComplexityLgpMono`. It contains the required auxiliary
proofs and does not import an `Outside` proof file.

The environment used for the checked proof chains is Lean `4.36.0` with
the project's pinned dependencies. From the repository's `lean` directory,
the standalone source can be checked with:

```sh
lake env lean ../research/L-meta-1031/OneSurplusQuadraticAndForest.lean
```

The packaging process used `run-state/prune_lean_checkpoint.py`. It keeps
whole declarations and their conservative source dependencies, without
editing proof bodies. The input frozen assembly was
`CheckedRelativeForestEqualityCorollary.lean`:

* Input SHA-256:
  `d8ecc55d484b8d88f27b9488787be424ad977cfee0a666d0a4e85a2f13bb7260`.
* Input size: 606,343 bytes.
* Selected declarations: 344 of 766.
* Standalone size: 243,843 bytes.
* Standalone SHA-256:
  `ddc0e3d8accf19c933314c2c51355086118f136e8df08ee4151e5d9d5fe4d026`.

`OneSurplusQuadraticAndForest.prune.json` records the selected theorem
roots, input/output hashes, and removed declarations. The independent
check is recorded in
`verification.json`. The verification record includes the exact checked source hash.

The project checkout used to assemble these proofs was
`67b12c81a4864e00b7443c98602811c27825f5b7`. The relative forest lower-bound
core reuses dependency-selected accepted L-meta-173 proofs; the relative
induction, one-surplus circuit decomposition, semantic rigidity, and
equality corollaries are the new auxiliary proof chain recorded here.

