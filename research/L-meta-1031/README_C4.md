# Small monotone circuits and C4-free relative graph functions

This is the second checked auxiliary package developed during the work on
L-meta-1031. It adds accepted-pair forest classification and C4-free
relative lower bounds to the earlier quadratic-rigidity package. The
earlier files remain unchanged.

`OneSurplusQuadraticAndC4.lean` passed an independent Lean check unchanged:
exit code 0 in 8.39 seconds. It is a dependency-pruned standalone source
for the project's pinned Lean/Mathlib environment. The complete
L-meta-1031 ownership normal form remains the research target.

## Public results

All theorem names below are in
`PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit`.

### 1. Raw-input quadratic rigidity

`one_surplus_accepted_pair` applies to any monotone AND/OR circuit on
`n>0` primary inputs with at most `n` gates. If it rejects every singleton
and every input belongs to an accepted pair, every accepted assignment
contains a distinct accepted pair. Thus its minimal true inputs all have
size two.

The given circuit need not be minimum or clean. The proof works in the
original project model, including gates with fewer than two operands and
default-false invalid wire reads, by passing to a minimum equivalent
circuit and proving the required normalization.

### 2. C4-free accepted-pair graphs are forests at this size

`one_surplus_pair_forest` adds C4-freeness of the graph of accepted
distinct pairs to the preceding circuit hypotheses. It concludes that
this graph is acyclic. No triangle-free hypothesis is required.

The underlying structural theorem,
`clean_one_shared_source_pair_forest`, allows arbitrary fanout at one
source wire while all other sources are read at most once. It assumes a
clean positive circuit with terminal output, singleton rejection, and a
C4-free accepted-pair graph. It imposes no gate-count or pair-activity
bound. This theorem classifies the pair graph even when higher-degree
minterms are present.

### 3. Direct C4-free relative lower bound

Write `F_H` for the edge function of a critical graph `H`, `m(H)` for its
edge count, and `τ(H)` for its minimum vertex-cover size. Let `G` be a
C4-free ambient graph on `n>0` vertices, with every vertex incident to an
`H` edge. Suppose a monotone circuit of size `g` computes `F` satisfying

\[
F_H\le F\le F_G.
\]

`relative_c4free_small_circuit_lower` proves that if `g≤n`, then

\[
m(H)+\tau(H)\le g+1.
\]

There is no canonical-budget premise in this lower-bound statement.

`relative_c4free_large_potential` states the useful threshold consequence
without assuming `g≤n`:

\[
m(H)+\tau(H)\ge n+2\quad\Longrightarrow\quad g\ge n+1.
\]

### 4. Equality at the canonical budget

`relative_c4free_small_circuit_equality` uses the same C4-free sandwich
and active critical vertices. If `g≤n` and

\[
g+1\le m(H)+\tau(H),
\]

then `F=F_H` on every input. This strengthens the earlier equality result
by replacing acyclicity of the original ambient graph with C4-freeness.
The circuit need not be minimum.

## Proof architecture

Quadratic pair activity makes every primary input essential. In a clean
live binary circuit, the difference between the input-port count and the
number of nonoutput source wires is `g−n+1`. At `g≤n`, either every source
is read once or only one source is read twice.

The proof constructs expressions from the actual circuit, recording each
original gate used in the unfolding. Unique upward readers make the two
child gate sets disjoint after cutting the shared wire. An exact
incoming-port identity bounds expression leaf occurrences. This yields a
read-once inner expression, an outer expression whose only repeated atom
is the shared source, disjoint input sets, and exact circuit semantics.

Semantic expression arguments prove quadratic rigidity at two occurrences
and pair-graph acyclicity with arbitrary occurrences of that one atom.
The latter uses C4-freeness to reduce complete bipartite pieces to stars
and glues forests along at most one vertex. The actual-circuit adapter
transfers adjacency between `Fin n` inputs and `Nat` expression labels
and pulls acyclicity back along the injective `Fin.val` graph map.

For the relative bounds, let `K` be the graph of pairs accepted by the
circuit. Soundness gives `K≤G`, so `K` is C4-free. The small-circuit
classification makes `K` acyclic, and quadratic rigidity gives `F≤F_K`.
The checked relative forest lower bound applies to `H≤K`, yielding the
direct inequality above. At the canonical budget it also forces the
accepted-pair profile to equal `H`, and purity gives equality of the whole
functions.

## Reproduction and provenance

The source imports only Mathlib modules and
`PEqualNP.Defs.MetaComplexityLgpMono`, with all required auxiliary proofs
included locally. It does not import an `Outside` proof file.

The checked environment uses Lean `4.36.0` and the project's pinned
dependencies. From the repository's `lean` directory:

```sh
lake env lean /absolute/path/to/OneSurplusQuadraticAndC4.lean
```

The conservative dependency selector retained 449 of 824 declarations,
reducing the checked 663,194-byte assembly to **319,912 bytes**. It kept
whole declarations and did not edit proof bodies. The generated slice
then passed its own independent Lean check unchanged.

* Source SHA-256:
  `4986000d09d5b75e9f3bd5ed8838b09bce64087bd85a71c0dd2a8694a088e171`.
* Input checkpoint SHA-256:
  `67aabc707b455d46bcf8a6325e559469cccc6dc070f759490ce320cf690beb80`.
* Project base commit:
  `67b12c81a4864e00b7443c98602811c27825f5b7`.

`verification_C4.json` records the independent check and exact scope.
`dependency_prune_C4.json` records the selected roots, hashes, and removed
declarations. The forest elimination core reuses dependency-selected
accepted L-meta-173 proofs; the relative induction, actual circuit
decomposition, semantic rigidity, accepted-pair forest classification,
and C4-free corollaries form the auxiliary chain developed here.

