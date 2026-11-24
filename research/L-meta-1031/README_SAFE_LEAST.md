# Safe minimum circuits suffice for L-meta-1031

This package isolates a conditional reduction to the exact full L-meta-1031
statement. Its remaining hypothesis is the existence, for every triangle-free
and C4-free graph, of a globally minimum monotone binary circuit in which every
AND gate is semantically safe.

A wire is safe when every input making that wire true contains an edge of the
graph. The safe-minimum existence hypothesis remains open.

## What this removes from the upstream reduction

The upstream [R_meta_1031_2 reduction](https://github.com/brilliant-hq/pequalnp-proofs/blob/8d6cf763d2a598e240f2d059606cdde25b3c9288/lean/PEqualNP/Outside/R_meta_1031_2.lean)
assumes both safe-minimum existence (`hSoundLeast`) and a separate ownership
cleanup statement (`hCleanOwn`). The theorem
`safe_least_suffices_for_full_star_ownership` has the same `hSoundLeast`
hypothesis and concludes the literal full L-meta-1031 statement directly.

The conclusion uses the exact increasing-wire transitive ancestry relation
from L-meta-1031, including AND gates in dormant branches. It retains global
minimum total size, fan-in at most two, exact edge-function semantics, and a
nonempty star of owned edges at every AND gate. Empty graphs are included.

## Public theorem interfaces

All helper declarations are in `PEqualNP.Outside.L_meta_1031_aux` or its
subnamespaces.

| Theorem | Hypotheses and conclusion |
|---|---|
| `safe_minimum_can_have_nonempty_star_owners` | Given a C4-free graph and an all-safe globally minimum circuit for its edge function, produces a globally minimum circuit of exactly the same size, with all ANDs safe and every AND owning a nonempty star. |
| `safe_least_suffices_for_full_star_ownership` | The exact global safe-minimum premise from upstream `R_meta_1031_2` implies the full literal L-meta-1031 conclusion. |

The first theorem needs no triangle-free premise and no nonempty-graph premise.
The global theorem retains the triangle-free premise from the original task.

## Proof structure

Among minimum circuits, choose one minimizing the number of unsafe AND gates,
then maximizing the number of safe gates. The given all-safe minimum circuit
forces the selected circuit's unsafe-AND count to be zero.

The checked safe-forward normalization shows that a reader of a safe wire is
an OR gate and is safe. Consequently, an AND gate has no AND ancestor in the
selected circuit. Minimality supplies a critical edge for every gate: forcing
that gate false would lose the edge. The gate fires on this edge, and the
absence of AND ancestors supplies the exact ownership condition.

Finally, the singleton traces feeding a safe binary AND generate a complete
bipartite set of accepted pairs. C4-freeness forces one side to have a common
center, giving the required star of owned edges.

## Verification and scope

The source is a dependency slice of a larger checked development. The slice
is checked independently before publication; the accompanying verification
record identifies its exact source hash, compiler version, environment, and
check result. The pruning manifest records the selected declarations.

The source imports project definitions and Mathlib. It does not import an
upstream Outside proof or assume a separate ownership-cleanup theorem.

This package advances the reduction. Full L-meta-1031 remains open because
safe-minimum existence is still an explicit hypothesis. No full-target
completion submission accompanies this helper package.

## Reproduction

The pinned environment uses Lean 4.36.0 and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

From the repository's `lean` directory, run:

```sh
lake env lean ../research/L-meta-1031/SafeLeastOwnershipReduction.lean
```

The package was checked against project definitions at commit
`67b12c81a4864e00b7443c98602811c27825f5b7`. The upstream reduction cited above
was inspected read-only; it is not a dependency of the source.
