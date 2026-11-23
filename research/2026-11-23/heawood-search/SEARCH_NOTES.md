# Heawood circuit synthesis

This directory records a search for the witness in public gap L-meta-582. A
witness must be a monotone binary AND/OR circuit with at most 26 gates computing
the Heawood graph's edge function on 14 inputs. The known star construction has
27 gates. Search failure alone is not a lower-bound proof.

## Exact boundary test set

The graph has 21 edges and 37 maximal independent sets. Of the latter, 21 have
size 4, 14 have size 5, and two have size 7. These counts were obtained by
enumerating all 16,384 subsets independently in two agents' programs.

For any monotone candidate circuit, correctness on the 21 edge-positive inputs
and the 37 maximal-independent-set negative inputs is equivalent to correctness
on every input. A positive input contains an edge, and a negative input is
contained in a maximal independent set. Monotonicity gives the corresponding
output value in both cases. Every SAT witness is additionally checked on all
16,384 inputs before being saved.

## Sound cuts for a minimum-size circuit

For a wire w, let P(w) be its set of true edge-positive rows and N(w) its set of
true maximal-independent-set rows. If an earlier wire h satisfies

    P(w) subset P(h), and N(h) subset N(w),

then h can replace w. On every positive row the downstream monotone circuit's
value can only increase, and on every negative row it can only decrease. Thus
correctness on all boundary rows is preserved, and the boundary argument gives
correctness on all inputs. Removing the replaced gate gives a smaller circuit.

Consequently a minimum-size circuit contains no such dominated gate. In
particular:

- Each gate is true on at least one edge-positive row.
- Each gate is false on at least one maximal-independent negative row.
- Every AND gate removes at least one negative row from each of its operands.
- Every OR gate adds at least one positive row beyond each of its operands.

The first two statements also follow by replacing the gate by a Boolean
constant and simplifying. Constant gates, unary gates, repeated-input gates,
unused gates, and references that evaluate to the default false value can all
be simplified before choosing a minimum circuit. A nonconstant target therefore
admits a minimum circuit with distinct binary fanins referring to previous
wires, and every gate reaching the output.

The optional `--edge-singletons` normalization is also sound: if a gate is true
on exactly one edge row e=(u,v), replace it by AND(x_u,x_v). Being true at that
two-element input implies that the direct conjunction is pointwise below the
original monotone gate. All edge-row values stay identical and negative-row
values can only decrease, at no extra gate cost. Repeating this replacement
preserves every downstream gate's edge-row support, so the normalizations hold
simultaneously. Any newly redundant gates can then be removed. This argument
was independently reviewed by a second agent.

## Canonical gate ordering and four symmetry cases

A circuit can be topologically ordered so that the maximum fanin index is
nondecreasing. At each step choose a ready gate with the smallest maximum
fanin. Previously ready gates cannot have a smaller maximum than the gate just
chosen; newly ready gates refer to that gate's newly assigned wire index, which
is greater than every earlier index.

`--lex-order` further sorts ready gates by their minimum fanin and operation
when maximum fanins tie. The same argument applies: newly ready gates have a
strictly larger first ordering coordinate. The fixed operation order is AND
before OR.

Independent enumeration found all 336 automorphisms of this Heawood labeling.
There are three unordered input-pair orbits: 42 same-part pairs, 21 edges, and
28 cross-part nonedges. A first AND on a nonedge is excluded by the empty
positive-support cut. The following priority partition therefore covers
minimum circuits, up to graph automorphism and the canonical gate ordering:

| Orbit option | First gate | Further restrictions on active input-input gates |
| --- | --- | --- |
| 0 | OR(0,1) | None; used when some same-part input OR exists. |
| 1 | AND(0,7) | No same-part input OR. |
| 2 | OR(0,7) | No same-part input OR and no input-edge AND. |
| 3 | OR(2,7) | No same-part input OR and no gate on an input edge. |

For case 0 the chosen gate can be sent to the globally smallest input pair. For
cases 1 and 2 every available input pair is cross-part, and (0,7) has the
smallest possible maximum fanin. For case 3, (2,7) is the smallest cross-nonedge
pair. The chosen gate can therefore be first while preserving the canonical
ordering. The later cases deliberately exclude earlier priority types.

## Encoding sizes at most 26

`--at-most` introduces an active prefix of the allocated gate slots. The output
is exactly the last active gate. Minimality and live-consumer cuts are
conditioned on activity. Since all predecessors of an active gate are earlier,
its gate predecessors are also active. An inactive suffix can be completed with
dummy gates on input 0 and the preceding wire, preserving the maximum-fanin
ordering. It therefore imposes no additional condition on the active circuit.

This mode covers every possible minimum size up to the stated bound. An earlier
exact-26 experiment required all 26 gates to be nonredundant, so its failure
would not by itself exclude a smaller circuit. Those earlier runs are retained
as exploratory runs only.

## Solver and result records

Runtime dependencies: Python 3.12, `python-sat==1.9.dev24`, and `six==1.17.0`.
The packages were installed as binary wheels into the local `vendor/` folder.
Each solver process is single-threaded and has a 4 GiB address-space limit.
`synth.py` emits every option, variable count, clause count, wall-clock start,
result, elapsed time, and solver statistics when the solver API provides them.
Each full orbit run writes its exact DIMACS CNF.

JSON result statuses have these meanings:

- `true`: SAT; inspect the saved circuit and all-input validation result.
- `false`: the solver reported UNSAT for that exact configured model.
- `null`: the conflict budget was exhausted without a verdict.
- A log with no final result: the process was interrupted or hit its wall limit.

The SAT solver is separate from the project's Lean checker. An UNSAT report
does not by itself constitute a submitted Lean proof or settle the public gap.

## Validation already performed

`baseline-validated.json` fixes the known 27-gate construction and passes the
encoding and the full truth-table check. `baseline-pruned-validated.json` adds
all semantic dominance cuts. `atmost-baseline-validated.json` allocates 28 slots,
fixes that 27-gate construction, and correctly selects exactly 27 active gates.
The strong cuts and full lexicographic ordering also pass eight small-graph
checks: matching2 and K2,2 have minimum 3, while path3 and triangle have minimum
4; each stated size returned a fully validated circuit and each bound one lower
returned UNSAT. Records are in `strong-small-graph-sanity.json`.

Local repair results `repair1.json` through `repair4.json` exhaust one to four
gate edits of a particular 26-gate star near miss under canonical ordering and
minimality cuts. They concern only that neighborhood. A broader five-edit run
without those cuts was interrupted to prioritize the four complete orbit cases.

No 26-gate witness or general UNSAT result has been obtained as of this note.

## Clean circuits and the remaining dirty cases (22:42 UTC update)

The paper proof in `../heawood-math/clean-or/clean-or-proof.md` now establishes
OR count at least m−1 and AND count at least the vertex-cover number for every
C4-free graph circuit whose AND gates are all globally clean. A globally clean
wire is false on every independent input. The finite port-count cores have a
local Lean proof; extraction from the project's circuit semantics remains open.
This is a restricted-class research result, not a checked proof of L-meta-582.

The raw-union charge permits sharing among stars with the same center. Group
all chosen noncenter operands by center v, with p_v outputs and raw union U_v.
Their OR-only union DAG needs at least |U_v|−p_v binary merges. Support of size
at least two makes these merges private across distinct centers by C4-freeness.
Typed empty-support ports provide the separate aggregation count. No final-OR
normalization is assumed.

The exact `--clean-abstract` encoding uses 21 edge rows and14 singleton rows.
Every AND is explicitly constrained to have disjoint, completely adjacent raw
operand supports. Its output singleton support is empty. This is an exact
35-coordinate model of the globally clean class. A fixed27-gate baseline in28
active-prefix slots was verified in this model and on all16,384 inputs.
The unpinned≤26 clean run was stopped without a result after the paper proof
closed this class; its status is UNKNOWN, not UNSAT.

For arbitrary monotone circuits, choose the first AND true on an independent
input. Earlier ANDs are all false on that input, so each true operand contains
a true raw input. Some AND is therefore true on an independent singleton or
pair. In Heawood, every such set extends to a size7 or size5 maximal independent
set. Consequently, if all ANDs reject the16 maximal independent sets of these
two sizes, they reject every independent input. There is no class whose only
dirty witnesses are the size4 maximal independent sets.

A complete normalized witness partition for≤26 gates, using the clean lower
bound as a paper argument, is now:

1. The clean class (paper-excluded, not yet root-model Lean formalized).
2. Some AND is true on the canonical same-part pair {0,1}.
3. Every AND is false on both full bipartition inputs, and some AND is true on
   the canonical cross nonedge pair {2,7}.

To justify case2, choose the first AND true on a full part; earlier ANDs are
false on that part, yielding a singleton/pair witness inside it. Extend a
singleton to a pair. The automorphism group is transitive on same-part pairs.
In case3, choose the first globally dirty AND. Its small witness cannot lie
inside either full part, so it is a cross nonedge; the group is transitive on
these pairs as well. The pair representative and a first-gate representative
must not be normalized independently: their joint orbit/stabilizer is needed.

`--dirty-pair-class 7` and `--dirty-pair-class 5` append one negative pair row to
the full58-row correctness basis, require an active AND true there, and (in
class5) forbid every active AND from firing on either full part. All37 output
MIS constraints remain. `dirty_pair_fixtures.py` constructs explicit valid
Heawood circuits of29 and30 gates respectively, checks the encoded constraints
with pinned gates, and independently checks all16,384 inputs. These fixtures
are deliberately nonoptimal and serve to validate the model, not suggest a
26-gate construction.

The older MIS-only class7 run returned UNKNOWN after4M conflicts and421.78s.
The older MIS-only class5 run was interrupted to use the stronger pair model.
The pair runs use5M conflicts,40min wall caps, and4GiB memory caps each:

```sh
python3 -u synth.py --gates 26 --at-most --solver cadical300 --lex-order --live \
  --semantic-pruning --dominance-all --edge-singletons --dirty-pair-class 5 \
  --conflicts 5000000 --cnf dirty-pair5-26.cnf --result dirty-pair5-26.json
python3 -u synth.py --gates 26 --at-most --solver kissat404 --lex-order --live \
  --semantic-pruning --dominance-all --edge-singletons --dirty-pair-class 7 \
  --conflicts 5000000 --cnf dirty-pair7-26.cnf --result dirty-pair7-26.json
```

A useful normalization remains valid globally: if an AND has a globally clean
operand h, bypass it by h. This changes no independent-input value and can only
increase positive values, so correctness persists. A minimum circuit has no
such gate. Classifying actual wires as clean C or dirty D, and writing A_C for
clean AND outputs, c for OR(C,C), and r for mixed OR(C,D), the same port argument
gives c+r≥A_C−1. Extending the charge across dirty AND outputs and their later
filtering is the remaining structural bottleneck.

## Lease stop at22:43 UTC

The locally managed L-meta-582 lease was marked HTTP410. On root's instruction,
both canonical-pair solver processes were stopped immediately (exit130), with
no final solver result. Their status is INTERRUPTED/UNKNOWN. CNFs, options, and
start timestamps remain in the corresponding files. No582 solver is active.

The checked L_meta_1006 counterexample concerns a weaker maximal-independent
boundary condition. It does not compute the exact graph edge function, so it
does not by itself refute an exact-function AND-count≥vertex-cover theorem.
The current clean proof and search records do not rely on that implication.
