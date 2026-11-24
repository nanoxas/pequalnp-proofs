# Research on the one-NOT refund bound

This checkpoint contains reusable Lean lemmas and partial results for the
public L-meta-997 statement. **The full statement remains unproved here.**
The complete statement is preserved in [task.json](task.json) and
[statement.txt](statement.txt). No theorem submission or upstream acceptance
is claimed by this research checkpoint.

The problem concerns a linear family of input sets: two distinct sets
intersect in at most one point. A circuit with at most one NOT computes the
OR of each set. Its NOT output is true below a specified input weight and
false at an input set Y. The requested inequality charges heavy targets
(those disjoint from Y) at their full size, light targets at their size
truncated to |Y|, and permits a precisely defined refund for certain gates.

## Kernel-checked components

There are twenty-six checked modules. Each has a sibling `.verification.json`
and `.check.log`.
The records give the exact source hash, successful exit code, and inline
axiom audit. Audited declarations use only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`, or a subset of them.

| Module | Checked contribution |
|---|---|
| [MintermSlack](formal/MintermSlack.lean) | A monotone function with minimum positive weight k needs at least k−1 true-at-Y AND gates with empty singleton support in its prefix. |
| [LightCount](formal/LightCount.lean) | Private gate counts for the small-input light window, with disjointness across a linear set family. |
| [LightMinterm](formal/LightMinterm.lean) | Combines the light and minterm gate sets without double counting. |
| [NotWindow](formal/NotWindow.lean) | Derives the actual NOT and valid head from the posted window hypotheses and transports the combined count to the original circuit. |
| [OrPrivateCount](formal/OrPrivateCount.lean) | Counts only OR gates for globally sound heavy targets, with a prefix version and disjoint family sum. |
| [HeavyReplacement](formal/HeavyReplacement.lean) | Replaces the NOT by false; proves global domination, agreement above Y, and the original-circuit heavy count. |
| [RefundCount](formal/RefundCount.lean) | Matches the exact posted predicate, proves forced refunds for nontrivial heavy outputs, and derives sufficient cases from the light/minterm count. |
| [SmallWindow](formal/SmallWindow.lean) | Proves the inequality without refunds when |Y|≤2, and proves the exact refund inequality whenever every target has size at most four. |
| [ClauseMinterm](formal/ClauseMinterm.lean) | Strengthens the accepted mandatory-clause count by adding the k−1 empty-support prefix AND gates; deletion cost counts only targets of size at least two. |
| [OutsideIncidence](formal/OutsideIncidence.lean) | Bounds the nontrivial target incidence of a point outside Y by the exact refund count plus |Y|. |
| [PairClause](formal/PairClause.lean) | Proves the stronger unweighted target-size inequality when the NOT input has a mandatory pair clause with one point in Y and one outside. |
| [HeavyPacking](formal/HeavyPacking.lean) | Uses ordered-pair packing to prove the exact posted inequality whenever n≤3|Y|+1, including empty and singleton targets. |
| [HeavyMinterm](formal/HeavyMinterm.lean) | Combines heavy OR charges, nontrivial light output gates, and the minterm budget; derives a complementary sufficient criterion using the exact refund count. |
| [TriplePacking](formal/TriplePacking.lean) | Bounds heavy excess by 2k when the outside universe has size at most 3k+1, using a finite linear-family packing argument. |
| [OutsideActivation](formal/OutsideActivation.lean) | Recovers full private counts when fewer than k exceptional wide gates remain, using a direct cut and a small negative input. |
| [DoubleExcess](formal/DoubleExcess.lean) | Proves the exact refund inequality when the total heavy excess after the forced-heavy refund is at most 2k. |
| [FourWindow](formal/FourWindow.lean) | Combines the packing and activation results to prove the exact posted inequality whenever n≤4|Y|+1. |
| [BoundaryActivation](formal/BoundaryActivation.lean) | Builds target-avoiding activation inputs, proves a full private count when such an input is negative, and bounds a private deficit by the exceptional gates. |
| [BoundaryRigidity](formal/BoundaryRigidity.lean) | Finds at least k+1 popular points in a deficient class and pays all private deficits when there are at most 2k−2 exceptional gates. |
| [TripleExcess](formal/TripleExcess.lean) | Proves the exact refund inequality when the heavy excess is at most 3k−1, for k≥2. |
| [OrCompensation](formal/OrCompensation.lean) | Pays each private deficit using exceptional OR gates after subtracting the class's private AND gates. |
| [DeficientSeparation](formal/DeficientSeparation.lean) | Produces missed points whose active exceptional-gate sets have directed difference at least k−1 against every point outside the target. |
| [DeficientPacking](formal/DeficientPacking.lean) | Shows that at most two private classes are deficient when k≥3 and there are at most 3k−4 exceptional gates. |
| [CoupledCut](formal/CoupledCut.lean) | Constructs a full cut and a positive subfrontier together, with the required containment and an AND-only branching count. |
| [PrivateAnd](formal/PrivateAnd.lean) | Proves that every deficient private class contains at least k−1 AND gates. |
| [QuadrupleExcess](formal/QuadrupleExcess.lean) | Combines the deficiency bounds and proves the exact refund inequality when the heavy excess is at most 4k−3, for k≥3. |

The files are research modules with local imports. They are not an exact
standalone submission for the unrestricted posted statement. Earlier
accepted project sources reused by these modules are attributed in their
headers and verification records under the repository's Apache-2.0 license.

One useful checked combined bound is

\[
\sum_i\bigl(\min(k,|S_i|)-1\bigr)_+ + k \le N,
\]

where k=|Y|≥2 and N is the gate count. The exact refund inequality follows
when

\[
E_{+}:=\sum_{i:S_i\cap Y=\varnothing}\max(|S_i|-k-1,0)\le 4k-3
\]

for k≥3. This is the checked `QuadrupleExcess` criterion. `SmallWindow`
handles every instance with k≤2. The earlier `DoubleExcess` and
`TripleExcess` bounds remain available as intermediate results. The all-light
case and the case in which every heavy set has size at most k+1 are
consequences. Empty and singleton targets are allowed throughout.

The [strengthened clause argument](crossing-pair-independent-audit.txt) now
has checked components in `ClauseMinterm`, `OutsideIncidence`, and `PairClause`.
Its pair clause is a semantic condition on the NOT input; the pair does not
have to be a target. A separate checked packing argument proves the original
inequality for every instance with **n≤4|Y|+1** through `FourWindow`.

The new activation argument counts wide gates outside every private target
class. If their number r is less than k, one can activate them on fewer than
k inputs outside any chosen target. The cut lemma would then transfer a
positive target output to a negative input unless its private class already
has the full |S_i|−1 gates. `OutsideActivation` proves this argument directly,
including empty and singleton targets, constants, and unavailable wires.

The latest proof extends this approach to r≤3k−4. Directed separation of
active exceptional-gate sets permits at most two deficient private classes.
Each deficient class has at least k−1 private AND gates, while its missing
count is bounded by the exceptional OR gates minus those private AND gates.
The combined budget pays both deficits. The
[deficiency-budget explanation](deficiency-budget-paper.txt) and
[independent review](deficiency-budget-independent.txt) record this argument
and the precise scope of its checked components.

## The thirteen-input audit

The [case data](case13/case.json) have one heavy eight-point target, nine
light triples, and Y={0,1,2}. The [data and baseline audit](case13/audit.json)
checks all 45 target-pair intersections and all 8,192 input rows of a
28-gate baseline. Its exact weighted total is 35; the earlier checked bounds
leave only the potential violation size 23 with refund count 1.

An [independent support audit](case13/independent-audit.json) verifies the
family arithmetic and a finite superset of the possible support transitions.
The accompanying [exclusion proof](case13/exclusion-independent.txt) shows
that equality in the light/minterm bound cannot build the eight-point output
from its two private gates. This is a reviewed paper exclusion with a Python
data audit; no target SAT query or target-specific Lean instantiation was run.
The case now also falls within both checked general sufficient ranges:
its heavy excess is 4≤2k=6 and n=13≤4k+1=13.

## Paper arguments and the remaining step

The [PG(2,4) paper argument](pg4-exclusion-paper.txt) excludes a violation for
the 21 five-point line targets with a three-point collinear Y. Its proof
combines private heavy OR gates, light output gates, minterm AND gates, and
a classification of the small remaining prefix. The
[generalization](saturation-generalization.txt) gives a corresponding
three-point saturation criterion that permits light triples. The
[independent audit](saturation-independent-audit.txt) checks the residual
classification, including sharing, constants, unary gates, and unavailable
wire references. The newer
[small-surplus proof](saturation-small-surplus-audit.txt) allows arbitrary
light target sizes and every k=|Y|≥2. If H counts nontrivial heavy targets,
e counts empty targets, and Q is the sum of max(min(k,|S_i|)−2,0) over light
targets, it proves the sufficient criterion Q≤H+k+e+2 on paper. Its complete
gate classification has not been checked as a Lean theorem.

The [exceptional-support note](exceptional-support-paper.txt) records the
checked sequence through r≤3k−4 and Eplus≤4k−3 in Section 8. The historical
projected-support classification in Section 6 remains **PAPER_REVIEWED**;
its numerical range is covered by the later checked results. Supplementary
normalization, transversal refinements, and the stronger global OR/AND
dichotomy remain paper arguments.

The unresolved general step controls overlap between light and heavy gate
charges when the small-input activation argument has too many independent
outside supports. The checked crossing-pair theorem and the reviewed
small-surplus classification settle additional cases, but the current
results do not charge every remaining overlap to the exact refund predicate.

## Why raw overlap charging fails

The [overlap audit](overlap-audit/selection-obstruction.txt) gives a seven-input
circuit whose partial light and heavy charge classes share gates that do not
satisfy a whole-target refund. Repeated live aliases make the raw overlap
larger than the refund count. The [reproducer](overlap-audit/audit.py) checks
all 128 inputs of each of four circuits, the exact guarded refund predicate,
and every per-set count. The original L-meta-997 inequality holds in all four.

These examples admit disjoint selections of the minimum required quotas.
They show why a proof must control selected charges or account for unused
gate capacity. They do not refute a suitable minimum-quota selection lemma.
The [results](overlap-audit/results.json) and [manifest](overlap-audit/manifest.json)
preserve the exact data and hashes; this is an exhaustive finite audit, with
no SAT or Lean claim for these particular circuits.

## Exact statement and parsing check

The posted shifted-input condition is explicitly grouped as
`p ∉ Y → (value = true ↔ p ∈ S i)`. A fresh public-row comparison and balanced
parenthesis check are saved in
[refund-parse-public-row.json](refund-parse-public-row.json).

A draft helper omitted the outer grouping when abbreviating the wire
expression. That draft failed compilation and was corrected. The checked
`refundGates_eq_posted` lemma now equates the helper to the
[verbatim posted Finset expression](formal/refund-predicate-verbatim.txt).
The public statement and the SAT encoder used the guarded predicate throughout.

## Finite diagnostic and its limits

The independent [geometry audit](pg4/audit.json) verifies the 21 points and
21 lines of PG(2,4), all 210 line-pair and 210 point-pair incidences, and the
13-light/eight-heavy split. Its affine enumeration is checked against an
independent homogeneous-coordinate construction. The full truth-vector
validator also checked an 87-gate baseline on all 2,097,152 inputs.

The sole 49-gate SAT query was stopped and remains **INTERRUPTED_UNKNOWN**.
It returned neither a candidate nor UNSAT. Its
[run record](pg4-run-record.json) preserves 53,227 variables, 2,437,625
clauses, 272 sampled input rows, and the last saved search statistics.
No 48-gate query was run. The original runner did not finalize cleanup, so
the child's reaping remains unconfirmed in that record.

The corrected runner passed five dummy-only lifecycle checks, including an
intentional exception and signal interruption; those checks do not establish
cleanup of the earlier child. See [SEARCH.md](SEARCH.md), the
[encoder](search.py), and the
[lifecycle test record](wrapper-lifecycle-tests.json) for reproduction details.
The search requires Python-SAT; the observed environment used
`python-sat==1.9.dev24` and `six==1.17.0`. Solver binaries and compiled Lean
objects are excluded from this checkpoint. A new target search requires a
current authorized assignment and an explicit decision to run it.
