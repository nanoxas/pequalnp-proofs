P vs NP research checkpoint — 23 November 2026
================================================
This checkpoint records completed local work while the collaboration continues.
No theorem in this bundle is claimed to resolve P versus NP. No new upstream
proof submission has been accepted on behalf of this session. The current desk
assignment is L-meta-519, shard 0: a paying restriction step at a degree-three
vertex in a least circuit. The user removed the original time limit.

Verification labels
-------------------
LEAN CHECKED means the indicated exact source completed Lean 4.36.0 with exit 0.
PAPER ARGUMENT means a mathematical argument independently reviewed within our
team, with its remaining formalization boundary stated. FINITE AUDIT means
explicit computation on the listed instances. UNKNOWN means a search stopped
without either a witness or an unsatisfiability certificate.

1. Exact support of the ladder recurrence — LEAN CHECKED
------------------------------------------------------
For q>0 and the project's posted ladder base and recursion,
  G_t(b,K)>0 iff 2^t<=K and b+2^t<=q+1.
In particular G_s(0,q^2+q+1)=0 iff q+1<2^s.
LadderSupport.lean proves a generic positivity characterization and the exact
posted specialization. AxiomAudit.check.log lists only propext,
Classical.choice, and Quot.sound. A second implementation checked the direct
recurrence against the independent greedy partition computation on 13,502
states with q<=16, with no mismatch. This identifies the exact limitation of
this recurrence; it does not exclude different lower-bound methods.

Task L-meta-1395 itself was proved by another contributor and accepted upstream
in PR2852. This bundle does not claim credit for that submission.
https://github.com/brilliant-hq/pequalnp-proofs/pull/2852

2. Clean-AND graph circuits — PAPER ARGUMENT + LEAN CHECKED CORES
--------------------------------------------------------------
For a finite C4-free graph with m edges and minimum vertex-cover size tau, the
reviewed argument proves at least tau AND gates and m-1 OR gates, provided every
AND gate is false on every independent input. These are monotone fan-in-two
circuits. For the Heawood graph this restricted class needs at least27 gates.

TypedPortCount.lean checks the finite union-network count, typed aggregation
count, and numerical assembly. The extraction of these abstract finite networks
from the full circuit semantics is not yet formalized. Thus it would be incorrect
to describe the full clean-circuit theorem as Lean checked.

The proof permits shared OR subcomputations among stars with the same center.
C4-freeness forbids certain shared merges across different centers. Normalizing
an AND with an empty raw support requires the globally clean-input hypothesis.
The examples document why omitting that hypothesis is unsound.

3. First dirty AND has a small witness — LEAN CHECKED
--------------------------------------------------
FirstDirtyWitness.lean is the exact 16,228-byte source checked with Lean4.36.0.
SHA256:1d31e54c3ef5ddb879d3afab4ced25d0d2b6ef9927f755ce3c0daa6129da1eaf.
It proves first_and_small_witness, independent_small_witness, and the direct
contrapositive clean_of_small_clean using actual CircuitLowerBounds semantics.
If an AND gate accepts an input, some AND gate accepts a subset of that input
with cardinality at most2. Independence of the support is preserved.
The statement assumes every gate is AND/OR with at most2 input entries.
Nullary and unary gates, repeated operands and invalid wire references are
handled. The conclusion can concern a different, earlier AND gate.
FirstDirtyInlineAudit.lean has this exact source as its byte prefix followed
only by three axiom-printing commands. The complete audit finished with exit0
and no warnings; only propext, Classical.choice, and Quot.sound are used.

4. Heawood search reduction — FINITE AUDITS; SEARCHES UNKNOWN
---------------------------------------------------------
The exact specification uses21 edge-positive inputs and37 maximal independent
negative inputs, with final validation against all16,384 input assignments.
The dirty case can be partitioned, using the first-dirty lemma and graph
symmetries, into a same-part pair case and a cross-part nonedge case after
excluding all same-part dirty witnesses. The included fixtures validate that
the reduced models retain intended dirty circuits. Earlier and final searches
returned UNKNOWN or were interrupted. No26-gate witness, unrestricted lower
bound, or exhaustive search claim was obtained. Task-specific searches were
stopped when the active lease ended. Regenerable CNFs and solver binaries are
omitted; synth.py and requirements.txt are included.

5. Degree-four diagonal counting — PAPER OBSTRUCTION + INTEGER AUDIT
------------------------------------------------------------------
For the exact L-meta-1394 statement, the counting and connected-cone argument
shows that a violating example would require one cone component containing at
least1,330,083 active input vertices in total, and at least1,330,082 gates.
The declared number of vertices on each side would be at least665,042.
The smallest boundary case requires at least542,673,873 counted pairs.
These active-vertex figures concern both bipartition sides combined. They do
not give a separate active-vertex bound on each side. The necessary counting
condition is8e^2<=4ve+v^2(v-2), combined with e>=408v+1 for a violation.
The missing positive lemma is a sharing-sensitive compression or count of
simultaneous degree-two factor contexts. No counterexample or exhaustion was
obtained; the desk lease was returned as missing_lemma. The unverified Lean
draft is omitted.

6. Explicit few-NOT upper bound — PAPER CONSTRUCTION + BOOLEAN AUDITS
------------------------------------------------------------------
For Desarguesian projective planes PG(2,q), q=2^h, N=q^2+q+1, the construction
computes the point/line incidence Boolean function with O(N log^2 N) gates and
at most2h+1 NOT gates. Only point-side bits need complements. The construction
uses a binary-field Walsh transform, inverse slices using the transpose of
field multiplication, and an explicit sorting-based inverter.

The implemented unoptimized circuit size is
 q^2(174h^2+168h+48)+q(54h^2+144h+64)+60h+29,
with at most2 extra gates if constants are charged separately. The inverter
uses exactlyceil(log2(N+1))=2h+1 NOT gates. Its finite audit is exhaustive for
input widths0 through10. The complete incidence compiler was checked on all
16,384 point/line inputs for q=2 (2,173 gates,3 NOT);699 cases for q=4
(19,701 gates,5 NOT); and258 cases for q=8 (143,617 gates,7 NOT).
There is no full Lean certificate for this construction. The included
ThresholdInverterCore.lean has now checked the complete dyadic refinement
recursion universally, plus the two reverse-comparator identities. Its final
Lean4.36 check exited0 with no warnings. The full threshold theorem uses only
standard axioms; comparator recovery is axiom-free. Sorter correctness,
compilation into the root circuit model, and gate counts remain formal bridges. The tiny q=2
construction is much larger than the known27-gate circuit; its relevance is
asymptotic. No novelty claim is made for known transform or inverter principles.

7. A statement distinction that prevents an invalid inference
------------------------------------------------------------
The checked L-meta-1006 six-AND witness meets a weaker maximal-independent-set
boundary condition. An exhaustive2,048-input audit finds39 false negatives and
no false positives for the full11-vertex graph function. It therefore does not
refute a six-AND lower bound for computing the full function. The separate
full-function six-AND exploratory run reached its conflict budget and is UNKNOWN.

Reproduction and provenance
---------------------------
The proofs use Lean4.36.0 and the pequalnp-proofs repository. Mathlib is pinned
at fc4f59e577feb1a4956671bc04ac18aaaf8cd842. check_lean.py shows the exact direct,
one-worker invocation and expected cached package layout. Its workspace paths
must be adjusted when reproducing elsewhere. Python audits contain their own
run options. See individual proof notes for assumptions and finite-test scope.
The manifest gives SHA256 and byte count for every bundled file.

This archive includes project research only. Operational lease data, account
credentials, toolchain caches and dependencies are excluded.
