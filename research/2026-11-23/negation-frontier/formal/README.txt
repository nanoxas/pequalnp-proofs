Threshold inverter: checked semantic core
========================================

Source: ThresholdInverterCore.lean
Toolchain: Lean 4.36.0, using only standard Lean modules. No Mathlib import is
required. Run the local Lean binary with -j 1; startup has been intermittently
slow in this workspace. ThresholdInverterCore.check.log records the final
check and axiom output. The manifest records its exit status and source hash.

What the source proves
----------------------

For every natural weight w and index j, threshold w j is the semantic value
of the positive threshold [j <= w]. The function below w j is its desired
complement [w < j].

1. interval_index_unique: equal-width half-open intervals cannot both contain
   a weight unless their indices agree.

2. midpoint_identity: suppose a shared Boolean bit identifies the upper half
   of whichever interval contains the weight. Given complemented endpoints,
   the expression
       Z_lo OR (NOT bit AND Z_hi)
   equals the complemented midpoint threshold.

3. levelBit_eq_true and levelBit_local: the OR of
       T_mid AND Z_hi
   over all blocks has exactly that upper-half meaning, assuming the endpoint
   complements are correct. No separate binary-digit theorem is needed.

4. refineGrid_correct: one shared complemented level bit recovers every new
   midpoint complement and preserves every old endpoint complement.

5. refineToUnits_correct: recursive dyadic refinement turns any correct coarse
   grid with spacing 2^k into the complete unit-spaced grid.

6. thresholdInverter_correct: for every w < 2^k, starting from Z_0=false and
   Z_(2^k)=true recovers NOT T_j for every 0 <= j <= 2^k. This includes k=0.
   The initial endpoint function is defined on all natural indices for
   convenience, but only indices 0 and 1 are used initially; each induction
   step explicitly bounds all queries to its valid endpoint range.

7. reverse_comparator_left, reverse_comparator_right, comparator_recovery:
   if low=a AND b and high=a OR b, the exact identities
       NOT a = NOT high OR (b AND NOT low),
       NOT b = NOT high OR (a AND NOT low)
   recover the original input complements using positive inputs and the
   known output complements.

The weight parameter is a semantic valuation of the supplied positive
threshold signals. It is not an extra input weight-computation circuit.
The data-dependent formulas in the threshold stage use positive threshold
signals, existing endpoint complements, AND, OR, and one shared NOT per
refinement level. Index arithmetic and parity tests choose fixed wires.

Bridge still required for a project circuit theorem
---------------------------------------------------

This file proves universal identities and the entire threshold-stage
recursion. It does not yet prove a bitonic sorter correct, compile the
recursion or the reverse-comparator trace into the project's root Circuit
model, verify legal wire indices, or account for gates and shared fanout in
that model. In particular, the exact count of k NOT gates and
6C+4(2^k-1) total gates is a property of the supplied compiler and paper
construction; the semantic file does not certify that count.

The source's final commands print the axiom dependencies of the full
threshold theorem and the comparator-recovery theorem. Those two dependency
closures cover the mathematical results used here.
