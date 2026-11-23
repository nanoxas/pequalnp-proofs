import Init.Data.List.Nat.Range
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.RCases
import Lean.Meta.Tactic.AC.Main

/-!
Semantic core for the sorting-based inverter in `review/boolean_audit.py`.
This file proves Boolean identities and finite threshold refinement. It does
not yet extract a circuit in the project's root model, certify a bitonic sorter,
or count the gates of a generated circuit.
-/

namespace ThresholdInverterCore

/-- Increasing weight thresholds. -/
def threshold (weight index : Nat) : Bool := decide (index ≤ weight)

/-- Their desired complements. -/
def below (weight index : Nat) : Bool := decide (weight < index)

theorem below_eq_not_threshold (weight index : Nat) :
    below weight index = !(threshold weight index) := by
  by_cases h : index ≤ weight
  · have hn : ¬ weight < index := by omega
    simp [below, threshold, h, hn]
  · have hl : weight < index := by omega
    simp [below, threshold, h, hl]

theorem reverse_comparator_left (a b : Bool) :
    (!(a || b) || (b && !(a && b))) = !a := by
  cases a <;> cases b <;> decide

theorem reverse_comparator_right (a b : Bool) :
    (!(a || b) || (a && !(a && b))) = !b := by
  cases a <;> cases b <;> decide

theorem comparator_recovery (a b low high negLow negHigh : Bool)
    (hlow : low = (a && b)) (hhigh : high = (a || b))
    (hnlow : negLow = !low) (hnhigh : negHigh = !high) :
    ((negHigh || (b && negLow)) = !a) ∧
    ((negHigh || (a && negLow)) = !b) := by
  subst low high negLow negHigh
  exact ⟨reverse_comparator_left a b, reverse_comparator_right a b⟩

/-- Half-open equal-width intervals have a unique index. -/
theorem interval_index_unique (weight width i j : Nat)
    (hi0 : i * width ≤ weight) (hi1 : weight < (i + 1) * width)
    (hj0 : j * width ≤ weight) (hj1 : weight < (j + 1) * width) : i = j := by
  apply Nat.le_antisymm
  · by_cases h : i ≤ j
    · exact h
    have hle : j + 1 ≤ i := by omega
    have := Nat.mul_le_mul_right width hle
    omega
  · by_cases h : j ≤ i
    · exact h
    have hle : i + 1 ≤ j := by omega
    have := Nat.mul_le_mul_right width hle
    omega

/-- If a shared bit selects the upper half of the containing interval, the
complements of the interval endpoints recover its midpoint complement. -/
theorem midpoint_identity (weight lo mid hi : Nat) (bit : Bool)
    (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (hbit : lo ≤ weight → weight < hi → (bit = true ↔ mid ≤ weight)) :
    (below weight lo || (!bit && below weight hi)) = below weight mid := by
  by_cases hbefore : weight < lo
  · have hm : weight < mid := by omega
    simp [below, hbefore, hm]
  by_cases hafter : hi ≤ weight
  · have hm : ¬ weight < mid := by omega
    have hh : ¬ weight < hi := by omega
    simp [below, hbefore, hm, hh]
  have hwlo : lo ≤ weight := by omega
  have hwhi : weight < hi := by omega
  have hb := hbit hwlo hwhi
  cases bit <;> simp_all [below] <;> omega

/-- One shared weight bit, computed from the positive midpoint thresholds and
already known complemented upper endpoints. -/
def levelBit (weight half blocks : Nat) (negEndpoints : Nat → Bool) : Bool :=
  (List.range blocks).any fun i =>
    threshold weight (i * (2 * half) + half) && negEndpoints (i + 1)

theorem levelBit_eq_true (weight half blocks : Nat) (negEndpoints : Nat → Bool)
    (hends : ∀ i ≤ blocks, negEndpoints i = below weight (i * (2 * half))) :
    levelBit weight half blocks negEndpoints = true ↔
      ∃ i, i < blocks ∧ i * (2 * half) + half ≤ weight ∧
        weight < (i + 1) * (2 * half) := by
  simp only [levelBit, List.any_eq_true, List.mem_range, Bool.and_eq_true,
    threshold, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi, hm, hz⟩
    have he := hends (i + 1) (by omega)
    rw [he] at hz
    exact ⟨i, hi, hm, by simpa [below] using hz⟩
  · rintro ⟨i, hi, hm, hh⟩
    refine ⟨i, hi, hm, ?_⟩
    rw [hends (i + 1) (by omega)]
    simpa [below] using hh

/-- Inside a particular half-open interval, the shared bit selects exactly
that interval's upper half. -/
theorem levelBit_local (weight half blocks i : Nat) (negEndpoints : Nat → Bool)
    (hends : ∀ j ≤ blocks, negEndpoints j = below weight (j * (2 * half)))
    (hi : i < blocks) (hlo : i * (2 * half) ≤ weight)
    (hhi : weight < (i + 1) * (2 * half)) :
    levelBit weight half blocks negEndpoints = true ↔
      i * (2 * half) + half ≤ weight := by
  rw [levelBit_eq_true weight half blocks negEndpoints hends]
  constructor
  · rintro ⟨j, hj, hm, hh⟩
    have hjlo : j * (2 * half) ≤ weight := by omega
    have hij := interval_index_unique weight (2 * half) i j hlo hhi hjlo hh
    subst j
    exact hm
  · intro hm
    exact ⟨i, hi, hm, hhi⟩

/-- One dyadic refinement step computes every new midpoint complement. -/
theorem midpoint_from_levelBit (weight half blocks i : Nat) (negEndpoints : Nat → Bool)
    (hends : ∀ j ≤ blocks, negEndpoints j = below weight (j * (2 * half)))
    (hi : i < blocks) :
    (negEndpoints i ||
      (!(levelBit weight half blocks negEndpoints) && negEndpoints (i + 1))) =
      below weight (i * (2 * half) + half) := by
  rw [hends i (by omega), hends (i + 1) (by omega)]
  apply midpoint_identity
  · omega
  · simp only [Nat.add_mul, Nat.one_mul]
    omega
  · exact levelBit_local weight half blocks i negEndpoints hends hi

/-- Refine a grid of complemented thresholds to half its spacing. `bit` and
its complement are shared by all the new odd-indexed outputs. -/
def refineGrid (weight half blocks : Nat) (negEndpoints : Nat → Bool) : Nat → Bool :=
  let notBit := !(levelBit weight half blocks negEndpoints)
  fun j => if j % 2 = 0 then negEndpoints (j / 2)
    else negEndpoints (j / 2) || (notBit && negEndpoints (j / 2 + 1))

theorem refineGrid_even (weight half blocks i : Nat) (negEndpoints : Nat → Bool) :
    refineGrid weight half blocks negEndpoints (2 * i) = negEndpoints i := by
  have hm : (2 * i) % 2 = 0 := by omega
  have hd : (2 * i) / 2 = i := by omega
  simp [refineGrid, hm, hd]

theorem refineGrid_odd (weight half blocks i : Nat) (negEndpoints : Nat → Bool) :
    refineGrid weight half blocks negEndpoints (2 * i + 1) =
      (negEndpoints i ||
        (!(levelBit weight half blocks negEndpoints) && negEndpoints (i + 1))) := by
  have hd : (2 * i + 1) / 2 = i := by omega
  simp [refineGrid, hd]

/-- A complete level preserves old threshold complements and establishes the
new ones, using one shared complemented level bit. -/
theorem refineGrid_correct (weight half blocks : Nat) (negEndpoints : Nat → Bool)
    (hends : ∀ i ≤ blocks, negEndpoints i = below weight (i * (2 * half))) :
    ∀ j ≤ 2 * blocks,
      refineGrid weight half blocks negEndpoints j = below weight (j * half) := by
  intro j hj
  by_cases heven : j % 2 = 0
  · have heq : j = 2 * (j / 2) := by omega
    have hi : j / 2 ≤ blocks := by omega
    rw [heq, refineGrid_even, hends (j / 2) hi]
    congr 1
    ac_rfl
  · have heq : j = 2 * (j / 2) + 1 := by omega
    have hi : j / 2 < blocks := by omega
    rw [heq, refineGrid_odd, midpoint_from_levelBit weight half blocks (j / 2) negEndpoints hends hi]
    congr 1
    simp only [Nat.add_mul, Nat.one_mul]
    ac_rfl

/-- Descend all remaining dyadic levels. The incoming grid has spacing
`2^remaining`; the returned grid has unit spacing. -/
def refineToUnits (weight : Nat) : Nat → Nat → (Nat → Bool) → (Nat → Bool)
  | 0, _, negEndpoints => negEndpoints
  | remaining + 1, blocks, negEndpoints =>
      refineToUnits weight remaining (2 * blocks)
        (refineGrid weight (2 ^ remaining) blocks negEndpoints)

/-- Universal semantic correctness of the entire dyadic threshold stage. -/
theorem refineToUnits_correct (weight remaining blocks : Nat) (negEndpoints : Nat → Bool)
    (hends : ∀ i ≤ blocks, negEndpoints i = below weight (i * 2 ^ remaining)) :
    ∀ j ≤ blocks * 2 ^ remaining,
      refineToUnits weight remaining blocks negEndpoints j = below weight j := by
  induction remaining generalizing blocks negEndpoints with
  | zero => simpa [refineToUnits] using hends
  | succ remaining ih =>
    have hend : ∀ i ≤ blocks,
        negEndpoints i = below weight (i * (2 * 2 ^ remaining)) := by
      simpa [Nat.pow_succ, Nat.mul_comm] using hends
    have hrefined := refineGrid_correct weight (2 ^ remaining) blocks negEndpoints hend
    intro j hj
    simp only [refineToUnits]
    apply ih (2 * blocks) (refineGrid weight (2 ^ remaining) blocks negEndpoints) hrefined j
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hj

/-- Initially only the two endpoint complements, at indices 0 and 1, matter. -/
def initialEndpoints (i : Nat) : Bool := decide (0 < i)

def thresholdInverter (weight levels : Nat) : Nat → Bool :=
  refineToUnits weight levels 1 initialEndpoints

/-- Given positive thresholds and weight below `2^levels`, the dyadic stage
recovers every threshold complement, including both endpoints. -/
theorem thresholdInverter_correct (weight levels : Nat) (hw : weight < 2 ^ levels) :
    ∀ j ≤ 2 ^ levels, thresholdInverter weight levels j = !(threshold weight j) := by
  have hends : ∀ i ≤ 1, initialEndpoints i = below weight (i * 2 ^ levels) := by
    intro i hi
    by_cases hz : i = 0
    · subst i
      simp [initialEndpoints, below]
    · have hone : i = 1 := by omega
      subst i
      simp [initialEndpoints, below, hw]
  have h := refineToUnits_correct weight levels 1 initialEndpoints hends
  intro j hj
  rw [thresholdInverter, h j (by simpa using hj)]
  exact below_eq_not_threshold weight j

end ThresholdInverterCore

-- The final semantic theorem depends on all threshold-refinement lemmas.
#print axioms ThresholdInverterCore.thresholdInverter_correct
#print axioms ThresholdInverterCore.comparator_recovery
