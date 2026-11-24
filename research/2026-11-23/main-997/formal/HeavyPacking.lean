import SmallWindow
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith

/-
Finite ordered-pair packing for the heavy targets in L-meta-997. The new
combinatorial and arithmetic lemmas feed the already checked excess criterion.
This proves the n <= 3*|Y|+1 special case, not the unrestricted statement.
-/

namespace PEqualNP.Research.HeavyPacking

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

/-- A linear family uses each ordered pair of distinct points at most once. -/
theorem linear_pair_packing {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (S : ι → Finset α) (U : Finset α)
    (hsub : ∀ i ∈ I, S i ⊆ U)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∑ i ∈ I, (S i).card * ((S i).card - 1)) ≤ U.card * (U.card - 1) := by
  classical
  have hdis : (I : Set ι).PairwiseDisjoint (fun i => (S i).offDiag) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    obtain ⟨hpi1, hpi2, hne⟩ := Finset.mem_offDiag.mp hpi
    obtain ⟨hpj1, hpj2, _⟩ := Finset.mem_offDiag.mp hpj
    have hpair : {p.1, p.2} ⊆ S i ∩ S j := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Finset.mem_inter.mpr ⟨hpi1, hpj1⟩
      · have he := Finset.mem_singleton.mp ha
        subst a
        exact Finset.mem_inter.mpr ⟨hpi2, hpj2⟩
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair hne] at hc
    have hs := hinter i hi j hj hij
    omega
  have hU : I.biUnion (fun i => (S i).offDiag) ⊆ U.offDiag := by
    intro p hp
    obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
    exact Finset.offDiag_mono (hsub i hi) hpi
  calc
    (∑ i ∈ I, (S i).card * ((S i).card - 1)) =
        ∑ i ∈ I, (S i).offDiag.card := by
      simp only [Finset.offDiag_card, Nat.mul_sub_one]
    _ = (I.biUnion (fun i => (S i).offDiag)).card := (Finset.card_biUnion hdis).symm
    _ ≤ U.offDiag.card := Finset.card_le_card hU
    _ = U.card * (U.card - 1) := by rw [Finset.offDiag_card, Nat.mul_sub_one]

/-- The exact integer bound is sharp at d=2*k+1 and d=2*k+2. -/
lemma excess_pair_cost (k d : ℕ) :
    (4 * k + 2) * (d - k - 1) ≤ d * (d - 1) := by
  by_cases hd : d ≤ k + 1
  · have hz : d - k - 1 = 0 := by omega
    simp [hz]
  · have hd1 : d - 1 + 1 = d := by omega
    have he : d - k - 1 + k + 1 = d := by omega
    by_cases hlow : d ≤ 2 * k + 1
    · have h1 : 2 * k + 1 - d + d = 2 * k + 1 := by omega
      have h2 : 2 * k + 2 - d + d = 2 * k + 2 := by omega
      have hp := Nat.zero_le ((2 * k + 1 - d) * (2 * k + 2 - d))
      nlinarith
    · have h1 : d - (2 * k + 1) + (2 * k + 1) = d := by omega
      have h2 : d - (2 * k + 2) + (2 * k + 2) = d := by omega
      have hp := Nat.zero_le ((d - (2 * k + 1)) * (d - (2 * k + 2)))
      nlinarith

/-- A universe of at most 2*k+1 points leaves total excess at most k. -/
theorem linear_excess_bound {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (S : ι → Finset α) (U : Finset α) (k : ℕ)
    (hsub : ∀ i ∈ I, S i ⊆ U)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hsize : U.card ≤ 2 * k + 1) :
    (∑ i ∈ I, ((S i).card - k - 1)) ≤ k := by
  have hp := linear_pair_packing I S U hsub hinter
  have he : (4 * k + 2) * (∑ i ∈ I, ((S i).card - k - 1)) ≤
      ∑ i ∈ I, (S i).card * ((S i).card - 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => excess_pair_cost k (S i).card)
  have hU := Nat.mul_le_mul hsize (show U.card - 1 ≤ 2 * k by omega)
  have hbound : U.card * (U.card - 1) ≤ (4 * k + 2) * k := by nlinarith
  exact Nat.le_of_mul_le_mul_left (he.trans (hp.trans hbound)) (by omega)

theorem heavy_excess_bound {n m : ℕ}
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) (k : ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hsize : ((Finset.univ : Finset (Fin n)) \ Y).card ≤ 2 * k + 1) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - k - 1 else 0) ≤ k := by
  classical
  let I := Finset.univ.filter fun i : Fin m => Disjoint (S i) Y
  let U := (Finset.univ : Finset (Fin n)) \ Y
  have hsub : ∀ i ∈ I, S i ⊆ U := by
    intro i hi p hp
    have hd := (Finset.mem_filter.mp hi).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hpY => Finset.disjoint_left.mp hd hp hpY⟩
  have h := linear_excess_bound I S U k hsub (fun i _ j _ hij => hinter i j hij) hsize
  simpa only [I, Finset.sum_filter] using h

/-- Exact 997 follows when there are at most 2*|Y|+1 variables outside Y. -/
theorem one_not_refund_bound_small_complement {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hsize : ((Finset.univ : Finset (Fin n)) \ Y).card ≤ 2 * Y.card + 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  by_cases hk : 2 ≤ Y.card
  · exact one_not_refund_bound_of_excess C S out t Y hk hgate hnot hinter hout hbelow hfalse
      (heavy_excess_bound S Y Y.card hinter hsize)
  · have h := PEqualNP.Research.SmallWindow.one_not_small_window_bound C S out t Y
      (by omega) hgate hnot hinter hout hbelow hfalse
    omega

/-- Consequently, an unresolved counterexample must have n >= 3*|Y|+2. -/
theorem one_not_refund_bound_three_window {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hn : n ≤ 3 * Y.card + 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  apply one_not_refund_bound_small_complement C S out t Y _ hgate hnot hinter hout hbelow hfalse
  have hp := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) Y
  simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hp
  omega

end PEqualNP.Research.HeavyPacking

#print axioms PEqualNP.Research.HeavyPacking.linear_pair_packing
#print axioms PEqualNP.Research.HeavyPacking.excess_pair_cost
#print axioms PEqualNP.Research.HeavyPacking.one_not_refund_bound_three_window
