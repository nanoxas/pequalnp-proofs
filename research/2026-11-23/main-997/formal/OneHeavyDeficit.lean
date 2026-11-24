import BoundaryRigidity
import SmallWindow

/-
At most one deficient heavy C1 private class suffices for the full weighted
bound, with no restriction on the number of outside gates. The single
residual demand is paid by the checked compensated-private cut. The result
does not need refund credits. The unrestricted L-meta-997 target remains
open. Apache-2.0; uses the checked replacement semantics adapted from986.
-/

namespace PEqualNP.Research.OneHeavyDeficit

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.BoundaryActivation
open PEqualNP.Research.HeavyReplacement
open PEqualNP.Research.SmallWindow

/-- Heavy target classes whose full private demand is not already paid. -/
noncomputable def deficientHeavy {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) (z : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => Disjoint (S i) Y ∧
    (lightAssigned C (S i) z).card < (S i).card - 1

lemma private_outside_count {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) :
    (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card +
      (outsideWide C S z).card ≤ C.size := by
  classical
  let G := Finset.univ.biUnion (fun i => lightAssigned C (S i) z)
  let W := outsideWide C S z
  have hd : Disjoint G W := by
    apply Finset.disjoint_left.mpr
    intro w hwG hwW
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hwG
    exact (Finset.mem_filter.mp hwW).2.2.2 i (Finset.mem_filter.mp hwi).2.2.1
  have hG : G ⊆ Finset.Ico n (n + C.size) :=
    (lightAssigned_union_subset C S z).trans (Finset.erase_subset _ _)
  have hW : W ⊆ Finset.Ico n (n + C.size) := Finset.filter_subset _ _
  have hc := Finset.card_le_card (Finset.union_subset hG hW)
  rw [Finset.card_union_of_disjoint hd] at hc
  simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hc

/-- Only the heavy deficiencies matter: light targets need their smaller
window quota, even when their full private demand is deficient. -/
theorem one_heavy_private_sum {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (Y : Finset (Fin n)) (z : ℕ) (hk : 2 ≤ k)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hD : (deficientHeavy C S Y z).card ≤ 1) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - 1
      else min k (S i).card - 1) ≤
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card +
        (outsideWide C S z).card := by
  classical
  let r := (outsideWide C S z).card
  have hpos (i : Fin m) :=
    window_singleton_positive (k := k) C (S i) (out i) (by omega) (hwindow i)
  have hzero (i : Fin m) : value C (fun _ : Fin n => false) (out i) = false := by
    apply window_negative C (S i) (out i) (hwindow i)
    · simpa using (show 0 < k by omega)
    · simp
  have hterm (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card - 1 else min k (S i).card - 1) ≤
        (lightAssigned C (S i) z).card +
          (if Disjoint (S i) Y ∧ (lightAssigned C (S i) z).card < (S i).card - 1
            then r else 0) := by
    by_cases hh : Disjoint (S i) Y
    · by_cases hd : (lightAssigned C (S i) z).card < (S i).card - 1
      · simpa only [ite_eq_left hh, ite_eq_left (And.intro hh hd)] using
          compensated_private_count C S z hG hz hinter i (out i) (hpos i) (hzero i)
      · simp only [ite_eq_left hh, and_false, hd, ite_false, Nat.add_zero]
        omega
    · have hnot : ¬ (Disjoint (S i) Y ∧
          (lightAssigned C (S i) z).card < (S i).card - 1) := fun h => hh h.1
      simpa only [ite_eq_right hh, ite_eq_right hnot, Nat.add_zero] using
        light_window_bound C (S i) (out i) z hG hz (hwindow i)
  have hcharge : (∑ i : Fin m,
      if Disjoint (S i) Y ∧ (lightAssigned C (S i) z).card < (S i).card - 1
      then r else 0) = (deficientHeavy C S Y z).card * r := by
    rw [← Finset.sum_filter]
    simp [deficientHeavy]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, hcharge] at hsum
  have hsumcard : (∑ i : Fin m, (lightAssigned C (S i) z).card) =
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card :=
    (Finset.card_biUnion (lightAssigned_pairwise_disjoint C S z hinter)).symm
  rw [hsumcard] at hsum
  have hpaid := Nat.mul_le_mul_right r hD
  simp only [Nat.one_mul] at hpaid
  exact hsum.trans (Nat.add_le_add_left hpaid _)

theorem one_heavy_window_bound {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (Y : Finset (Fin n)) (z : ℕ) (hk : 2 ≤ k)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hD : (deficientHeavy C S Y z).card ≤ 1) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
      C.size + m := by
  classical
  have hcount := one_heavy_private_sum C S out Y z hk hG hz hinter hwindow hD
  have hbudget := private_outside_count C S z
  have hterm (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
        (if Disjoint (S i) Y then (S i).card - 1 else min k (S i).card - 1) + 1 := by
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.mul_one] at hsum
  omega

/-- Original one-NOT semantics. The hypothesis concerns only heavy private
classes in the actual true-NOT replacement, and places no bound on r. -/
theorem one_not_one_heavy_deficit {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false)
    (hD : (deficientHeavy (replC C.gates t) S Y (n + t)).card ≤ 1) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + m := by
  classical
  by_cases hsmall : Y.card ≤ 2
  · exact one_not_small_window_bound C S out t Y hsmall hgate hnot hinter hout hbelow hfalse
  have hk : 2 ≤ Y.card := by omega
  have hzero : value C (fun _ : Fin n => false) (n + t) = true :=
    hbelow _ (by simpa using (show 0 < Y.card by omega))
  obtain ⟨i0, hit, _hop, _u, _hhead, _hlt⟩ :=
    not_of_window_drop C t (bit Y) hgate hnot hzero hfalse
  have hu : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q = i0 := by
    intro q hq
    apply Fin.ext
    exact (hnot q hq).trans hit.symm
  let D := replC C.gates i0.val
  have hG := replC_gates C.gates i0 hgate hu
  have hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < Y.card →
      value D x (out i) = decide (∃ p ∈ S i, x p = true) := by
    intro i x hx
    have hz : value ⟨C.gates, C.output⟩ x (n + i0.val) = true := by
      simpa only [hit] using hbelow x hx
    rw [replC_eq C.gates i0 C.output x hz (out i)]
    exact hout i x
  have hD' : (deficientHeavy D S Y (n + i0.val)).card ≤ 1 := by
    simpa only [D, hit] using hD
  have h := one_heavy_window_bound D S out Y (n + i0.val) hk hG
    (replC_true C.gates i0) hinter hwindow hD'
  have hsize : D.size = C.size := by simp [D, replC, Circuit.size]
  simpa only [hsize] using h

/-- Any failure of the exact posted inequality needs at least two deficient
heavy C1 private classes, independently of all outside-count estimates. -/
theorem one_not_failure_has_two_heavy_deficits {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false)
    (hfail : C.size + (refundGates C S Y).card + m <
      ∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) :
    2 ≤ (deficientHeavy (replC C.gates t) S Y (n + t)).card := by
  by_contra! hsmall
  have h := one_not_one_heavy_deficit C S out t Y hgate hnot hinter hout hbelow hfalse
    (by omega)
  omega

end PEqualNP.Research.OneHeavyDeficit

#print axioms PEqualNP.Research.OneHeavyDeficit.one_heavy_private_sum
#print axioms PEqualNP.Research.OneHeavyDeficit.one_not_one_heavy_deficit
#print axioms PEqualNP.Research.OneHeavyDeficit.one_not_failure_has_two_heavy_deficits
