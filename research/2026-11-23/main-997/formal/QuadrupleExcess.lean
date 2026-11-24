import TripleExcess
import DeficientPacking
import PrivateAnd

/-
Two-deficiency accounting from the directed-separation and private-AND
counts. This proves a sufficient heavy-excess range for L-meta-997.
The unrestricted target remains open. Apache-2.0.
-/

namespace PEqualNP.Research.QuadrupleExcess

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.BoundaryActivation
open PEqualNP.Research.OrCompensation
open PEqualNP.Research.DeficientPacking
open PEqualNP.Research.PrivateAnd
open PEqualNP.Research.HeavyReplacement
open PEqualNP.Research.DoubleExcess

/-- Two deficits are paid by the outside budget once each deficient class
contains at least k-1 private AND gates. -/
lemma two_deficit_sum {m k : ℕ} (a g b : Fin m → ℕ) (R r : ℕ)
    (hk : 3 ≤ k) (hR : R ≤ r) (hr : r ≤ 3 * k - 4)
    (hD : (Finset.univ.filter (fun i : Fin m => g i < a i)).card ≤ 2)
    (hcomp : ∀ i : Fin m, a i - g i ≤ R - b i)
    (hand : ∀ i : Fin m, g i < a i → k - 1 ≤ b i) :
    (∑ i : Fin m, a i) ≤ (∑ i : Fin m, g i) + r + k := by
  classical
  let D := Finset.univ.filter fun i : Fin m => g i < a i
  by_cases hRk : k ≤ R
  · have hsum_eq : (∑ i : Fin m, (a i - g i)) = ∑ i ∈ D, (a i - g i) := by
      simp only [D, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : g i < a i
      · simp only [ite_eq_left hi]
      · have he : a i - g i = 0 := by omega
        simp only [ite_eq_right hi, he]
    have hterm (i : Fin m) (hi : i ∈ D) : a i - g i ≤ R - k + 1 := by
      have hd := (Finset.mem_filter.mp hi).2
      have hb := hand i hd
      have hc := hcomp i
      omega
    have hdelta : (∑ i : Fin m, (a i - g i)) ≤ r + k := by
      calc
        (∑ i : Fin m, (a i - g i)) = ∑ i ∈ D, (a i - g i) := hsum_eq
        _ ≤ ∑ _i ∈ D, (R - k + 1) := Finset.sum_le_sum hterm
        _ = D.card * (R - k + 1) := by simp
        _ ≤ 2 * (R - k + 1) := Nat.mul_le_mul_right _ hD
        _ ≤ r + k := by omega
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
      (fun i _ => (show a i ≤ g i + (a i - g i) by omega))
    simp only [Finset.sum_add_distrib] at hsum
    omega
  · have hle (i : Fin m) : a i ≤ g i := by
      by_contra! hi
      have hb := hand i hi
      have hc := hcomp i
      omega
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hle i)
    omega

/-- The full private demand is at most the private-gate count plus r+k
through the range r<=3*k-4. -/
theorem quadruple_private_sum {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (z : ℕ)
    (hk : 3 ≤ k)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hW : (outsideWide C S z).card ≤ 3 * k - 4)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, ((S i).card - 1)) ≤
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card +
        (outsideWide C S z).card + k := by
  classical
  have hpos (i : Fin m) := window_singleton_positive (k := k) C (S i) (out i) (by omega) (hwindow i)
  have hneg (i : Fin m) := window_negative C (S i) (out i) (hwindow i)
  have hzero (i : Fin m) : value C (fun _ : Fin n => false) (out i) = false := by
    apply hneg i
    · simpa using (show 0 < k by omega)
    · simp
  have hD := deficient_count_le_two C S out z hk hG hz hinter hW hwindow
  have hcount := two_deficit_sum
    (fun i : Fin m => (S i).card - 1)
    (fun i => (lightAssigned C (S i) z).card)
    (fun i => (opPart n C GateOp.and (lightAssigned C (S i) z)).card)
    (opPart n C GateOp.or (outsideWide C S z)).card
    (outsideWide C S z).card hk
    (Finset.card_filter_le _ _) hW hD
    (fun i => compensated_deficit C S z hG (hz _) hinter i (out i) (hpos i) (hzero i))
    (fun i hi => deficient_and_count C S z hG hz hinter i (out i) (hpos i) (hneg i) hi)
  have hsumcard : (∑ i : Fin m, (lightAssigned C (S i) z).card) =
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card :=
    (Finset.card_biUnion (lightAssigned_pairwise_disjoint C S z hinter)).symm
  simpa only [hsumcard] using hcount

/-- Replacement-circuit version, allowing any externally justified refund
budget R. No properness assumption on the target sets is required. -/
theorem quadruple_refund_bound {n m k : ℕ} (D : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Y : Finset (Fin n))
    (z u : ℕ) (y : Fin n → Bool) (R : ℕ) (hk : 3 ≤ k)
    (hG : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value D x z = true)
    (hzgate : z ∈ Finset.Ico n (n + D.size)) (huz : u < z)
    (hy : value D y u = true)
    (hmin : ∀ x : Fin n → Bool, value D x u = true →
      k ≤ (Finset.univ.filter (fun p : Fin n => x p = true)).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value D x (out i) = decide (∃ p ∈ S i, x p = true))
    (hrefund : (heavyNontrivial S Y).card ≤ R)
    (hexcess : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - k - 1 else 0) ≤ 4 * k - 3) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
      D.size + R + m := by
  classical
  have hbudget := private_outside_minterm_count D S z u y hG hzgate huz hy hmin
  have hlight := light_window_sum_bound D S out z hG hz hinter hwindow
  have hweighted := weighted_le_light_excess (k := k) S Y (by omega)
  by_contra! hfail
  have hW : (outsideWide D S z).card ≤ 3 * k - 4 := by omega
  have hfull := quadruple_private_sum D S out z hk hG hz hinter hW hwindow
  have hterm (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤ (S i).card - 1 + 1 := by
    have hm := Nat.min_le_right k (S i).card
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.mul_one] at hsum
  omega

/-- The original one-NOT hypotheses plus total heavy excess at most 4*|Y|-3
prove the exact posted refund inequality. -/
theorem one_not_refund_bound_quadruple_excess {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hk : 3 ≤ Y.card)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false)
    (hexcess : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - Y.card - 1 else 0) ≤
      4 * Y.card - 3) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  classical
  have hzero : value C (fun _ : Fin n => false) (n + t) = true :=
    hbelow _ (by simpa using (show 0 < Y.card by omega))
  obtain ⟨i0, hit, hop, u, hhead, hlt⟩ :=
    not_of_window_drop C t (bit Y) hgate hnot hzero hfalse
  have hu : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q = i0 := by
    intro q hq
    apply Fin.ext
    exact (hnot q hq).trans hit.symm
  let D := replC C.gates i0.val
  have hG := replC_gates C.gates i0 hgate hu
  have hy : value D (bit Y) u = true := by
    rw [replC_prefix_eq C.gates i0 C.output (bit Y) u hlt]
    have h : value ⟨C.gates, C.output⟩ (bit Y) (n + i0.val) = false := by
      simpa only [hit] using hfalse
    rw [orig_not_value C.gates i0 C.output u hop hhead hlt (bit Y)] at h
    simpa using h
  have hmin : ∀ x : Fin n → Bool, value D x u = true →
      Y.card ≤ (Finset.univ.filter (fun p => x p = true)).card := by
    intro x hx
    by_contra! hsmall
    have hz : value ⟨C.gates, C.output⟩ x (n + i0.val) = true := by
      simpa only [hit] using hbelow x hsmall
    have hv : value ⟨C.gates, C.output⟩ x u = true := by
      rw [← replC_prefix_eq C.gates i0 C.output x u hlt]
      exact hx
    rw [orig_not_value C.gates i0 C.output u hop hhead hlt x, hv] at hz
    contradiction
  have hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < Y.card →
      value D x (out i) = decide (∃ p ∈ S i, x p = true) := by
    intro i x hx
    have hz : value ⟨C.gates, C.output⟩ x (n + i0.val) = true := by
      simpa only [hit] using hbelow x hx
    rw [replC_eq C.gates i0 C.output x hz (out i)]
    exact hout i x
  have hzgate : n + i0.val ∈ Finset.Ico n (n + D.size) := by
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · change n + i0.val < n + (replC C.gates i0.val).size
      rw [replC_size]
      exact Nat.add_lt_add_left i0.isLt n
  have h := quadruple_refund_bound D S out Y (n + i0.val) u (bit Y)
    (refundGates C S Y).card hk hG (replC_true C.gates i0) hzgate hlt hy hmin hinter hwindow
    (forced_refund_count C S out Y hout hinter) hexcess
  have hsize : D.size = C.size := by simp [D, replC, Circuit.size]
  simpa only [hsize] using h

end PEqualNP.Research.QuadrupleExcess

#print axioms PEqualNP.Research.QuadrupleExcess.quadruple_refund_bound
#print axioms PEqualNP.Research.QuadrupleExcess.one_not_refund_bound_quadruple_excess

#print axioms PEqualNP.Research.QuadrupleExcess.quadruple_private_sum
