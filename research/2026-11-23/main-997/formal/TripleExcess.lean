import BoundaryRigidity
import DoubleExcess

/-
The boundary cut proves the exact L-meta-997 refund inequality when the
heavy excess is at most 3*k-1. The full target remains open.
This is a checked-helper assembly with the existing replacement semantics.
Apache-2.0.
-/

namespace PEqualNP.Research.TripleExcess

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.BoundaryActivation
open PEqualNP.Research.HeavyReplacement
open PEqualNP.Research.DoubleExcess

/-- Replacement-circuit version, allowing any externally justified refund
budget R. No properness assumption on the target sets is required. -/
theorem boundary_refund_bound {n m k : ℕ} (D : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Y : Finset (Fin n))
    (z u : ℕ) (y : Fin n → Bool) (R : ℕ) (hk : 2 ≤ k)
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
    (hexcess : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - k - 1 else 0) ≤ 3 * k - 1) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
      D.size + R + m := by
  classical
  have hbudget := private_outside_minterm_count D S z u y hG hzgate huz hy hmin
  have hlight := light_window_sum_bound D S out z hG hz hinter hwindow
  have hweighted := weighted_le_light_excess S Y hk
  by_contra! hfail
  have hW : (outsideWide D S z).card ≤ 2 * k - 2 := by omega
  have hfull := boundary_activation_sum D S out z hk hG hz hinter hW hwindow
  have hterm (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤ (S i).card - 1 + 1 := by
    have hm := Nat.min_le_right k (S i).card
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.mul_one] at hsum
  omega

/-- The original one-NOT hypotheses plus total heavy excess at most 3*|Y|-1
prove the exact posted refund inequality. -/
theorem one_not_refund_bound_triple_excess {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hk : 2 ≤ Y.card)
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
      3 * Y.card - 1) :
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
  have h := boundary_refund_bound D S out Y (n + i0.val) u (bit Y)
    (refundGates C S Y).card hk hG (replC_true C.gates i0) hzgate hlt hy hmin hinter hwindow
    (forced_refund_count C S out Y hout hinter) hexcess
  have hsize : D.size = C.size := by simp [D, replC, Circuit.size]
  simpa only [hsize] using h

end PEqualNP.Research.TripleExcess

#print axioms PEqualNP.Research.TripleExcess.boundary_refund_bound
#print axioms PEqualNP.Research.TripleExcess.one_not_refund_bound_triple_excess
