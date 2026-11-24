import OutsideIncidence
import ClauseMinterm
import HeavyReplacement

/-
Crossing-pair clauses settle the exact L-meta-997 refund inequality.
The clause is semantic and need not belong to the target family.
-/

namespace PEqualNP.Research.PairClause

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideIncidence
open PEqualNP.Research.ClauseMinterm
open PEqualNP.Research.HeavyReplacement

/-- If the NOT input requires a or b, with a in Y and b outside Y, the
stronger unweighted set-size sum is paid by gates, exact refunds, and m. -/
theorem crossing_pair_full_count {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (a b : Fin n) (ha : a ∈ Y) (hb : b ∉ Y)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false)
    (hpair : ∀ x : Fin n → Bool, x a = false → x b = false → value C x (n + t) = true) :
    (∑ i : Fin m, (S i).card) ≤ C.size + (refundGates C S Y).card + m := by
  classical
  have hk : 0 < Y.card := Finset.card_pos.mpr ⟨a, ha⟩
  have hzero : value C (fun _ : Fin n => false) (n + t) = true :=
    hbelow _ (by simpa using hk)
  obtain ⟨i0, hit, hop, u, hhead, hlt⟩ := not_of_window_drop C t (bit Y) hgate hnot hzero hfalse
  have hu : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q = i0 := by
    intro q hq
    apply Fin.ext
    exact (hnot q hq).trans hit.symm
  have hne : a ≠ b := by intro h; exact hb (h ▸ ha)
  have hT : ∀ x : Fin n → Bool, (∀ p ∈ ({a, b} : Finset (Fin n)), x p = false) →
      value ⟨C.gates, C.output⟩ x u = false := by
    intro x hx
    have hz : value ⟨C.gates, C.output⟩ x (n + i0.val) = true := by
      simpa only [hit] using hpair x (hx a (by simp)) (hx b (by simp))
    rw [orig_not_value C.gates i0 C.output u hop hhead hlt x] at hz
    simpa using hz
  have hcount := one_not_clause_window_bound_explicit (k := Y.card)
    C.gates C.output S out i0 u (bit Y) {a, b} a hgate hu hop hhead hlt hinter hout
    (by intro x hx; simpa only [hit] using hbelow x hx)
    (by simpa only [hit] using hfalse) hT (by simp)
  have herase : ({a, b} : Finset (Fin n)).erase a = {b} := by simp [hne]
  rw [herase] at hcount
  simp only [Finset.sum_singleton] at hcount
  have hdegree := outside_large_incidence_refund C S out Y b hb hout hinter
  change (Finset.univ.filter (fun i : Fin m => b ∈ S i ∧ 2 ≤ (S i).card)).card ≤
    (refundGates C S Y).card + Y.card at hdegree
  have hpred : (∑ i : Fin m, ((S i).card - 1)) ≤ C.size + (refundGates C S Y).card := by
    unfold Circuit.size
    omega
  have hterm (i : Fin m) : (S i).card ≤ (S i).card - 1 + 1 := by omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.mul_one] at hsum
  omega

/-- The posted weighted inequality is a consequence of the stronger count. -/
theorem one_not_refund_bound_crossing_pair {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (a b : Fin n) (ha : a ∈ Y) (hb : b ∉ Y)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false)
    (hpair : ∀ x : Fin n → Bool, x a = false → x b = false → value C x (n + t) = true) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  apply le_trans _ (crossing_pair_full_count C S out t Y a b ha hb
    hgate hnot hinter hout hbelow hfalse hpair)
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact Nat.min_le_right _ _

end PEqualNP.Research.PairClause

#print axioms PEqualNP.Research.PairClause.crossing_pair_full_count
#print axioms PEqualNP.Research.PairClause.one_not_refund_bound_crossing_pair
