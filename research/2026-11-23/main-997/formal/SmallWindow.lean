import RefundCount
import HeavyReplacement

/-
Small-window cases of the exact L-meta-997 inequality. Heavy OR charges are
false on Y; distinct nontrivial light outputs are true there. Their disjoint
union proves the bound without a refund when |Y| is at most two.
-/

namespace PEqualNP.Research.SmallWindow

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OrPrivateCount
open PEqualNP.Research.HeavyReplacement

theorem monotone_replacement_small_bound {n m k : ℕ} (C D : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Y : Finset (Fin n))
    (hk : k ≤ 2)
    (hsize : D.size = C.size)
    (hG : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hbelow : ∀ (x : Fin n → Bool) (w : ℕ), value D x w = true → value C x w = true)
    (hagrees : ∀ x : Fin n → Bool, (∀ p ∈ Y, x p = true) →
      ∀ w, value D x w = value C x w)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
      C.size + m := by
  classical
  let H := Finset.univ.filter fun i : Fin m => Disjoint (S i) Y
  let L := Finset.univ.filter fun i : Fin m => ¬ Disjoint (S i) Y ∧ 2 ≤ (S i).card
  let A := H.biUnion fun i => heavyAssigned D Y (S i)
  let B := L.image out
  have hneg (i : Fin m) : value D (negative (S i)) (out i) = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    have h := hbelow (negative (S i)) (out i) hv
    rw [hout] at h
    simp [negative] at h
  have hpos (i : Fin m) (p : Fin n) (hp : p ∈ S i) :
      value D (baseSamples Y p) (out i) = true := by
    rw [hagrees (baseSamples Y p) (by intro q hq; exact decide_eq_true (Or.inl hq))]
    rw [hout]
    exact decide_eq_true ⟨p, hp, by simp [baseSamples]⟩
  have hd : (H : Set (Fin m)).PairwiseDisjoint (fun i => heavyAssigned D Y (S i)) := by
    intro i hi j hj hij
    have hiY : Disjoint Y (S i) := (Finset.mem_filter.mp hi).2.symm
    have hjY : Disjoint Y (S j) := (Finset.mem_filter.mp hj).2.symm
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hai := (Finset.mem_filter.mp hwi).2.2.1
    have haj := (Finset.mem_filter.mp hwj).2.2.1
    have hwide := (Finset.mem_filter.mp hwi).2.2.2
    have hsub : sampleSupport D (baseSamples Y) w ⊆ S i ∩ S j := by
      intro p hp
      exact Finset.mem_inter.mpr
        ⟨sampleSupport_subset D hG Y (S i) hiY w hai hp,
         sampleSupport_subset D hG Y (S j) hjY w haj hp⟩
    have hcard := Finset.card_le_card hsub
    have hsmall := hinter i j hij
    omega
  have hA : (∑ i ∈ H, ((S i).card - 1)) ≤ A.card := by
    calc
      (∑ i ∈ H, ((S i).card - 1)) ≤ ∑ i ∈ H, (heavyAssigned D Y (S i)).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact heavy_or_count D hG Y (S i) (Finset.mem_filter.mp hi).2.symm (out i) (hneg i) (hpos i)
      _ = A.card := (Finset.card_biUnion hd).symm
  have hB : B.card = L.card := by
    exact Finset.card_image_of_injOn (output_injOn_large C S out L hout hinter
      (fun i hi => (Finset.mem_filter.mp hi).2.2))
  have hAfalse : ∀ w ∈ A, value D (bit Y) w = false := by
    intro w hw
    obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw
    have hdis : Disjoint Y (S i) := (Finset.mem_filter.mp hi).2.symm
    have ha := (Finset.mem_filter.mp hwi).2.2.1
    apply Bool.eq_false_iff.mpr
    intro hv
    have hm : value D (negative (S i)) w = true := by
      apply value_mono D hG (bit Y) (negative (S i)) _ w hv
      intro p hp
      apply decide_eq_true
      exact fun hpS => Finset.disjoint_left.mp hdis (of_decide_eq_true hp) hpS
    rw [ha] at hm
    contradiction
  have hBtrue : ∀ w ∈ B, value D (bit Y) w = true := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hhit := (Finset.mem_filter.mp hi).2.1
    obtain ⟨p, hpS, hpY⟩ := Finset.not_disjoint_iff.mp hhit
    rw [hagrees (bit Y) (by intro q hq; exact decide_eq_true hq), hout]
    exact decide_eq_true ⟨p, hpS, decide_eq_true hpY⟩
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have h := hBtrue w hb
    rw [hAfalse w ha] at h
    contradiction
  have hAsub : A ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    have h := (Finset.mem_filter.mp hi).1
    simpa only [hsize] using h
  have hBsub : B ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_Ico.mpr (output_gate_of_card C S out hout i (Finset.mem_filter.mp hi).2.2)
  have htotal : A.card + L.card ≤ C.size := by
    have h := Finset.card_le_card (Finset.union_subset hAsub hBsub)
    rw [Finset.card_union_of_disjoint hAB, hB] at h
    simpa using h
  have hterm (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
        (if Disjoint (S i) Y then (S i).card - 1 else 0) +
        (if ¬ Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0) + 1 := by
    by_cases hi : Disjoint (S i) Y
    · simp only [hi, ite_true, not_true_eq_false, false_and, ite_false, Nat.add_zero]
      omega
    · by_cases hlarge : 2 ≤ (S i).card
      · have hm := Nat.min_le_left k (S i).card
        simp only [hi, ite_false, not_false_eq_true, true_and, hlarge, ite_true, Nat.zero_add]
        omega
      · have hm := Nat.min_le_right k (S i).card
        simp only [hi, ite_false, not_false_eq_true, true_and, hlarge, Nat.zero_add]
        omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hterm i)
  have hHsum : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - 1 else 0) =
      ∑ i ∈ H, ((S i).card - 1) := by simp [H, Finset.sum_filter]
  have hLsum : (∑ i : Fin m, if ¬ Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0) = L.card := by
    rw [Finset.card_eq_sum_ones]
    simp [L]
  simp only [Finset.sum_add_distrib, hHsum, hLsum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] at hsum
  omega

lemma zero_not_monotone_replacement {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hfalse : value C (bit (∅ : Finset (Fin n))) (n + t) = false) :
    ∃ D : Circuit, D.size = C.size ∧
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ (x : Fin n → Bool) (w : ℕ), value D x w = value C x w := by
  classical
  by_cases hn : ∃ i0 : Fin C.gates.length, (C.gates.get i0).op = GateOp.not
  · obtain ⟨i0, hop⟩ := hn
    have hit := hnot i0 hop
    have hu : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q = i0 := by
      intro q hq
      apply Fin.ext
      exact (hnot q hq).trans hit.symm
    have hy : value C (bit (∅ : Finset (Fin n))) (n + i0.val) = false := by
      simpa only [hit] using hfalse
    obtain ⟨u, hhead, hlt⟩ := not_input_of_false C.gates i0 C.output (bit (∅ : Finset (Fin n))) hop hy
    refine ⟨repl0C C.gates i0.val, ?_, repl0C_gates C.gates i0 hgate hu, ?_⟩
    · simp [repl0C, Circuit.size]
    · intro x w
      apply repl0C_above_eq C.gates i0 C.output u hgate hu hop hhead hlt (bit ∅) x hy
      intro p hp
      simp [bit] at hp
  · refine ⟨C, rfl, ?_, fun _ _ => rfl⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hgate g hg
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · obtain ⟨q, hq⟩ := List.mem_iff_get.mp hg
      exact False.elim (hn ⟨q, by rw [hq]; exact hop⟩)

/-- Both the empty-window and positive-window cases admit the same monotone
replacement interface. The empty case may have no NOT gate at all. -/
theorem window_monotone_replacement {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false) :
    ∃ D : Circuit, D.size = C.size ∧
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ (x : Fin n → Bool) (w : ℕ), value D x w = true → value C x w = true) ∧
      (∀ x : Fin n → Bool, (∀ p ∈ Y, x p = true) →
        ∀ w : ℕ, value D x w = value C x w) := by
  classical
  by_cases hY : Y = ∅
  · subst Y
    obtain ⟨D, hsize, hG, heq⟩ := zero_not_monotone_replacement C t hgate hnot hfalse
    refine ⟨D, hsize, hG, ?_, fun x _ w => heq x w⟩
    intro x w hv
    rwa [heq] at hv
  · apply false_window_replacement C t Y hgate hnot _ hfalse
    apply hbelow
    have hp : 0 < Y.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hY)
    simpa using hp

/-- The exact original assumptions prove the two-point window bound without
using any refund. This includes Y empty and malformed gate references. -/
theorem one_not_small_window_bound {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hk : Y.card ≤ 2)
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
      C.size + m := by
  obtain ⟨D, hsize, hG, hle, heq⟩ := window_monotone_replacement C t Y hgate hnot hbelow hfalse
  exact monotone_replacement_small_bound C D S out Y hk hsize hG hle heq hinter hout

/-- A checked sufficient family: every target has at most four points. -/
theorem one_not_refund_bound_max_four {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hsize : ∀ i : Fin m, (S i).card ≤ 4)
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
  by_cases hk : Y.card ≤ 2
  · have h := one_not_small_window_bound C S out t Y hk hgate hnot hinter hout hbelow hfalse
    omega
  · apply one_not_refund_bound_of_heavy_size C S out t Y (by omega) hgate hnot hinter hout hbelow hfalse
    intro i _
    have := hsize i
    omega

end PEqualNP.Research.SmallWindow

#print axioms PEqualNP.Research.SmallWindow.monotone_replacement_small_bound
#print axioms PEqualNP.Research.SmallWindow.one_not_small_window_bound
#print axioms PEqualNP.Research.SmallWindow.one_not_refund_bound_max_four
