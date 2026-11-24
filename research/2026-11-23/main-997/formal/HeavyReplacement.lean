import NotWindow
import OrPrivateCount

/-
False replacement for a single NOT gate. Same-index list machinery is adapted
from the accepted L-meta-986 and the checked NotWindow helper, under Apache-2.0.
The new direction preserves every gate index, is globally below the original,
and agrees on all inputs containing a given false-NOT witness.
-/

namespace PEqualNP.Research.HeavyReplacement

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

lemma repl_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

def repl0C (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨GateOp.or, []⟩, 0⟩

lemma repl0C_size (gates : List Gate) (i0 : ℕ) : (repl0C gates i0).size = gates.length := by
  simp [repl0C, Circuit.size]

lemma repl0C_gates (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (repl0C gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [repl0C] using hk
  by_cases hki : i0.val = k
  · simp [repl0C, hki]
  · have e : (repl0C gates i0.val).gates[k] = gates[k] := by
      simp [repl0C, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma repl0C_false {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    value (repl0C gates i0.val) x (n + i0.val) = false := by
  have h := gate_value (repl0C gates i0.val) x (n + i0.val) (by omega)
    (by rw [repl0C_size]; omega)
  simp only at h
  rw [h]
  simp [repl0C, GateOp.eval]

lemma repl0C_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (repl0C gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (repl0C gates i0) x r else false) := by
  have h := gate_value (repl0C gates i0) x w hn (by rw [repl0C_size]; exact hw)
  simp only at h
  rw [h]
  have e : (repl0C gates i0).gates[w - n]'(by simp [repl0C]; omega) = gates[w - n]'(by omega) := by
    simp only [repl0C, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma repl0C_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = false) (w : ℕ) :
    value (repl0C gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (repl0C gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact repl0C_false gates i0 x
      · rw [orig_value gates o x w (by omega) hw, repl0C_other gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (repl0C gates i0.val) x w (by rw [repl0C_size]; omega)]

/-- Replacement changes no earlier wire, independently of the input value
at the replaced gate. Malformed reads remain false through the prefix. -/
lemma repl0C_prefix_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (w : ℕ) :
    w < n + i0.val → value (repl0C gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hbefore
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (repl0C gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    have hw : w < n + gates.length := by have := i0.isLt; omega
    rw [orig_value gates o x w (by omega) hw,
      repl0C_other gates i0.val x w (by omega) hw (by omega)]
    apply repl_eval_congr
    intro r _
    by_cases hr : r < w
    · simpa [hr] using ih r hr (by omega)
    · simp [hr]

lemma repl0C_prefix_support {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (o w : ℕ) (hbefore : w < n + i0.val) :
    support (n := n) (repl0C gates i0.val) w = support (n := n) ⟨gates, o⟩ w := by
  ext p
  simp only [mem_support]
  rw [repl0C_prefix_eq gates i0 o _ w hbefore]

/-- Every pre-replacement gate operation is preserved at the same index. -/
lemma repl0C_gate_before (gates : List Gate) (i0 : Fin gates.length)
    (j : Fin gates.length) (hbefore : j.val < i0.val) :
    ((repl0C gates i0.val).gates.get
      ⟨j.val, by simp [repl0C]⟩).op = (gates.get j).op := by
  have hne : i0.val ≠ j.val := by omega
  simp [repl0C, hne]

lemma repl0C_le {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (x : Fin n → Bool) (w : ℕ) :
    value (repl0C gates i0.val) x w = true → value ⟨gates, o⟩ x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (repl0C gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact id
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · intro hv
        rw [hne, repl0C_false gates i0 x] at hv
        contradiction
      · rw [orig_value gates o x w (by omega) hw, repl0C_other gates i0.val x w (by omega) hw hne]
        have hop : (gates[w - n]'(by omega)).op = GateOp.and ∨
            (gates[w - n]'(by omega)).op = GateOp.or := by
          rcases (hgate (gates[w - n]'(by omega)) (List.getElem_mem _)).1 with hop | hop | hop
          · exact Or.inl hop
          · exact Or.inr hop
          · have := congrArg Fin.val (hnot ⟨w - n, by omega⟩ hop)
            simp only at this
            omega
        apply repl_eval_mono _ hop
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · intro h
      rw [missing_value (repl0C gates i0.val) x w (by rw [repl0C_size]; omega)] at h
      exact absurd h (by simp)

lemma repl0C_above_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o u : ℕ)
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hop : (gates.get i0).op = GateOp.not)
    (hhead : (gates.get i0).inputs.head? = some u)
    (hlt : u < n + i0.val) (y x : Fin n → Bool)
    (hy : value ⟨gates, o⟩ y (n + i0.val) = false)
    (hxy : ∀ p, y p = true → x p = true) (w : ℕ) :
    value (repl0C gates i0.val) x w = value ⟨gates, o⟩ x w := by
  have huy : value (repl0C gates i0.val) y u = true := by
    rw [repl0C_prefix_eq gates i0 o y u hlt]
    rw [orig_not_value gates i0 o u hop hhead hlt y] at hy
    simpa using hy
  have hux := value_mono (repl0C gates i0.val)
    (repl0C_gates gates i0 hgate hnot) y x hxy u huy
  rw [repl0C_prefix_eq gates i0 o x u hlt] at hux
  have hz : value ⟨gates, o⟩ x (n + i0.val) = false := by
    rw [orig_not_value gates i0 o u hop hhead hlt x, hux]
    rfl
  exact repl0C_eq gates i0 o x hz w

open PEqualNP.Research.OrPrivateCount

lemma repl0C_output_negative {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (o out : ℕ) (T : Finset (Fin n))
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hout : ∀ x : Fin n → Bool, value ⟨gates, o⟩ x out = decide (∃ p ∈ T, x p = true)) :
    value (repl0C gates i0.val) (negative T) out = false := by
  apply Bool.eq_false_iff.mpr
  intro hv
  have h := repl0C_le gates i0 o hgate hnot (negative T) out hv
  rw [hout] at h
  simp [negative] at h

lemma repl0C_output_positive {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (o out u : ℕ) (Y T : Finset (Fin n))
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hop : (gates.get i0).op = GateOp.not)
    (hhead : (gates.get i0).inputs.head? = some u)
    (hlt : u < n + i0.val)
    (hy : value ⟨gates, o⟩ (bit Y) (n + i0.val) = false)
    (hout : ∀ x : Fin n → Bool, value ⟨gates, o⟩ x out = decide (∃ p ∈ T, x p = true)) :
    ∀ p ∈ T, value (repl0C gates i0.val) (baseSamples Y p) out = true := by
  intro p hp
  rw [repl0C_above_eq gates i0 o u hgate hnot hop hhead hlt (bit Y) (baseSamples Y p)
    hy (by intro q hq; exact decide_eq_true (Or.inl (of_decide_eq_true hq))) out]
  rw [hout]
  exact decide_eq_true ⟨p, hp, by simp [baseSamples]⟩

/-- The OR-only private heavy count applies to the original one-NOT circuit
after replacing its NOT by false, while preserving gate indices and count. -/
theorem one_not_heavy_or_count {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (o out u : ℕ) (Y T : Finset (Fin n))
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hop : (gates.get i0).op = GateOp.not)
    (hhead : (gates.get i0).inputs.head? = some u)
    (hlt : u < n + i0.val) (hYT : Disjoint Y T)
    (hy : value ⟨gates, o⟩ (bit Y) (n + i0.val) = false)
    (hout : ∀ x : Fin n → Bool, value ⟨gates, o⟩ x out = decide (∃ p ∈ T, x p = true)) :
    T.card - 1 ≤ ((heavyAssigned (repl0C gates i0.val) Y T).filter (· ≤ out)).card := by
  apply heavy_or_prefix_count (repl0C gates i0.val)
    (repl0C_gates gates i0 hgate hnot) Y T hYT out
  · exact repl0C_output_negative gates i0 o out T hgate hnot hout
  · exact repl0C_output_positive gates i0 o out u Y T hgate hnot hop hhead hlt hy hout

/-- A drop from true at zero to false at y identifies the unique NOT and
its valid first operand directly from the original circuit hypotheses. -/
lemma not_of_window_drop {n : ℕ} (C : Circuit) (t : ℕ) (y : Fin n → Bool)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hzero : value C (fun _ : Fin n => false) (n + t) = true)
    (hfalse : value C y (n + t) = false) :
    ∃ i0 : Fin C.gates.length, i0.val = t ∧ (C.gates.get i0).op = GateOp.not ∧
      ∃ u, (C.gates.get i0).inputs.head? = some u ∧ u < n + i0.val := by
  have ht : t < C.gates.length := by
    by_contra! hbad
    rw [missing_value C _ (n + t) (by simpa [Circuit.size] using Nat.add_le_add_left hbad n)] at hzero
    contradiction
  let i0 : Fin C.gates.length := ⟨t, ht⟩
  have huniq : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q = i0 := by
    intro q hq
    apply Fin.ext
    exact hnot q hq
  have hop : (C.gates.get i0).op = GateOp.not := by
    by_contra hnon
    have hmono : ∀ g ∈ C.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hgate g hg
      refine ⟨?_, hlen⟩
      rcases hop with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · obtain ⟨q, hq⟩ := List.mem_iff_get.mp hg
        have hqn : (C.gates.get q).op = GateOp.not := by rw [hq]; exact hop
        have hqi := huniq q hqn
        exact False.elim (hnon (by simpa [hqi] using hqn))
    have hy := value_mono C hmono (fun _ : Fin n => false) y
      (by intro p hp; contradiction) (n + t) hzero
    rw [hfalse] at hy
    contradiction
  exact ⟨i0, rfl, hop, not_input_of_false C.gates i0 C.output y hop hfalse⟩

/-- The original drop hypotheses give a monotone circuit of the same size,
globally below the original and identical on all inputs containing Y. -/
theorem false_window_replacement {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hzero : value C (fun _ : Fin n => false) (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false) :
    ∃ D : Circuit, D.size = C.size ∧
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ (x : Fin n → Bool) (w : ℕ), value D x w = true → value C x w = true) ∧
      (∀ (x : Fin n → Bool), (∀ p ∈ Y, x p = true) →
        ∀ w : ℕ, value D x w = value C x w) := by
  obtain ⟨i0, hit, hop, u, hhead, hlt⟩ := not_of_window_drop C t (bit Y) hgate hnot hzero hfalse
  have hu : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q = i0 := by
    intro q hq
    apply Fin.ext
    exact (hnot q hq).trans hit.symm
  refine ⟨repl0C C.gates i0.val, ?_, repl0C_gates C.gates i0 hgate hu,
    repl0C_le C.gates i0 C.output hgate hu, ?_⟩
  · simp [repl0C, Circuit.size]
  · intro x hx w
    apply repl0C_above_eq C.gates i0 C.output u hgate hu hop hhead hlt (bit Y) x
    · simpa only [hit] using hfalse
    · intro p hp
      exact hx p (of_decide_eq_true hp)

end PEqualNP.Research.HeavyReplacement

#print axioms PEqualNP.Research.HeavyReplacement.repl0C_le
#print axioms PEqualNP.Research.HeavyReplacement.repl0C_above_eq
#print axioms PEqualNP.Research.HeavyReplacement.one_not_heavy_or_count
#print axioms PEqualNP.Research.HeavyReplacement.false_window_replacement
