import LightMinterm

/-
Research bridge for the combined light-plus-minterm count. The same-index
replacement helpers through replC_eq are copied from accepted L-meta-986,
using its already-reused evaluation helpers. The source and adaptation use
Apache-2.0. New lemmas make prefix preservation and the threshold window
explicit. This file does not claim the complete L-meta-997 bound.
-/

namespace PEqualNP.Research.MintermSlack

open PEqualNP.CircuitLowerBounds

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def replC (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨GateOp.and, []⟩, 0⟩

lemma replC_size (gates : List Gate) (i0 : ℕ) : (replC gates i0).size = gates.length := by
  simp [replC, Circuit.size]

lemma replC_gates (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (replC gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [replC] using hk
  by_cases hki : i0.val = k
  · simp [replC, hki]
  · have e : (replC gates i0.val).gates[k] = gates[k] := by
      simp [replC, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma replC_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    value (replC gates i0.val) x (n + i0.val) = true := by
  have h := gate_value (replC gates i0.val) x (n + i0.val) (by omega)
    (by rw [replC_size]; omega)
  simp only at h
  rw [h]
  simp [replC, GateOp.eval]

lemma replC_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (replC gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (replC gates i0) x r else false) := by
  have h := gate_value (replC gates i0) x w hn (by rw [replC_size]; exact hw)
  simp only at h
  rw [h]
  have e : (replC gates i0).gates[w - n]'(by simp [replC]; omega) = gates[w - n]'(by omega) := by
    simp only [replC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma replC_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = true) (w : ℕ) :
    value (replC gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0.val) x w (by rw [replC_size]; omega)]

/-- Replacement changes no earlier wire, independently of the input value
at the replaced gate. Malformed reads remain false through the prefix. -/
lemma replC_prefix_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (w : ℕ) :
    w < n + i0.val → value (replC gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hbefore
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    have hw : w < n + gates.length := by have := i0.isLt; omega
    rw [orig_value gates o x w (by omega) hw,
      replC_other gates i0.val x w (by omega) hw (by omega)]
    apply repl_eval_congr
    intro r _
    by_cases hr : r < w
    · simpa [hr] using ih r hr (by omega)
    · simp [hr]

lemma replC_prefix_support {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (o w : ℕ) (hbefore : w < n + i0.val) :
    support (n := n) (replC gates i0.val) w = support (n := n) ⟨gates, o⟩ w := by
  ext p
  simp only [mem_support]
  rw [replC_prefix_eq gates i0 o _ w hbefore]

/-- Every pre-replacement gate operation is preserved at the same index. -/
lemma replC_gate_before (gates : List Gate) (i0 : Fin gates.length)
    (j : Fin gates.length) (hbefore : j.val < i0.val) :
    ((replC gates i0.val).gates.get
      ⟨j.val, by simp [replC]⟩).op = (gates.get j).op := by
  have hne : i0.val ≠ j.val := by omega
  simp [replC, hne]

lemma orig_not_value {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o u : ℕ)
    (hop : (gates.get i0).op = GateOp.not)
    (hhead : (gates.get i0).inputs.head? = some u)
    (hlt : u < n + i0.val) (x : Fin n → Bool) :
    value ⟨gates, o⟩ x (n + i0.val) = !(value ⟨gates, o⟩ x u) := by
  rw [orig_value gates o x (n + i0.val) (by omega) (by have := i0.isLt; omega)]
  have e : gates[n + i0.val - n]'(by have := i0.isLt; omega) = gates.get i0 := by simp
  rw [e, hop]
  obtain ⟨rest, hin⟩ : ∃ rest, (gates.get i0).inputs = u :: rest := by
    cases h : (gates.get i0).inputs with
    | nil => rw [h] at hhead; simp at hhead
    | cons a rest => rw [h] at hhead; exact ⟨rest, by simpa using hhead⟩
  rw [hin]
  simp [GateOp.eval, hlt]

/-- A NOT gate that is false has a first input, and that read is valid. -/
lemma not_input_of_false {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
    (o : ℕ) (y : Fin n → Bool)
    (hop : (gates.get i0).op = GateOp.not)
    (hfalse : value ⟨gates, o⟩ y (n + i0.val) = false) :
    ∃ u, (gates.get i0).inputs.head? = some u ∧ u < n + i0.val := by
  rw [orig_value gates o y (n + i0.val) (by omega) (by have := i0.isLt; omega)] at hfalse
  have e : gates[n + i0.val - n]'(by have := i0.isLt; omega) = gates.get i0 := by simp
  rw [e, hop] at hfalse
  cases hin : (gates.get i0).inputs with
  | nil =>
    rw [hin] at hfalse
    simp [GateOp.eval] at hfalse
  | cons u rest =>
    refine ⟨u, by simp, ?_⟩
    rw [hin] at hfalse
    by_contra! hbad
    have hnotlt : ¬ u < n + i0.val := by omega
    simp [GateOp.eval, hnotlt] at hfalse

/-- Combined bound with an explicitly identified unique NOT and valid head. -/
theorem one_not_window_bound_explicit {n m k : ℕ} (gates : List Gate) (origOut : ℕ)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (i0 : Fin gates.length) (u : ℕ) (y : Fin n → Bool)
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hop : (gates.get i0).op = GateOp.not)
    (hhead : (gates.get i0).inputs.head? = some u)
    (hlt : u < n + i0.val)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value ⟨gates, origOut⟩ x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value ⟨gates, origOut⟩ x (n + i0.val) = true)
    (hfalse : value ⟨gates, origOut⟩ y (n + i0.val) = false) :
    (∑ i : Fin m, (min k (S i).card - 1)) + k ≤ gates.length := by
  classical
  let D := replC gates i0.val
  have hG := replC_gates gates i0 hgate hnot
  have hy : value D y u = true := by
    rw [replC_prefix_eq gates i0 origOut y u hlt]
    have h := hfalse
    rw [orig_not_value gates i0 origOut u hop hhead hlt y] at h
    simpa using h
  have hmin : ∀ x : Fin n → Bool, value D x u = true →
      k ≤ (Finset.univ.filter (fun p => x p = true)).card := by
    intro x hx
    by_contra! hsmall
    have hz := hbelow x hsmall
    have hu : value ⟨gates, origOut⟩ x u = true := by
      rw [← replC_prefix_eq gates i0 origOut x u hlt]
      exact hx
    rw [orig_not_value gates i0 origOut u hop hhead hlt x, hu] at hz
    contradiction
  have hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value D x (out i) = decide (∃ p ∈ S i, x p = true) := by
    intro i x hx
    rw [replC_eq gates i0 origOut x (hbelow x hx) (out i)]
    exact hout i x
  have hzgate : n + i0.val ∈ Finset.Ico n (n + D.size) := by
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · change n + i0.val < n + (replC gates i0.val).size
      rw [replC_size]
      exact Nat.add_lt_add_left i0.isLt n
  have h := light_minterm_bound D S out u (n + i0.val) y hG
    (replC_true gates i0) hzgate hlt hy hmin hinter hwindow
  simpa only [D, replC_size] using h

/-- The original threshold-window hypotheses themselves force a unique valid
NOT at t. This derives B+k≤N without an extra NOT-existence or valid-head axiom. -/
theorem one_not_window_bound {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (y : Fin n → Bool)
    (hk : 2 ≤ k)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k → value C x (n + t) = true)
    (hfalse : value C y (n + t) = false) :
    (∑ i : Fin m, (min k (S i).card - 1)) + k ≤ C.size := by
  classical
  have hzero : value C (fun _ : Fin n => false) (n + t) = true :=
    hbelow _ (by simpa using (show 0 < k by omega))
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
  obtain ⟨u, hhead, hlt⟩ := not_input_of_false C.gates i0 C.output y hop hfalse
  have h := one_not_window_bound_explicit C.gates C.output S out i0 u y
    hgate huniq hop hhead hlt hinter hout hbelow hfalse
  simpa only [Circuit.size] using h

end PEqualNP.Research.MintermSlack

#print axioms PEqualNP.Research.MintermSlack.replC_prefix_eq
#print axioms PEqualNP.Research.MintermSlack.one_not_window_bound

