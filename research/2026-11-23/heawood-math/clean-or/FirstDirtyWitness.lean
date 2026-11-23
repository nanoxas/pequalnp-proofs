import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Data.Finset.Card

/-
Local research: first-true-AND witness compression in the actual root Circuit
model. Foundational wire lemmas are adapted from checked L_meta_970, with no
import of that outside proof. No project submission or task lease is claimed.
-/

namespace FirstDirtyWitness

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len
  rw [foldl_step_len]
  exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate) (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i => if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false = g0.op.eval (g0.inputs.map fun i => w.getD i false) :=
        getD_append_self w _
      rw [hself]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]
          omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]
        exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]
        omega
      rw [List.foldl_cons, ← hlen]
      exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]
  exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2))
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true → (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]
      exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]
        intro h; exact absurd h (by decide)
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hilt : i < n + j
        · simp only [hilt, ↓reduceIte] at hi ⊢
          exact ih i (by omega) hi
        · simp only [hilt, ↓reduceIte] at hi
          exact absurd hi (by decide)


abbrev value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

def oneInput {n : ℕ} (v : Fin n) : Fin n → Bool := fun u => decide (u = v)

def setInput {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun u => decide (u ∈ S)

lemma or_input_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or)
    (ht : value C x (n + j) = true) :
    ∃ w ∈ g.inputs, w < n + j ∧ value C x w = true := by
  change (C.wires (List.ofFn x)).getD (n + j) false = true at ht
  rw [wires_gate_ofFn C x j g hg, hop] at ht
  change (g.inputs.map (fun i => if i < n + j then value C x i else false)).any id = true at ht
  obtain ⟨b, hb, hbt⟩ := List.any_eq_true.mp ht
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
  by_cases hwi : w < n + j
  · exact ⟨w, hw, hwi, by simpa only [hwi, ↓reduceIte, id_eq] using hbt⟩
  · simp only [hwi, ↓reduceIte, id_eq, Bool.false_eq_true] at hbt

lemma or_true_of_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or)
    (w : ℕ) (hw : w ∈ g.inputs) (hwi : w < n + j) (ht : value C x w = true) :
    value C x (n + j) = true := by
  change (C.wires (List.ofFn x)).getD (n + j) false = true
  rw [wires_gate_ofFn C x j g hg, hop]
  apply List.any_eq_true.mpr
  refine ⟨true, List.mem_map.mpr ⟨w, hw, ?_⟩, rfl⟩
  simpa only [hwi, ↓reduceIte] using ht

lemma and_inputs_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (ht : value C x (n + j) = true) :
    ∀ w ∈ g.inputs, w < n + j ∧ value C x w = true := by
  change (C.wires (List.ofFn x)).getD (n + j) false = true at ht
  rw [wires_gate_ofFn C x j g hg, hop] at ht
  have hall := List.all_eq_true.mp ht
  intro w hw
  have hwt := hall _ (List.mem_map_of_mem hw)
  by_cases hwi : w < n + j
  · exact ⟨hwi, by simpa only [hwi, ↓reduceIte, id_eq] using hwt⟩
  · simp only [hwi, ↓reduceIte, id_eq, Bool.false_eq_true] at hwt

lemma and_true_of_inputs {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hinputs : ∀ w ∈ g.inputs, w < n + j ∧ value C x w = true) :
    value C x (n + j) = true := by
  change (C.wires (List.ofFn x)).getD (n + j) false = true
  rw [wires_gate_ofFn C x j g hg, hop]
  apply List.all_eq_true.mpr
  intro b hb
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hb
  obtain ⟨hwi, ht⟩ := hinputs w hw
  simpa only [hwi, ↓reduceIte, id_eq] using ht

/-- Before the first true AND on x, every true wire already accepts a singleton
whose variable is true in x. This needs no fan-in restriction on the OR gates. -/
theorem singleton_witness_before {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (j : ℕ) (hj : j ≤ C.gates.length)
    (hfalse : ∀ i < j, ∀ g, C.gates[i]? = some g → g.op = GateOp.and →
      value C x (n + i) = false) :
    ∀ w < n + j, value C x w = true →
      ∃ v : Fin n, x v = true ∧ value C (oneInput v) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw ht
    by_cases hin : w < n
    · refine ⟨⟨w, hin⟩, ?_, ?_⟩
      · simpa only [value, wires_input C x w hin] using ht
      · rw [value, wires_input C (oneInput ⟨w, hin⟩) w hin]
        simp [oneInput]
    · have hi : w - n < j := by omega
      have hilen : w - n < C.gates.length := by omega
      let g := C.gates[w - n]'hilen
      have hg : C.gates[w - n]? = some g := List.getElem?_eq_getElem hilen
      have hwid : w = n + (w - n) := by omega
      rcases hops g (List.mem_of_getElem? hg) with hand | hor
      · have hf := hfalse (w - n) hi g hg hand
        rw [← hwid, ht] at hf
        contradiction
      · obtain ⟨a, ha, hai, hat⟩ := or_input_true C x (w - n) g hg hor (by simpa [← hwid] using ht)
        obtain ⟨v, hv, hvat⟩ := ih a (by omega) (by omega) hat
        refine ⟨v, hv, ?_⟩
        rw [hwid]
        exact or_true_of_input C (oneInput v) (w - n) g hg hor a ha hai hvat

/-- If some AND gate is true on x, then some AND gate is already true on a
subinput of x containing at most two true variables. Empty and unary AND gates
are included: the chosen support has at most the actual fan-in of the gate. -/
theorem first_and_small_witness {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hex : ∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      value C x (n + j) = true) :
    ∃ (j : ℕ) (g : Gate) (S : Finset (Fin n)),
      C.gates[j]? = some g ∧ g.op = GateOp.and ∧ S.card ≤ 2 ∧
      (∀ v ∈ S, x v = true) ∧ value C (setInput S) (n + j) = true := by
  classical
  let P : ℕ → Prop := fun j => ∃ g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
    value C x (n + j) = true
  have hP : ∃ j, P j := hex
  let j := Nat.find hP
  obtain ⟨g, hg, hop, htrue⟩ := Nat.find_spec hP
  have hjlt : j < C.gates.length := by
    by_contra h
    have hnone : C.gates[j]? = none := List.getElem?_eq_none (by omega)
    rw [hg] at hnone
    contradiction
  have hfalse : ∀ i < j, ∀ gi, C.gates[i]? = some gi → gi.op = GateOp.and →
      value C x (n + i) = false := by
    intro i hi gi hgi hgiop
    cases hv : value C x (n + i) with
    | false => rfl
    | true => exact False.elim ((Nat.find_min hP hi) ⟨gi, hgi, hgiop, hv⟩)
  have hraw := singleton_witness_before C x (fun g hg => (hmono g hg).1) j hjlt.le hfalse
  have hinputs := and_inputs_true C x j g hg hop htrue
  have hwitness : ∀ w : {w // w ∈ g.inputs},
      ∃ v : Fin n, x v = true ∧ value C (oneInput v) w.val = true := by
    intro w
    exact hraw w.val (hinputs w.val w.property).1 (hinputs w.val w.property).2
  let pick : {w // w ∈ g.inputs} → Fin n := fun w => Classical.choose (hwitness w)
  let S : Finset (Fin n) := (g.inputs.attach.map pick).toFinset
  have hcard : S.card ≤ 2 := by
    have hcard' := List.toFinset_card_le (g.inputs.attach.map pick)
    simp only [List.length_map, List.length_attach] at hcard'
    exact hcard'.trans (hmono g (List.mem_of_getElem? hg)).2
  have hsubset : ∀ v ∈ S, x v = true := by
    intro v hv
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    exact (Classical.choose_spec (hwitness w)).1
  refine ⟨j, g, S, hg, hop, hcard, hsubset, ?_⟩
  apply and_true_of_inputs C (setInput S) j g hg hop
  intro w hw
  refine ⟨(hinputs w hw).1, ?_⟩
  let w' : {w // w ∈ g.inputs} := ⟨w, hw⟩
  have hsingle : value C (oneInput (pick w')) w = true :=
    (Classical.choose_spec (hwitness w')).2
  have hinS : pick w' ∈ S :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨w', List.mem_attach _ _, rfl⟩)
  apply wires_mono C hmono (oneInput (pick w')) (setInput S) _ w hsingle
  intro v hv
  have heq : v = pick w' := by simpa only [oneInput, decide_eq_true_eq] using hv
  subst v
  simp only [setInput, hinS, decide_true]

/-- Independence is inherited by the supported subinput. The relation R can
be instantiated directly with the adjacency relation of any simple graph. -/
theorem independent_small_witness {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (R : Fin n → Fin n → Prop)
    (hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hindependent : ∀ u v, x u = true → x v = true → ¬ R u v)
    (hex : ∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
      value C x (n + j) = true) :
    ∃ (j : ℕ) (g : Gate) (S : Finset (Fin n)),
      C.gates[j]? = some g ∧ g.op = GateOp.and ∧ S.card ≤ 2 ∧
      (∀ u ∈ S, ∀ v ∈ S, ¬ R u v) ∧ value C (setInput S) (n + j) = true := by
  obtain ⟨j, g, S, hg, hop, hcard, hsubset, htrue⟩ := first_and_small_witness C x hmono hex
  exact ⟨j, g, S, hg, hop, hcard,
    fun u hu v hv => hindependent u v (hsubset u hu) (hsubset v hv), htrue⟩

/-- To establish cleanliness of every AND gate on every independent input, it
suffices to establish it on independent supports of cardinality at most two. -/
theorem clean_of_small_clean {n : ℕ} (C : Circuit) (R : Fin n → Fin n → Prop)
    (hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsmall : ∀ S : Finset (Fin n), S.card ≤ 2 →
      (∀ u ∈ S, ∀ v ∈ S, ¬ R u v) →
      ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
        value C (setInput S) (n + j) = false) :
    ∀ x : Fin n → Bool, (∀ u v, x u = true → x v = true → ¬ R u v) →
      ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
        value C x (n + j) = false := by
  intro x hindependent j g hg hop
  cases hv : value C x (n + j) with
  | false => rfl
  | true =>
    obtain ⟨k, g', S, hk, hop', hcard, hind, htrue⟩ :=
      independent_small_witness C x R hmono hindependent ⟨j, g, hg, hop, hv⟩
    have hzero := hsmall S hcard hind k g' hk hop'
    rw [htrue] at hzero
    contradiction

end FirstDirtyWitness
