import PEqualNP.Defs.CircuitLowerBounds
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation

/-! Actual circuit semantics and shared interfaces for L-meta-1407. -/

namespace PEqualNP.MetaComplexity.L1407

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


/-- The edge function is true on the support of `x`. -/
def EdgeOn {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

instance edgeOn_decidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : Decidable (EdgeOn G x) := by
  unfold EdgeOn
  infer_instance

def AndOr (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

/-- Every AND output is below the graph edge function. -/
def AndBelow {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin n → Bool, value C x (n + j) = true → EdgeOn G x

/-- Singleton acceptance, which agrees with raw OR-only input support in clean circuits. -/
def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => value C (oneInput v) w = true)

/-- A forward or nonexistent reference reads false when its gate is evaluated. -/
def portSupport {n : ℕ} (C : Circuit) (j w : ℕ) : Finset (Fin n) :=
  if w < n + j then support C w else ∅

/-- A valid earlier wire read by a gate, directed from child to parent. -/
def Reads {n : ℕ} (C : Circuit) (a b : ℕ) : Prop :=
  ∃ j g, C.gates[j]? = some g ∧ b = n + j ∧ a ∈ g.inputs ∧ a < b

def Live {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  Relation.ReflTransGen (Reads (n := n) C) w C.output

noncomputable def liveGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j => Live (n := n) C (n + j))

/-- A live binary AND with two nonempty raw input supports. -/
def Productive {n : ℕ} (C : Circuit) (j : ℕ) : Prop :=
  Live (n := n) C (n + j) ∧ ∃ g a b,
    C.gates[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
    a < n + j ∧ b < n + j ∧
    (support (n := n) C a).Nonempty ∧ (support (n := n) C b).Nonempty

noncomputable def productiveGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (Productive (n := n) C)

/-- A live binary OR with two nonempty raw input supports and a wide output support. -/
def RawMerge {n : ℕ} (C : Circuit) (j : ℕ) : Prop :=
  Live (n := n) C (n + j) ∧ ∃ g a b,
    C.gates[j]? = some g ∧ g.op = GateOp.or ∧ g.inputs = [a, b] ∧
    a < n + j ∧ b < n + j ∧
    (support (n := n) C a).Nonempty ∧ (support (n := n) C b).Nonempty ∧
    2 ≤ (support (n := n) C (n + j)).card

noncomputable def rawMergeGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (RawMerge (n := n) C)

@[simp] theorem mem_support {n : ℕ} (C : Circuit) (w : ℕ) (v : Fin n) :
    v ∈ support C w ↔ value C (oneInput v) w = true := by
  simp [support]

@[simp] theorem mem_portSupport {n : ℕ} (C : Circuit) (j w : ℕ) (v : Fin n) :
    v ∈ portSupport C j w ↔ w < n + j ∧ v ∈ support C w := by
  by_cases hw : w < n + j <;> simp [portSupport, hw]

theorem support_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    support C w = {⟨w, hw⟩} := by
  ext v
  simp only [mem_support, value, wires_input C (oneInput v) w hw,
    oneInput, decide_eq_true_eq, Finset.mem_singleton]
  exact eq_comm

theorem support_oob {n : ℕ} (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    support (n := n) C w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have ht := (mem_support C w v).mp hv
  change (C.wires (List.ofFn (oneInput v))).getD w false = true at ht
  rw [wires_oob C (oneInput v) w hw] at ht
  cases ht

theorem not_edgeOn_one {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
    ¬ EdgeOn G (oneInput v) := by
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [oneInput, decide_eq_true_eq] at ha hb
  subst a
  subst b
  exact G.loopless.irrefl _ hab

theorem not_edgeOn_false {n : ℕ} (G : SimpleGraph (Fin n)) :
    ¬ EdgeOn G (fun _ => false) := by
  rintro ⟨a, b, hab, ha, hb⟩
  cases ha

theorem support_and {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) :
    support (n := n) C (n + j) = ∅ := by
  ext v
  simp only [Finset.notMem_empty, iff_false, mem_support]
  intro ht
  exact not_edgeOn_one G v (hclean j g hg hop (oneInput v) ht)

theorem support_or {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.or) :
    support (n := n) C (n + j) =
      g.inputs.toFinset.biUnion (fun w => portSupport (n := n) C j w) := by
  ext v
  simp only [mem_support, Finset.mem_biUnion, List.mem_toFinset, mem_portSupport]
  constructor
  · intro ht
    obtain ⟨w, hw, hwi, hwt⟩ := or_input_true C (oneInput v) j g hg hop ht
    exact ⟨w, hw, hwi, hwt⟩
  · rintro ⟨w, hw, hwi, hwt⟩
    exact or_true_of_input C (oneInput v) j g hg hop w hw hwi hwt

theorem support_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeOn G x)) :
    support (n := n) C C.output = ∅ := by
  ext v
  simp only [Finset.notMem_empty, iff_false, mem_support]
  intro ht
  have hf := hfun (oneInput v)
  change value C (oneInput v) C.output = decide (EdgeOn G (oneInput v)) at hf
  rw [ht] at hf
  have he : EdgeOn G (oneInput v) := of_decide_eq_true hf.symm
  exact not_edgeOn_one G v he

theorem reads_lt {n : ℕ} (C : Circuit) {a b : ℕ} (h : Reads (n := n) C a b) :
    a < b := h.choose_spec.choose_spec.2.2.2

theorem live_output {n : ℕ} (C : Circuit) : Live (n := n) C C.output :=
  Relation.ReflTransGen.refl

theorem live_of_reads {n : ℕ} (C : Circuit) {a b : ℕ}
    (hread : Reads (n := n) C a b) (hlive : Live (n := n) C b) :
    Live (n := n) C a := Relation.ReflTransGen.head hread hlive

theorem live_input_of_gate {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hlive : Live (n := n) C (n + j))
    (a : ℕ) (ha : a ∈ g.inputs) (hlt : a < n + j) : Live (n := n) C a :=
  live_of_reads C ⟨j, g, hg, rfl, ha, hlt⟩ hlive

@[simp] theorem mem_liveGates {n : ℕ} (C : Circuit) (j : ℕ) :
    j ∈ liveGates (n := n) C ↔ j < C.gates.length ∧ Live (n := n) C (n + j) := by
  classical
  simp [liveGates]

@[simp] theorem mem_productiveGates {n : ℕ} (C : Circuit) (j : ℕ) :
    j ∈ productiveGates (n := n) C ↔ j < C.gates.length ∧ Productive (n := n) C j := by
  classical
  simp [productiveGates]

@[simp] theorem mem_rawMergeGates {n : ℕ} (C : Circuit) (j : ℕ) :
    j ∈ rawMergeGates (n := n) C ↔ j < C.gates.length ∧ RawMerge (n := n) C j := by
  classical
  simp [rawMergeGates]

theorem input_support_card_le_one {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (support (n := n) C w).card ≤ 1 := by
  rw [support_input C w hw]
  simp

theorem portSupport_nonempty {n : ℕ} (C : Circuit) (j w : ℕ)
    (h : (portSupport (n := n) C j w).Nonempty) :
    w < n + j ∧ (support (n := n) C w).Nonempty := by
  by_cases hw : w < n + j
  · exact ⟨hw, by simpa only [portSupport, hw, ↓reduceIte] using h⟩
  · simp [portSupport, hw] at h

/-- A wide live support either continues through one earlier wire at zero
cost, or splits at a wide raw merge. Empty-support ports cause no charge. -/
theorem wide_support_step {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hlive : Live (n := n) C (n + j))
    (hwide : 2 ≤ (support (n := n) C (n + j)).card) :
    (∃ a, a < n + j ∧ Live (n := n) C a ∧ support (n := n) C (n + j) = support C a) ∨
    (RawMerge (n := n) C j ∧ ∃ a b, a < n + j ∧ b < n + j ∧
      Live (n := n) C a ∧ Live (n := n) C b ∧
      support (n := n) C (n + j) = support C a ∪ support C b) := by
  classical
  obtain ⟨hop, hlen⟩ := hops g (List.mem_of_getElem? hg)
  rcases hop with hand | hor
  · rw [support_and G C hclean j g hg hand] at hwide
    simp at hwide
  · have hs := support_or (n := n) C j g hg hor
    generalize heq : g.inputs = ins at hs hlen
    cases ins with
    | nil =>
      simp only [List.toFinset_nil, Finset.biUnion_empty] at hs
      rw [hs] at hwide
      simp at hwide
    | cons a tail =>
      cases tail with
      | nil =>
        have hs' : support (n := n) C (n + j) = portSupport C j a := by simpa using hs
        have hne : (portSupport (n := n) C j a).Nonempty := by
          apply Finset.card_pos.mp
          rw [← hs']
          omega
        obtain ⟨ha, hsa⟩ := portSupport_nonempty C j a hne
        left
        refine ⟨a, ha, live_input_of_gate C j g hg hlive a (by simp [heq]) ha, ?_⟩
        simpa only [portSupport, ha, ↓reduceIte] using hs'
      | cons b rest =>
        cases rest with
        | cons c cs => simp at hlen
        | nil =>
          have hs' : support (n := n) C (n + j) = portSupport C j a ∪ portSupport C j b := by
            simpa [Finset.biUnion_insert] using hs
          by_cases hna : (portSupport (n := n) C j a).Nonempty
          · by_cases hnb : (portSupport (n := n) C j b).Nonempty
            · obtain ⟨ha, hsa⟩ := portSupport_nonempty C j a hna
              obtain ⟨hb, hsb⟩ := portSupport_nonempty C j b hnb
              have hal := live_input_of_gate C j g hg hlive a (by simp [heq]) ha
              have hbl := live_input_of_gate C j g hg hlive b (by simp [heq]) hb
              right
              refine ⟨⟨hlive, g, a, b, hg, hor, heq, ha, hb, hsa, hsb, hwide⟩,
                a, b, ha, hb, hal, hbl, ?_⟩
              simpa only [portSupport, ha, hb, ↓reduceIte] using hs'
            · have heb : portSupport (n := n) C j b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnb
              obtain ⟨ha, hsa⟩ := portSupport_nonempty C j a hna
              rw [heb, Finset.union_empty] at hs'
              left
              refine ⟨a, ha, live_input_of_gate C j g hg hlive a (by simp [heq]) ha, ?_⟩
              simpa only [portSupport, ha, ↓reduceIte] using hs'
          · have hea : portSupport (n := n) C j a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hna
            rw [hea, Finset.empty_union] at hs'
            have hnb : (portSupport (n := n) C j b).Nonempty := by
              apply Finset.card_pos.mp
              rw [← hs']
              omega
            obtain ⟨hb, hsb⟩ := portSupport_nonempty C j b hnb
            left
            refine ⟨b, hb, live_input_of_gate C j g hg hlive b (by simp [heq]) hb, ?_⟩
            simpa only [portSupport, hb, ↓reduceIte] using hs'

end PEqualNP.MetaComplexity.L1407
