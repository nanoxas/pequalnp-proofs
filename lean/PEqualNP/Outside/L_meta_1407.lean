import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1407_aux

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



def EdgeOn {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

instance edgeOn_decidable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) : Decidable (EdgeOn G x) := by
  unfold EdgeOn
  infer_instance

def AndOr (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2


def AndBelow {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
    ∀ x : Fin n → Bool, value C x (n + j) = true → EdgeOn G x


def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => value C (oneInput v) w = true)


def portSupport {n : ℕ} (C : Circuit) (j w : ℕ) : Finset (Fin n) :=
  if w < n + j then support C w else ∅


def Reads {n : ℕ} (C : Circuit) (a b : ℕ) : Prop :=
  ∃ j g, C.gates[j]? = some g ∧ b = n + j ∧ a ∈ g.inputs ∧ a < b

def Live {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  Relation.ReflTransGen (Reads (n := n) C) w C.output

noncomputable def liveGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (fun j => Live (n := n) C (n + j))


def Productive {n : ℕ} (C : Circuit) (j : ℕ) : Prop :=
  Live (n := n) C (n + j) ∧ ∃ g a b,
    C.gates[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
    a < n + j ∧ b < n + j ∧
    (support (n := n) C a).Nonempty ∧ (support (n := n) C b).Nonempty

noncomputable def productiveGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (Productive (n := n) C)


def RawMerge {n : ℕ} (C : Circuit) (j : ℕ) : Prop :=
  Live (n := n) C (n + j) ∧ ∃ g a b,
    C.gates[j]? = some g ∧ g.op = GateOp.or ∧ g.inputs = [a, b] ∧
    a < n + j ∧ b < n + j ∧
    (support (n := n) C a).Nonempty ∧ (support (n := n) C b).Nonempty ∧
    2 ≤ (support (n := n) C (n + j)).card

noncomputable def rawMergeGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (RawMerge (n := n) C)

@[local simp] theorem mem_support {n : ℕ} (C : Circuit) (w : ℕ) (v : Fin n) :
    v ∈ support C w ↔ value C (oneInput v) w = true := by
  simp [support]

@[local simp] theorem mem_portSupport {n : ℕ} (C : Circuit) (j w : ℕ) (v : Fin n) :
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

@[local simp] theorem mem_liveGates {n : ℕ} (C : Circuit) (j : ℕ) :
    j ∈ liveGates (n := n) C ↔ j < C.gates.length ∧ Live (n := n) C (n + j) := by
  classical
  simp [liveGates]

@[local simp] theorem mem_productiveGates {n : ℕ} (C : Circuit) (j : ℕ) :
    j ∈ productiveGates (n := n) C ↔ j < C.gates.length ∧ Productive (n := n) C j := by
  classical
  simp [productiveGates]

@[local simp] theorem mem_rawMergeGates {n : ℕ} (C : Circuit) (j : ℕ) :
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

end PEqualNP.Outside.L_meta_1407_aux

namespace PEqualNP.Outside.L_meta_1407_aux

open Finset

variable {α : Type*} [DecidableEq α]
variable (charge : ℕ → Prop) [DecidablePred charge]


def rawWideGates (F : ℕ → Finset α) (n k : ℕ) (S : Finset α) : Finset ℕ :=
  (range k).filter (fun j => charge j ∧ 2 ≤ (F (n + j)).card ∧ F (n + j) ⊆ S)

theorem mem_rawWideGates (F : ℕ → Finset α) (n k j : ℕ) (S : Finset α) :
    j ∈ rawWideGates charge F n k S ↔
      j < k ∧ charge j ∧ 2 ≤ (F (n + j)).card ∧ F (n + j) ⊆ S := by
  simp only [rawWideGates, mem_filter, mem_range]

theorem rawWideGates_mono (F : ℕ → Finset α) (n : ℕ) {k l : ℕ}
    (S : Finset α) (hkl : k ≤ l) :
    rawWideGates charge F n k S ⊆ rawWideGates charge F n l S := by
  intro j hj
  obtain ⟨hj, hc, hwide, hsub⟩ := (mem_rawWideGates charge F n k j S).mp hj
  exact (mem_rawWideGates charge F n l j S).mpr ⟨by omega, hc, hwide, hsub⟩

theorem rawWideGates_succ_of_wide (F : ℕ → Finset α) (n k : ℕ) (S : Finset α)
    (hc : charge k) (hwide : 2 ≤ (F (n + k)).card) (hsub : F (n + k) ⊆ S) :
    rawWideGates charge F n (k + 1) S = insert k (rawWideGates charge F n k S) := by
  ext j
  simp only [mem_rawWideGates, mem_insert]
  constructor
  · rintro ⟨hj, hjc, hw, hs⟩
    by_cases h : j = k
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hjc, hw, hs⟩
  · rintro (rfl | ⟨hj, hjc, hw, hs⟩)
    · exact ⟨by omega, hc, hwide, hsub⟩
    · exact ⟨by omega, hjc, hw, hs⟩

theorem rawWideGates_card_succ (F : ℕ → Finset α) (n k : ℕ) (S : Finset α)
    (hc : charge k) (hwide : 2 ≤ (F (n + k)).card) (hsub : F (n + k) ⊆ S) :
    (rawWideGates charge F n (k + 1) S).card =
      (rawWideGates charge F n k S).card + 1 := by
  rw [rawWideGates_succ_of_wide charge F n k S hc hwide hsub, card_insert_of_notMem]
  simp only [mem_rawWideGates, lt_self_iff_false, false_and, not_false_eq_true]

theorem card_biUnion_le_card_of_small {β : Type*} [DecidableEq β]
    (R : Finset β) (F : β → Finset α) (h : ∀ r ∈ R, (F r).card ≤ 1) :
    (R.biUnion F).card ≤ R.card := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert a R ha ih =>
    have har : (F a).card ≤ 1 := h a (mem_insert_self _ _)
    have hr : (R.biUnion F).card ≤ R.card :=
      ih (fun r hr => h r (mem_insert_of_mem hr))
    rw [biUnion_insert, card_insert_of_notMem ha]
    have hu := card_union_le (F a) (R.biUnion F)
    omega


theorem raw_union_count
    (F : ℕ → Finset α) (n : ℕ) (S : Finset α)
    (hinput : ∀ i < n, (F i).card ≤ 1) (k : ℕ) :
    (∀ j < k, 2 ≤ (F (n + j)).card →
      (∃ a : ℕ, a < n + j ∧ F (n + j) = F a) ∨
      (charge j ∧ ∃ a b : ℕ, a < n + j ∧ b < n + j ∧ F (n + j) = F a ∪ F b)) →
    ∀ R : Finset ℕ,
      (∀ r ∈ R, r < n + k) →
      (∀ r ∈ R, F r ⊆ S) →
      (R.biUnion F).card ≤ R.card + (rawWideGates charge F n k S).card := by
  induction k with
  | zero =>
    intro _ R hR _
    simpa [rawWideGates] using
      card_biUnion_le_card_of_small R F (fun r hr => hinput r (by simpa using hR r hr))
  | succ k ih =>
    intro hgate R hR hsub
    have hgate' : ∀ j < k, 2 ≤ (F (n + j)).card →
        (∃ a : ℕ, a < n + j ∧ F (n + j) = F a) ∨
        (charge j ∧ ∃ a b : ℕ, a < n + j ∧ b < n + j ∧ F (n + j) = F a ∪ F b) :=
      fun j hj hw => hgate j (by omega) hw
    have hwmono : (rawWideGates charge F n k S).card ≤
        (rawWideGates charge F n (k + 1) S).card :=
      card_le_card (rawWideGates_mono charge F n S (by omega))
    by_cases htop : n + k ∈ R
    · let E := R.erase (n + k)
      have hE : ∀ r ∈ E, r < n + k := by
        intro r hr
        obtain ⟨hne, hmem⟩ := mem_erase.mp hr
        have := hR r hmem
        omega
      have hEsub : ∀ r ∈ E, F r ⊆ S :=
        fun r hr => hsub r (mem_of_mem_erase hr)
      have hEcard : E.card + 1 = R.card := card_erase_add_one htop
      have hRunion : R.biUnion F = F (n + k) ∪ E.biUnion F := by
        rw [← insert_erase htop, biUnion_insert]
      by_cases hwide : 2 ≤ (F (n + k)).card
      · rcases hgate k (by omega) hwide with ⟨a, ha, heq⟩ | ⟨hc, a, b, ha, hb, hab⟩
        · let Q := insert a E
          have hQ : ∀ r ∈ Q, r < n + k := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · exact ha
            · exact hE r hr
          have hQsub : ∀ r ∈ Q, F r ⊆ S := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · rw [← heq]
              exact hsub (n + k) htop
            · exact hEsub r hr
          have hQunion : Q.biUnion F = R.biUnion F := by
            rw [hRunion, heq]
            exact biUnion_insert
          have hQcard : Q.card ≤ R.card := by
            have h1 := card_insert_le a E
            change (insert a E).card ≤ R.card
            omega
          have hbound := ih hgate' Q hQ hQsub
          rw [hQunion] at hbound
          omega
        · let Q := insert a (insert b E)
          have hQ : ∀ r ∈ Q, r < n + k := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · exact ha
            · rcases mem_insert.mp hr with rfl | hr
              · exact hb
              · exact hE r hr
          have habsub : F a ⊆ S ∧ F b ⊆ S := by
            apply union_subset_iff.mp
            rw [← hab]
            exact hsub (n + k) htop
          have hQsub : ∀ r ∈ Q, F r ⊆ S := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · exact habsub.1
            · rcases mem_insert.mp hr with rfl | hr
              · exact habsub.2
              · exact hEsub r hr
          have hQunion : Q.biUnion F = R.biUnion F := by
            rw [hRunion, hab]
            simp only [Q, biUnion_insert, union_assoc]
          have hQcard : Q.card ≤ R.card + 1 := by
            have h1 := card_insert_le a (insert b E)
            have h2 := card_insert_le b E
            change (insert a (insert b E)).card ≤ R.card + 1
            omega
          have hbound := ih hgate' Q hQ hQsub
          rw [hQunion] at hbound
          have hwcard := rawWideGates_card_succ charge F n k S hc hwide (hsub (n + k) htop)
          omega
      · have hsmall : (F (n + k)).card ≤ 1 := by omega
        have hbound := ih hgate' E hE hEsub
        rw [hRunion]
        have hu := card_union_le (F (n + k)) (E.biUnion F)
        omega
    · have hR' : ∀ r ∈ R, r < n + k := by
        intro r hr
        have hne : r ≠ n + k := by rintro rfl; exact htop hr
        have := hR r hr
        omega
      have hbound := ih hgate' R hR' hsub
      omega

end PEqualNP.Outside.L_meta_1407_aux

namespace PEqualNP.Outside.L_meta_1407_aux

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

lemma common_neighbors_card_le_one (G : SimpleGraph V) (hG : NoFourCycle G)
    (a b : V) (hab : a ≠ b) (S : Finset V)
    (ha : ∀ u ∈ S, G.Adj a u) (hb : ∀ u ∈ S, G.Adj b u) :
    S.card ≤ 1 := by
  by_contra h
  have hcard : 1 < S.card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  exact hG a u b v hab huv ⟨ha u hu, (hb u hu).symm, hb v hv, (ha v hv).symm⟩

lemma biclique_has_singleton_side (G : SimpleGraph V) (hG : NoFourCycle G)
    (S T : Finset V) (hS : S.Nonempty) (hT : T.Nonempty)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) :
    (∃ v, S = {v}) ∨ (∃ v, T = {v}) := by
  by_cases hs : S.card ≤ 1
  · left
    have hc : S.card = 1 := by have := Finset.card_pos.mpr hS; omega
    exact Finset.card_eq_one.mp hc
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have ht := common_neighbors_card_le_one G hG a b hab T
      (fun u hu => hcross a ha u hu) (fun u hu => hcross b hb u hu)
    right
    have hc : T.card = 1 := by have := Finset.card_pos.mpr hT; omega
    exact Finset.card_eq_one.mp hc

lemma biclique_is_star (G : SimpleGraph V) (hG : NoFourCycle G)
    (S T : Finset V) (hS : S.Nonempty) (hT : T.Nonempty)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) :
    ∃ (v : V) (U : Finset V), U.Nonempty ∧
      ((S = {v} ∧ T = U) ∨ (T = {v} ∧ S = U)) ∧
      (∀ u ∈ U, G.Adj v u) := by
  rcases biclique_has_singleton_side G hG S T hS hT hcross with ⟨v, hv⟩ | ⟨v, hv⟩
  · refine ⟨v, T, hT, Or.inl ⟨hv, rfl⟩, ?_⟩
    intro u hu
    exact hcross v (by simp [hv]) u hu
  · refine ⟨v, S, hS, Or.inr ⟨hv, rfl⟩, ?_⟩
    intro u hu
    exact (hcross u hu v (by simp [hv])).symm

lemma shared_wide_support_implies_same_center (G : SimpleGraph V) (hG : NoFourCycle G)
    (a b : V) (S : Finset V) (hwide : 2 ≤ S.card)
    (ha : ∀ u ∈ S, G.Adj a u) (hb : ∀ u ∈ S, G.Adj b u) : a = b := by
  by_contra hab
  have := common_neighbors_card_le_one G hG a b hab S ha hb
  omega

lemma edge_count_le_star_unions (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : V → Finset V)
    (hcover : ∀ u v : V, G.Adj u v → v ∈ U u ∨ u ∈ U v) :
    G.edgeFinset.card ≤ ∑ v : V, (U v).card := by
  let E : V → Finset (Sym2 V) := fun v => (U v).image (fun u => s(v, u))
  have hsub : G.edgeFinset ⊆ Finset.univ.biUnion E := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      have huv : G.Adj u v := by simpa using he
      rcases hcover u v huv with h | h
      · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, h, rfl⟩⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨v, Finset.mem_univ _, Finset.mem_image.mpr ⟨u, h, ?_⟩⟩
        exact Sym2.eq_swap
  calc
    G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card hsub
    _ ≤ ∑ v : V, (E v).card := Finset.card_biUnion_le
    _ ≤ ∑ v : V, (U v).card := Finset.sum_le_sum fun v _ => Finset.card_image_le

lemma centers_form_cover {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph V) (A : Finset ι) (center : ι → V)
    (hcover : ∀ u v : V, G.Adj u v → ∃ a ∈ A, center a = u ∨ center a = v) :
    ∃ T : Finset V, (∀ u v : V, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ A.card := by
  refine ⟨A.image center, ?_, Finset.card_image_le⟩
  intro u v huv
  obtain ⟨a, ha, h⟩ := hcover u v huv
  rcases h with h | h
  · exact Or.inl (Finset.mem_image.mpr ⟨a, ha, h⟩)
  · exact Or.inr (Finset.mem_image.mpr ⟨a, ha, h⟩)

lemma sum_center_fibers {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (center : ι → V) :
    (∑ v : V, (A.filter fun a => center a = v).card) = A.card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter A (Finset.univ : Finset V) center

lemma clean_total_assembly (edges cover productive rawMerges aggregation other total : ℕ)
    (hedges : edges ≤ rawMerges + productive)
    (hcover : cover ≤ productive)
    (haggregation : productive ≤ aggregation + 1)
    (htotal : productive + rawMerges + aggregation + other ≤ total) :
    edges + cover ≤ total + 1 := by
  omega

lemma clean_total_from_live (edges cover productive wide live total : ℕ)
    (hedges : edges ≤ wide + productive) (hcover : cover ≤ productive)
    (hports : 2 * productive + wide ≤ live + 1) (hlive : live ≤ total) :
    edges + cover ≤ total + 1 := by
  omega

end PEqualNP.Outside.L_meta_1407_aux

namespace PEqualNP.Outside.L_meta_1407_aux

open PEqualNP.CircuitLowerBounds


theorem trace_raw_or_and {n : ℕ} (C : Circuit) (hops : AndOr C)
    (x : Fin n → Bool) :
    ∀ w, Live (n := n) C w → value C x w = true →
      (∃ v ∈ support C w, x v = true) ∨
      ∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        Live (n := n) C (n + j) ∧
        ∀ a ∈ g.inputs, a < n + j ∧ ∃ v ∈ support C a, x v = true := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlive ht
    by_cases hin : w < n
    · left
      refine ⟨⟨w, hin⟩, ?_, ?_⟩
      · rw [support_input C w hin]
        exact Finset.mem_singleton_self _
      · simpa only [value, wires_input C x w hin] using ht
    · by_cases hout : n + C.gates.length ≤ w
      · simp only [value, wires_oob C x w hout, Bool.false_eq_true] at ht
      · have hjlt : w - n < C.gates.length := by omega
        let j := w - n
        let g := C.gates[j]'hjlt
        have hw : w = n + j := by omega
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
        have hgj := (hops g (List.mem_of_getElem? hg)).1
        rw [hw] at hlive ht
        rcases hgj with hand | hor
        · have hall := and_inputs_true C x j g hg hand ht
          by_cases hraw : ∀ a ∈ g.inputs, ∃ v ∈ support C a, x v = true
          · right
            exact ⟨j, g, hg, hand, hlive, fun a ha => ⟨(hall a ha).1, hraw a ha⟩⟩
          · have hex : ∃ a, a ∈ g.inputs ∧ ¬ ∃ v ∈ support C a, x v = true := by
              simpa only [not_forall, not_imp] using hraw
            obtain ⟨a, ha, hnot⟩ := hex
            have halt := (hall a ha).1
            have halive := live_input_of_gate C j g hg hlive a ha halt
            rcases ih a (by omega) halive (hall a ha).2 with h | h
            · exact False.elim (hnot h)
            · exact Or.inr h
        · obtain ⟨a, ha, halt, hat⟩ := or_input_true C x j g hg hor ht
          have halive := live_input_of_gate C j g hg hlive a ha halt
          rcases ih a (by omega) halive hat with h | h
          · left
            obtain ⟨v, hv, hxv⟩ := h
            refine ⟨v, ?_, hxv⟩
            rw [hw, mem_support]
            exact or_true_of_input C (oneInput v) j g hg hor a ha halt
              ((mem_support C a v).mp hv)
          · exact Or.inr h


theorem and_inputs_ne_nil {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) : g.inputs ≠ [] := by
  intro hnil
  have ht : value C (fun _ : Fin n => false) (n + j) = true :=
    and_true_of_inputs C (fun _ => false) j g hg hop (by simp [hnil])
  exact not_edgeOn_false G (hclean j g hg hop _ ht)


theorem raw_and_binary {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C) (x : Fin n → Bool)
    (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hraw : ∀ a ∈ g.inputs, a < n + j ∧ ∃ v ∈ support C a, x v = true) :
    ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (∃ u ∈ support C a, x u = true) ∧ (∃ v ∈ support C b, x v = true) := by
  have hlen := (hops g (List.mem_of_getElem? hg)).2
  have hn := and_inputs_ne_nil G C hclean j g hg hop
  generalize heq : g.inputs = ins at hraw hlen hn ⊢
  cases ins with
  | nil => exact False.elim (hn rfl)
  | cons a tail =>
    cases tail with
    | nil =>
      obtain ⟨halt, v, hv, hxv⟩ := hraw a (by simp)
      have ht : value C (oneInput v) (n + j) = true := by
        apply and_true_of_inputs C (oneInput v) j g hg hop
        intro w hw
        rw [heq] at hw
        have hwa : w = a := by simpa using hw
        subst w
        exact ⟨halt, (mem_support C a v).mp hv⟩
      exact False.elim (not_edgeOn_one G v (hclean j g hg hop _ ht))
    | cons b rest =>
      cases rest with
      | nil =>
        exact ⟨a, b, rfl, (hraw a (by simp)).1, (hraw b (by simp)).1,
          (hraw a (by simp)).2, (hraw b (by simp)).2⟩
      | cons c cs => simp at hlen

def pairInput {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun w => decide (w = u ∨ w = v)

@[local simp] theorem pairInput_true_iff {n : ℕ} (u v w : Fin n) :
    pairInput u v w = true ↔ w = u ∨ w = v := by simp [pairInput]

theorem edgeOn_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    EdgeOn G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput_true_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ hab)
    · exact hab
    · exact hab.symm
    · exact False.elim (G.loopless.irrefl _ hab)
  · intro huv
    exact ⟨u, v, huv, by simp, by simp⟩


theorem and_raw_cross_adj {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C)
    (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hins : g.inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j)
    (u v : Fin n) (hu : u ∈ support C a) (hv : v ∈ support C b) : G.Adj u v := by
  have hmono_u : ∀ w, oneInput u w = true → pairInput u v w = true := by
    intro w hw
    simp only [oneInput, decide_eq_true_eq] at hw
    subst w
    simp
  have hmono_v : ∀ w, oneInput v w = true → pairInput u v w = true := by
    intro w hw
    simp only [oneInput, decide_eq_true_eq] at hw
    subst w
    simp
  have hat := wires_mono C hops (oneInput u) (pairInput u v) hmono_u a
    ((mem_support C a u).mp hu)
  have hbt := wires_mono C hops (oneInput v) (pairInput u v) hmono_v b
    ((mem_support C b v).mp hv)
  have ht : value C (pairInput u v) (n + j) = true := by
    apply and_true_of_inputs C (pairInput u v) j g hg hop
    intro w hw
    rw [hins] at hw
    simp only [List.mem_cons, List.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact ⟨ha, hat⟩
    · exact ⟨hb, hbt⟩
  exact (edgeOn_pair_iff G u v).mp (hclean j g hg hop _ ht)


theorem productive_biclique {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C) (j : ℕ) (hj : Productive (n := n) C j) :
    ∃ g a b, C.gates[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
      a < n + j ∧ b < n + j ∧
      (support (n := n) C a).Nonempty ∧ (support (n := n) C b).Nonempty ∧
      ∀ u ∈ support C a, ∀ v ∈ support C b, G.Adj u v := by
  obtain ⟨hlive, g, a, b, hg, hop, hins, ha, hb, hsa, hsb⟩ := hj
  exact ⟨g, a, b, hg, hop, hins, ha, hb, hsa, hsb,
    fun u hu v hv => and_raw_cross_adj G C hops hclean j g a b hg hop hins ha hb u v hu hv⟩


theorem edge_covered_by_productive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hops : AndOr C) (hclean : AndBelow G C)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeOn G x))
    (u v : Fin n) (huv : G.Adj u v) :
    ∃ j g a b, Productive (n := n) C j ∧ C.gates[j]? = some g ∧
      g.op = GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((u ∈ support C a ∧ v ∈ support C b) ∨
       (v ∈ support C a ∧ u ∈ support C b)) := by
  classical
  have hout : value C (pairInput u v) C.output = true := by
    change C.eval (List.ofFn (pairInput u v)) = true
    rw [hfun]
    exact decide_eq_true ((edgeOn_pair_iff G u v).mpr huv)
  have hsout := support_output G C hfun
  rcases trace_raw_or_and C hops (pairInput u v) C.output (live_output C) hout with h | h
  · obtain ⟨w, hw, hwt⟩ := h
    rw [hsout] at hw
    exact False.elim (Finset.notMem_empty w hw)
  · obtain ⟨j, g, hg, hop, hlive, hraw⟩ := h
    obtain ⟨a, b, hins, ha, hb, ⟨p, hp, hpt⟩, ⟨q, hq, hqt⟩⟩ :=
      raw_and_binary G C hops hclean (pairInput u v) j g hg hop hraw
    have hpq := and_raw_cross_adj G C hops hclean j g a b hg hop hins ha hb p q hp hq
    refine ⟨j, g, a, b, ⟨hlive, g, a, b, hg, hop, hins, ha, hb, ⟨p, hp⟩, ⟨q, hq⟩⟩,
      hg, hop, hins, ha, hb, ?_⟩
    simp only [pairInput_true_iff] at hpt hqt
    rcases hpt with rfl | rfl <;> rcases hqt with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ hpq)
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hq⟩
    · exact False.elim (G.loopless.irrefl _ hpq)

end PEqualNP.Outside.L_meta_1407_aux

namespace PEqualNP.Outside.L_meta_1407_aux

open PEqualNP.CircuitLowerBounds

def StarRep {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (j : ℕ) (center : Fin n) (root : ℕ) : Prop :=
  root < n + j ∧ Live (n := n) C root ∧ (support (n := n) C root).Nonempty ∧
    (∀ u ∈ support (n := n) C root, G.Adj center u) ∧
    ∀ g a b, C.gates[j]? = some g → g.inputs = [a, b] →
      (support (n := n) C a = {center} ∧ support C b = support C root) ∨
      (support (n := n) C b = {center} ∧ support C a = support C root)

lemma productive_star_rep {n : ℕ} (G : SimpleGraph (Fin n)) (hG : NoFourCycle G)
    (C : Circuit) (hops : AndOr C) (hclean : AndBelow G C)
    (j : ℕ) (hj : Productive (n := n) C j) :
    ∃ center root, StarRep G C j center root := by
  obtain ⟨g, a, b, hg, hop, hins, ha, hb, hsa, hsb, hcross⟩ :=
    productive_biclique G C hops hclean j hj
  have hindices : ∀ g' a' b', C.gates[j]? = some g' → g'.inputs = [a', b'] →
      a' = a ∧ b' = b := by
    intro g' a' b' hg' hins'
    have hgg : g' = g := Option.some.inj (hg'.symm.trans hg)
    subst g'
    have hh : [a', b'] = [a, b] := hins'.symm.trans hins
    simpa only [List.cons.injEq, and_true] using hh
  rcases biclique_has_singleton_side G hG (support C a) (support C b) hsa hsb hcross with
    ⟨v, hv⟩ | ⟨v, hv⟩
  · refine ⟨v, b, hb, live_input_of_gate C j g hg hj.1 b (by simp [hins]) hb, hsb, ?_, ?_⟩
    · intro u hu
      exact hcross v (by simp [hv]) u hu
    · intro g' a' b' hg' hins'
      obtain ⟨rfl, rfl⟩ := hindices g' a' b' hg' hins'
      exact Or.inl ⟨hv, rfl⟩
  · refine ⟨v, a, ha, live_input_of_gate C j g hg hj.1 a (by simp [hins]) ha, hsa, ?_, ?_⟩
    · intro u hu
      exact (hcross u hu v (by simp [hv])).symm
    · intro g' a' b' hg' hins'
      obtain ⟨rfl, rfl⟩ := hindices g' a' b' hg' hins'
      exact Or.inr ⟨hv, rfl⟩

lemma star_rep_covers_pair {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (j : ℕ) (center : Fin n) (root : ℕ) (hrep : StarRep G C j center root)
    (g : Gate) (a b : ℕ) (hg : C.gates[j]? = some g) (hins : g.inputs = [a, b])
    (u v : Fin n)
    (hpair : (u ∈ support C a ∧ v ∈ support C b) ∨
      (v ∈ support C a ∧ u ∈ support C b)) :
    (center = u ∧ v ∈ support C root) ∨ (center = v ∧ u ∈ support C root) := by
  rcases hrep.2.2.2.2 g a b hg hins with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rcases hpair with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [ha, Finset.mem_singleton] at hu
      exact Or.inl ⟨hu.symm, hb ▸ hv⟩
    · rw [ha, Finset.mem_singleton] at hv
      exact Or.inr ⟨hv.symm, hb ▸ hu⟩
  · rcases hpair with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [hb, Finset.mem_singleton] at hv
      exact Or.inr ⟨hv.symm, ha ▸ hu⟩
    · rw [hb, Finset.mem_singleton] at hu
      exact Or.inl ⟨hu.symm, ha ▸ hv⟩

lemma choose_star_family {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hops : AndOr C) (hclean : AndBelow G C)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeOn G x)) :
    ∃ (center : (productiveGates (n := n) C) → Fin n)
      (root : (productiveGates (n := n) C) → ℕ),
      (∀ i, StarRep G C i.val (center i) (root i)) ∧
      ∀ u v : Fin n, G.Adj u v →
        ∃ i : (productiveGates (n := n) C),
          (center i = u ∧ v ∈ support C (root i)) ∨
          (center i = v ∧ u ∈ support C (root i)) := by
  classical
  have hs : ∀ i : (productiveGates (n := n) C),
      ∃ center root, StarRep G C i.val center root := by
    intro i
    exact productive_star_rep G hG C hops hclean i.val
      ((mem_productiveGates C i.val).mp i.property).2
  choose center root hrep using hs
  refine ⟨center, root, hrep, ?_⟩
  intro u v huv
  obtain ⟨j, g, a, b, hj, hg, hop, hins, ha, hb, hpair⟩ :=
    edge_covered_by_productive G C hops hclean hfun u v huv
  have hjlt : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hmem : j ∈ productiveGates (n := n) C :=
    (mem_productiveGates C j).mpr ⟨hjlt, hj⟩
  let i : (productiveGates (n := n) C) := ⟨j, hmem⟩
  refine ⟨i, ?_⟩
  exact star_rep_covers_pair G C j (center i) (root i) (hrep i) g a b hg hins u v hpair

end PEqualNP.Outside.L_meta_1407_aux

namespace PEqualNP.Outside.L_meta_1407_aux

open Finset PEqualNP.CircuitLowerBounds
open scoped BigOperators

noncomputable def liveSupport {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical
  exact if Live (n := n) C w then support C w else ∅

theorem liveSupport_eq {n : ℕ} (C : Circuit) (w : ℕ) (h : Live (n := n) C w) :
    liveSupport (n := n) C w = support C w := by
  classical
  simp only [liveSupport, h, ↓reduceIte]

noncomputable def rawMergesWithin {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (rawMergeGates (n := n) C).filter (fun j => support C (n + j) ⊆ S)

theorem mem_rawMergesWithin {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (j : ℕ) :
    j ∈ rawMergesWithin C S ↔
      j < C.gates.length ∧ RawMerge (n := n) C j ∧ support C (n + j) ⊆ S := by
  classical
  simp only [rawMergesWithin, mem_filter, mem_rawMergeGates]
  exact ⟨fun ⟨⟨hj, hm⟩, hs⟩ => ⟨hj, hm, hs⟩,
    fun ⟨hj, hm, hs⟩ => ⟨⟨hj, hm⟩, hs⟩⟩

theorem rawWideGates_liveSupport {n : ℕ} (C : Circuit) (S : Finset (Fin n)) :
    @rawWideGates (Fin n) _ (RawMerge (n := n) C)
      (fun j => Classical.propDecidable (RawMerge (n := n) C j))
      (liveSupport C) n C.gates.length S =
      rawMergesWithin C S := by
  classical
  ext j
  simp only [mem_rawWideGates, mem_rawMergesWithin]
  constructor
  · rintro ⟨hj, hm, hw, hs⟩
    exact ⟨hj, hm, by simpa only [liveSupport_eq C _ hm.1] using hs⟩
  · rintro ⟨hj, hm, hs⟩
    have hlive := hm.1
    obtain ⟨_, g, a, b, hg, hop, hin, ha, hb, hna, hnb, hwide⟩ := hm
    refine ⟨hj, ⟨hlive, g, a, b, hg, hop, hin, ha, hb, hna, hnb, hwide⟩, ?_, ?_⟩
    · simpa only [liveSupport_eq C _ hlive] using hwide
    · simpa only [liveSupport_eq C _ hlive] using hs


theorem live_raw_union_count {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C)
    (S : Finset (Fin n)) (R : Finset ℕ)
    (hbound : ∀ r ∈ R, r < n + C.gates.length)
    (hlive : ∀ r ∈ R, Live (n := n) C r)
    (hsub : ∀ r ∈ R, support C r ⊆ S) :
    (R.biUnion (support (n := n) C)).card ≤ R.card + (rawMergesWithin C S).card := by
  classical
  have hi : ∀ i < n, (liveSupport (n := n) C i).card ≤ 1 := by
    intro i hi
    by_cases h : Live (n := n) C i
    · simpa only [liveSupport_eq C i h] using input_support_card_le_one C i hi
    · simp only [liveSupport, h, ↓reduceIte, card_empty]
      omega
  have hstep : ∀ j < C.gates.length, 2 ≤ (liveSupport (n := n) C (n + j)).card →
      (∃ a : ℕ, a < n + j ∧ liveSupport (n := n) C (n + j) = liveSupport C a) ∨
      (RawMerge (n := n) C j ∧ ∃ a b : ℕ, a < n + j ∧ b < n + j ∧
        liveSupport (n := n) C (n + j) = liveSupport C a ∪ liveSupport C b) := by
    intro j hj hw
    have hl : Live (n := n) C (n + j) := by
      by_contra h
      simp only [liveSupport, h, ↓reduceIte, card_empty] at hw
      omega
    have hw' : 2 ≤ (support (n := n) C (n + j)).card := by
      simpa only [liveSupport_eq C _ hl] using hw
    have hg : C.gates[j]? = some (C.gates[j]'hj) := List.getElem?_eq_getElem hj
    rcases wide_support_step G C hops hclean j _ hg hl hw' with
      ⟨a, ha, hla, heq⟩ | ⟨hm, a, b, ha, hb, hla, hlb, heq⟩
    · exact Or.inl ⟨a, ha, by simpa only [liveSupport_eq C _ hl,
        liveSupport_eq C _ hla] using heq⟩
    · exact Or.inr ⟨hm, a, b, ha, hb, by simpa only [liveSupport_eq C _ hl,
        liveSupport_eq C _ hla, liveSupport_eq C _ hlb] using heq⟩
  have hs : ∀ r ∈ R, liveSupport (n := n) C r ⊆ S := by
    intro r hr
    simpa only [liveSupport_eq C r (hlive r hr)] using hsub r hr
  have h := raw_union_count (RawMerge (n := n) C) (liveSupport C) n S hi
    C.gates.length hstep R hbound hs
  have hu : R.biUnion (liveSupport (n := n) C) = R.biUnion (support C) := by
    apply Finset.biUnion_congr rfl
    intro r hr
    exact liveSupport_eq C r (hlive r hr)
  rw [hu, rawWideGates_liveSupport C S] at h
  exact h


theorem circuit_family_union_count {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (center : ι → Fin n) (root : ι → ℕ)
    (hroot : ∀ i, root i < n + C.gates.length)
    (hlive : ∀ i, Live (n := n) C (root i))
    (hstar : ∀ i u, u ∈ support C (root i) → G.Adj (center i) u) :
    (∑ v : Fin n, ((univ.filter (fun i : ι => center i = v)).biUnion
      (fun i => support C (root i))).card) ≤
        Fintype.card ι + (rawMergeGates (n := n) C).card := by
  classical
  let J : Fin n → Finset ι := fun v => univ.filter (fun i => center i = v)
  let S : Fin n → Finset (Fin n) := fun v => univ.filter (fun u => G.Adj v u)
  let U : Fin n → Finset (Fin n) := fun v => (J v).biUnion (fun i => support C (root i))
  let W : Fin n → Finset ℕ := fun v => rawMergesWithin C (S v)
  have hlocal : ∀ v, (U v).card ≤ (J v).card + (W v).card := by
    intro v
    let R := (J v).image root
    have hr : ∀ r ∈ R, r < n + C.gates.length := by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      exact hroot i
    have hl : ∀ r ∈ R, Live (n := n) C r := by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      exact hlive i
    have hs : ∀ r ∈ R, support C r ⊆ S v := by
      intro r hr u hu
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      have hiv : center i = v := (mem_filter.mp hi).2
      exact mem_filter.mpr ⟨mem_univ _, by rw [← hiv]; exact hstar i u hu⟩
    have h := live_raw_union_count G C hops hclean (S v) R hr hl hs
    have heq : R.biUnion (support (n := n) C) = U v := by
      ext u
      simp only [R, U, mem_biUnion, mem_image]
      constructor
      · rintro ⟨r, ⟨i, hi, rfl⟩, hu⟩
        exact ⟨i, hi, hu⟩
      · rintro ⟨i, hi, hu⟩
        exact ⟨root i, ⟨i, hi, rfl⟩, hu⟩
    rw [heq] at h
    have hc : R.card ≤ (J v).card := card_image_le
    change (U v).card ≤ (J v).card + (rawMergesWithin C (S v)).card
    omega
  have hdisj : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint W := by
    intro v hv w hw hvw
    apply Finset.disjoint_left.mpr
    intro j hjv hjw
    obtain ⟨hj, hm, hsv⟩ := (mem_rawMergesWithin C (S v) j).mp hjv
    obtain ⟨_, _, hsw⟩ := (mem_rawMergesWithin C (S w) j).mp hjw
    obtain ⟨_, g, a, b, hg, hop, hin, ha, hb, hna, hnb, hwide⟩ := hm
    have heq := shared_wide_support_implies_same_center G hG v w
      (support C (n + j)) hwide
      (fun u hu => (mem_filter.mp (hsv hu)).2)
      (fun u hu => (mem_filter.mp (hsw hu)).2)
    exact hvw heq
  have hW : (∑ v : Fin n, (W v).card) ≤ (rawMergeGates (n := n) C).card := by
    rw [← Finset.card_biUnion hdisj]
    apply card_le_card
    intro j hj
    obtain ⟨v, _, hj⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hj).1
  have hJ : (∑ v : Fin n, (J v).card) = Fintype.card ι := by
    simpa only [J, Finset.card_univ] using
      sum_center_fibers (univ : Finset ι) center
  change (∑ v : Fin n, (U v).card) ≤ _
  calc
    (∑ v : Fin n, (U v).card) ≤ ∑ v : Fin n, ((J v).card + (W v).card) :=
      sum_le_sum fun v _ => hlocal v
    _ = (∑ v : Fin n, (J v).card) + ∑ v : Fin n, (W v).card := sum_add_distrib
    _ ≤ Fintype.card ι + (rawMergeGates (n := n) C).card := by rw [hJ]; omega

end PEqualNP.Outside.L_meta_1407_aux

namespace PEqualNP.Outside.L_meta_1407_aux

open PEqualNP.CircuitLowerBounds


theorem typed_port_core {α : Type*} [DecidableEq α]
    (A B D : Finset α) (output : α) (children : α → Finset α)
    (hdisjoint : Disjoint A B)
    (hlive : ∀ i ∈ A ∪ B, i ≠ output →
      (∃ j ∈ B, i ∈ children j) ∨ (∃ j ∈ D, i ∈ children j))
    (hB : ∀ j ∈ B, (children j).card ≤ 2)
    (hD : ∀ j ∈ D, (children j).card ≤ 1) :
    A.card ≤ B.card + D.card + 1 := by
  have hsub : A ∪ B ⊆ insert output ((B.biUnion children) ∪ (D.biUnion children)) := by
    intro i hi
    by_cases ho : i = output
    · subst i
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rcases hlive i hi ho with h | h
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr h)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr h)
  have htotal := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisjoint] at htotal
  have htwo : (B.biUnion children).card ≤ B.card * 2 :=
    Finset.card_biUnion_le_card_mul B children 2 hB
  have hone : (D.biUnion children).card ≤ D.card := by
    simpa using Finset.card_biUnion_le_card_mul D children 1 hD
  have hi := Finset.card_insert_le output ((B.biUnion children) ∪ (D.biUnion children))
  have hu := Finset.card_union_le (B.biUnion children) (D.biUnion children)
  omega


theorem live_next {n : ℕ} (C : Circuit) (w : ℕ)
    (hlive : Live (n := n) C w) (hne : w ≠ C.output) :
    ∃ j g, C.gates[j]? = some g ∧ w ∈ g.inputs ∧ w < n + j ∧
      Live (n := n) C (n + j) := by
  rcases Relation.ReflTransGen.cases_head hlive with heq | ⟨b, hread, hb⟩
  · exact False.elim (hne heq)
  · obtain ⟨j, g, hg, hbj, hw, hlt⟩ := hread
    subst b
    exact ⟨j, g, hg, hw, hlt, hb⟩

noncomputable def emptyGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (liveGates (n := n) C).filter (fun j => support (n := n) C (n + j) = ∅)


noncomputable def emptyPorts {n : ℕ} (C : Circuit) (j : ℕ) : Finset ℕ := by
  classical
  exact match C.gates[j]? with
    | none => ∅
    | some g => g.inputs.toFinset.filter
        (fun w => w < n + j ∧ n ≤ w ∧ support (n := n) C w = ∅)

noncomputable def emptyChildren {n : ℕ} (C : Circuit) (j : ℕ) : Finset ℕ :=
  (emptyPorts (n := n) C j).image (fun w => w - n)

@[local simp] theorem mem_emptyGates {n : ℕ} (C : Circuit) (j : ℕ) :
    j ∈ emptyGates (n := n) C ↔
      j ∈ liveGates (n := n) C ∧ support (n := n) C (n + j) = ∅ := by
  classical
  simp [emptyGates]

theorem mem_emptyPorts {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (w : ℕ) :
    w ∈ emptyPorts (n := n) C j ↔
      w ∈ g.inputs ∧ w < n + j ∧ n ≤ w ∧ support (n := n) C w = ∅ := by
  classical
  simp [emptyPorts, hg]

theorem emptyPorts_subset_inputs {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : emptyPorts (n := n) C j ⊆ g.inputs.toFinset := by
  intro w hw
  exact List.mem_toFinset.mpr ((mem_emptyPorts C j g hg w).mp hw).1

theorem emptyChildren_card_le {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : (emptyChildren (n := n) C j).card ≤ g.inputs.length := by
  classical
  have h1 : (emptyChildren (n := n) C j).card ≤ (emptyPorts (n := n) C j).card :=
    Finset.card_image_le
  have h2 := Finset.card_le_card (emptyPorts_subset_inputs (n := n) C j g hg)
  have h3 : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le
  omega

theorem emptyPorts_of_pair {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hinputs : g.inputs = [a, b])
    (ha : (support (n := n) C a).Nonempty) (hb : (support (n := n) C b).Nonempty) :
    emptyPorts (n := n) C j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hw, _, _, hzero⟩ := (mem_emptyPorts C j g hg w).mp hw
  rw [hinputs] at hw
  simp only [List.mem_cons, List.mem_singleton] at hw
  rcases hw with rfl | rfl
  · exact ha.ne_empty hzero
  · exact hb.ne_empty hzero

theorem productive_emptyChildren {n : ℕ} (C : Circuit) (j : ℕ)
    (hj : j ∈ productiveGates (n := n) C) : emptyChildren (n := n) C j = ∅ := by
  obtain ⟨_, _, g, a, b, hg, _, hinputs, _, _, ha, hb⟩ := (mem_productiveGates C j).mp hj
  have h := emptyPorts_of_pair C j g a b hg hinputs ha hb
  simp [emptyChildren, h]

theorem rawMerge_emptyChildren {n : ℕ} (C : Circuit) (j : ℕ)
    (hj : j ∈ rawMergeGates (n := n) C) : emptyChildren (n := n) C j = ∅ := by
  obtain ⟨_, _, g, a, b, hg, _, hinputs, _, _, ha, hb, _⟩ := (mem_rawMergeGates C j).mp hj
  have h := emptyPorts_of_pair C j g a b hg hinputs ha hb
  simp [emptyChildren, h]

theorem productive_subset_empty {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hclean : AndBelow G C) : productiveGates (n := n) C ⊆ emptyGates (n := n) C := by
  intro j hj
  obtain ⟨hjlt, hlive, g, a, b, hg, hop, _⟩ := (mem_productiveGates C j).mp hj
  apply (mem_emptyGates C j).mpr
  exact ⟨(mem_liveGates C j).mpr ⟨hjlt, hlive⟩, support_and G C hclean j g hg hop⟩

theorem rawMerge_subset_live_sdiff_empty {n : ℕ} (C : Circuit) :
    rawMergeGates (n := n) C ⊆ liveGates (n := n) C \ emptyGates (n := n) C := by
  intro j hj
  obtain ⟨hjlt, hlive, g, a, b, hg, hop, hinputs, ha, hb, hsa, hsb, hwide⟩ :=
    (mem_rawMergeGates C j).mp hj
  apply Finset.mem_sdiff.mpr
  refine ⟨(mem_liveGates C j).mpr ⟨hjlt, hlive⟩, ?_⟩
  intro he
  have hs := ((mem_emptyGates C j).mp he).2
  rw [hs, Finset.card_empty] at hwide
  omega


theorem nonempty_output_port {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hne : support (n := n) C (n + j) ≠ ∅) :
    ∃ a ∈ g.inputs, a < n + j ∧ (support (n := n) C a).Nonempty := by
  rcases (hmono g (List.mem_of_getElem? hg)).1 with hand | hor
  · exact False.elim (hne (support_and G C hclean j g hg hand))
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨a, ha, hlt, ht⟩ := or_input_true C (oneInput v) j g hg hor
      ((mem_support C (n + j) v).mp hv)
    exact ⟨a, ha, hlt, v, (mem_support C a v).mpr ht⟩

theorem nonempty_output_emptyChildren_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hne : support (n := n) C (n + j) ≠ ∅) :
    (emptyChildren (n := n) C j).card ≤ 1 := by
  classical
  obtain ⟨a, ha, hlt, hsa⟩ := nonempty_output_port G C hmono hclean j g hg hne
  have hnot : a ∉ emptyPorts (n := n) C j := by
    intro h
    exact hsa.ne_empty ((mem_emptyPorts C j g hg a).mp h).2.2.2
  have hsub : insert a (emptyPorts (n := n) C j) ⊆ g.inputs.toFinset := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact List.mem_toFinset.mpr ha
    · exact emptyPorts_subset_inputs C j g hg hw
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hc
  have hl : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le
  have hlen := (hmono g (List.mem_of_getElem? hg)).2
  have hi : (emptyChildren (n := n) C j).card ≤ (emptyPorts (n := n) C j).card :=
    Finset.card_image_le
  omega


theorem live_empty_consumed {n : ℕ} (C : Circuit) (i : ℕ)
    (hi : i ∈ emptyGates (n := n) C) (hne : i ≠ C.output - n) :
    ∃ j ∈ liveGates (n := n) C, i ∈ emptyChildren (n := n) C j := by
  classical
  obtain ⟨hilive, hs⟩ := (mem_emptyGates C i).mp hi
  have hwne : n + i ≠ C.output := by intro h; apply hne; omega
  obtain ⟨j, g, hg, hw, hlt, hjlive⟩ := live_next C (n + i)
    ((mem_liveGates C i).mp hilive).2 hwne
  obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hg
  refine ⟨j, (mem_liveGates C j).mpr ⟨hjlt, hjlive⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨n + i, (mem_emptyPorts C j g hg (n + i)).mpr ⟨hw, hlt, by omega, hs⟩, ?_⟩
  omega


theorem typed_aggregation_live_bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) :
    2 * (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card ≤
      (liveGates (n := n) C).card + 1 := by
  classical
  let A := productiveGates (n := n) C
  let E := emptyGates (n := n) C
  let L := liveGates (n := n) C
  let W := rawMergeGates (n := n) C
  let B := E \ A
  let D := (L \ E) \ W
  have hAE : A ⊆ E := productive_subset_empty G C hclean
  have hEL : E ⊆ L := fun i hi => ((mem_emptyGates C i).mp hi).1
  have hWL : W ⊆ L \ E := rawMerge_subset_live_sdiff_empty C
  have hAB : Disjoint A B := disjoint_sdiff_self_right
  have hcount := typed_port_core A B D (C.output - n) (emptyChildren (n := n) C) hAB
    (by
      intro i hi hne
      have hiE : i ∈ E := by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hAE hi
        · exact (Finset.mem_sdiff.mp hi).1
      obtain ⟨j, hj, hij⟩ := live_empty_consumed C i hiE hne
      have hjA : j ∉ A := by
        intro h
        have he := productive_emptyChildren C j h
        rw [he] at hij
        exact Finset.notMem_empty _ hij
      have hjW : j ∉ W := by
        intro h
        have he := rawMerge_emptyChildren C j h
        rw [he] at hij
        exact Finset.notMem_empty _ hij
      by_cases hjE : j ∈ E
      · exact Or.inl ⟨j, Finset.mem_sdiff.mpr ⟨hjE, hjA⟩, hij⟩
      · exact Or.inr ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hj, hjE⟩, hjW⟩, hij⟩)
    (by
      intro j hj
      have hjL : j ∈ L := hEL (Finset.mem_sdiff.mp hj).1
      have hjlt := ((mem_liveGates C j).mp hjL).1
      let g := C.gates[j]'hjlt
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
      exact (emptyChildren_card_le C j g hg).trans (hmono g (List.mem_of_getElem? hg)).2)
    (by
      intro j hj
      obtain ⟨hjL, hjE⟩ := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1)
      have hjlt := ((mem_liveGates C j).mp hjL).1
      let g := C.gates[j]'hjlt
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
      have hne : support (n := n) C (n + j) ≠ ∅ := by
        intro h
        exact hjE ((mem_emptyGates C j).mpr ⟨hjL, h⟩)
      exact nonempty_output_emptyChildren_le_one G C hmono hclean j g hg hne)
  have hB : B.card + A.card = E.card := Finset.card_sdiff_add_card_eq_card hAE
  have hE : (L \ E).card + E.card = L.card := Finset.card_sdiff_add_card_eq_card hEL
  have hD : D.card + W.card = (L \ E).card := Finset.card_sdiff_add_card_eq_card hWL
  change 2 * A.card + W.card ≤ L.card + 1
  omega

theorem typed_aggregation_bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) :
    2 * (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card ≤ C.size + 1 := by
  classical
  have h := typed_aggregation_live_bound G C hmono hclean
  have hsub : liveGates (n := n) C ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  change 2 * (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card ≤ C.gates.length + 1
  omega

end PEqualNP.Outside.L_meta_1407_aux

namespace PEqualNP.Outside.L_meta_1407_aux

open PEqualNP.CircuitLowerBounds
open Finset
open scoped BigOperators

lemma clean_total_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (C : Circuit) (hops : AndOr C) (hclean : AndBelow G C)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeOn G x)) :
    ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      G.edgeFinset.card + T.card ≤ C.gates.length + 1 := by
  classical
  obtain ⟨center, root, hrep, hcover⟩ := choose_star_family G hG C hops hclean hfun
  let U : Fin n → Finset (Fin n) := fun v =>
    (univ.filter (fun i : productiveGates (n := n) C => center i = v)).biUnion
      (fun i => support C (root i))
  have hUnionCover : ∀ u v : Fin n, G.Adj u v → v ∈ U u ∨ u ∈ U v := by
    intro u v huv
    obtain ⟨i, hi⟩ := hcover u v huv
    rcases hi with ⟨hc, hv⟩ | ⟨hc, hu⟩
    · left
      exact mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hc⟩, hv⟩
    · right
      exact mem_biUnion.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hc⟩, hu⟩
  have hEdges : G.edgeFinset.card ≤ ∑ v : Fin n, (U v).card :=
    edge_count_le_star_unions G U hUnionCover
  have hRoot : ∀ i : productiveGates (n := n) C, root i < n + C.gates.length := by
    intro i
    have hj := ((mem_productiveGates C i.val).mp i.property).1
    have hr := (hrep i).1
    omega
  have hLive : ∀ i : productiveGates (n := n) C, Live (n := n) C (root i) :=
    fun i => (hrep i).2.1
  have hStar : ∀ (i : productiveGates (n := n) C) u,
      u ∈ support C (root i) → G.Adj (center i) u := fun i => (hrep i).2.2.2.1
  have hFamily := circuit_family_union_count G hG C hops hclean center root hRoot hLive hStar
  have hUnion : (∑ v : Fin n, (U v).card) ≤
      (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card := by
    simpa only [U, Fintype.card_coe] using hFamily
  obtain ⟨T, hTcover, hTcard⟩ := centers_form_cover G
    (univ : Finset (productiveGates (n := n) C)) center (by
      intro u v huv
      obtain ⟨i, hi⟩ := hcover u v huv
      exact ⟨i, mem_univ _, hi.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩)
  have hT : T.card ≤ (productiveGates (n := n) C).card := by
    simpa only [card_univ, Fintype.card_coe] using hTcard
  have hPorts := typed_aggregation_bound G C hops hclean
  change 2 * (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card ≤
    C.gates.length + 1 at hPorts
  exact ⟨T, hTcover, by omega⟩

end PEqualNP.Outside.L_meta_1407_aux


theorem PEqualNP.Outside.L_meta_1407 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out⟩ (List.ofFn x) = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) → ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ G.edgeFinset.card + T.card ≤ gates.length + 1 := by
  intro n G _ hG gates out hops hfun hclean
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gates, out⟩
  have hc : PEqualNP.Outside.L_meta_1407_aux.AndBelow G C := by
    intro j g hg hop x hx
    have hj : j < gates.length := (List.getElem?_eq_some_iff.mp hg).1
    have hget : gates.get ⟨j, hj⟩ = g := (List.getElem?_eq_some_iff.mp hg).2
    have hop' : (gates.get ⟨j, hj⟩).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
      simpa only [hget] using hop
    have hx' : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩
        (List.ofFn x)).getD (n + (⟨j, hj⟩ : Fin gates.length).val) false = true := hx
    exact hclean ⟨j, hj⟩ x hop' hx'
  exact PEqualNP.Outside.L_meta_1407_aux.clean_total_bound G hG C hops hc hfun
