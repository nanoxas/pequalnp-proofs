import Mathlib.Combinatorics.SimpleGraph.Acyclic

import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Algebra.Order.Field.Rat

import Mathlib.Tactic.FinCases

import Mathlib.Data.Fin.VecNotation

import Mathlib.Data.Fintype.BigOperators

import Mathlib.Algebra.BigOperators.Fin

import Mathlib.Data.Finset.Union

import Mathlib.Data.Finset.Card

import Mathlib.Algebra.BigOperators.Group.Finset.Basic

import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Data.List.GetD

import Mathlib.Tactic.ByContra

import Mathlib.Data.List.OfFn

import Mathlib.Algebra.BigOperators.Ring.Finset

import Mathlib.Data.Fintype.EquivFin

import Mathlib.Data.Finset.Powerset

import Mathlib.Data.Nat.Basic

import Mathlib.Combinatorics.SimpleGraph.Clique

import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

import Mathlib.Combinatorics.SimpleGraph.VertexCover

import Mathlib.Combinatorics.Hall.Finite

import Mathlib.Data.Nat.Find

import Mathlib.Tactic.ByContra

import Mathlib.Logic.Equiv.Fin.Basic

import Mathlib.Logic.Equiv.Sum

import PEqualNP.Defs.MetaComplexityLgpMono

import Mathlib.Combinatorics.SimpleGraph.Basic

namespace PEqualNP.Outside.L_meta_1031_aux.RelativeClause

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def openNeighbors (G : SimpleGraph α) (U : Finset α) : Finset α := by
  classical
  exact Finset.univ.filter fun v => ∃ u ∈ U, G.Adj u v

@[simp] theorem mem_openNeighbors {G : SimpleGraph α} {U : Finset α} {v : α} :
    v ∈ openNeighbors G U ↔ ∃ u ∈ U, G.Adj u v := by
  classical
  simp [openNeighbors]

end PEqualNP.Outside.L_meta_1031_aux.RelativeClause

namespace PEqualNP.Outside.L_meta_1031_aux.RelativeClause

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def neighbors (G : SimpleGraph α) (u : α) : Finset α :=
  openNeighbors G {u}

@[simp] theorem mem_neighbors {G : SimpleGraph α} {u v : α} :
    v ∈ neighbors G u ↔ G.Adj u v := by
  classical
  simp [neighbors]

noncomputable def away (G : SimpleGraph α) (u : α) : Finset α := by
  classical
  exact Finset.univ.filter fun v => v ≠ u ∧ ¬ G.Adj u v

@[simp] theorem mem_away {G : SimpleGraph α} {u v : α} :
    v ∈ away G u ↔ v ≠ u ∧ ¬ G.Adj u v := by
  classical
  simp [away]

end PEqualNP.Outside.L_meta_1031_aux.RelativeClause

namespace PEqualNP.Outside.L_meta_1031_aux.RelativeClause

universe u

open Finset

variable {α : Type u} [Fintype α] [DecidableEq α]

noncomputable def liftSet (G : SimpleGraph α) (u : α)
    (S : Finset (away G u : Set α)) : Finset α := insert u (S.image Subtype.val)

@[simp] theorem mem_liftSet_subtype {G : SimpleGraph α} {u : α}
    {S : Finset (away G u : Set α)} {x : (away G u : Set α)} :
    x.val ∈ liftSet G u S ↔ x ∈ S := by
  classical
  have hx := (mem_away.mp x.property).1
  simp [liftSet, hx, Subtype.val_inj]

end PEqualNP.Outside.L_meta_1031_aux.RelativeClause

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs rest : List Gate) (w : List Bool) :
    wiresFrom (gs ++ rest) w = wiresFrom rest (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_initial (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]; simp

theorem wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial gs w
  rw [ht]; simp [hl]

theorem initial_val (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial gs w
  rw [ht, List.getD_append _ _ _ _ h]

def val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (wiresFrom C.gates (List.ofFn x)).getD i false

theorem val_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    val C x i.val = x i := by
  rw [val, initial_val _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

theorem val_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ}
    (hi : n + C.gates.length ≤ i) : val C x i = false := by
  rw [val, List.getD_eq_default _ _ (by simpa [wiresFrom_length] using hi)]

def operand {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j i : ℕ) : Bool :=
  if i < j then val C x i else false

theorem val_gate {n : ℕ} (C : Circuit) (x : Fin n → Bool) {p : ℕ} {g : Gate}
    (hp : C.gates[p]? = some g) :
    val C x (n+p) = g.op.eval (g.inputs.map (operand C x (n+p))) := by
  obtain ⟨hb, heq⟩ := List.getElem?_eq_some_iff.1 hp
  have hsplit : C.gates = (C.gates.take p ++ [g]) ++ C.gates.drop (p+1) := by
    conv_lhs => rw [← List.take_append_drop (p+1) C.gates]
    rw [List.take_succ_eq_append_getElem hb, heq]
  let w := wiresFrom (C.gates.take p) (List.ofFn x)
  have hw : w.length = n+p := by
    simp [w, wiresFrom_length, List.length_take, Nat.min_eq_left hb.le]
  have hread (i : ℕ) : w.getD i false = operand C x (n+p) i := by
    by_cases hi : i < n+p
    · have hv : val C x i = w.getD i false := by
        unfold val
        conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
        exact initial_val _ w i (hw.symm ▸ hi)
      simp only [operand, ite_eq_left hi, hv]
    · rw [operand, ite_eq_right hi, List.getD_eq_default _ _ (by omega)]
  have he : (g.inputs.map fun i => w.getD i false) = g.inputs.map (operand C x (n+p)) :=
    List.map_congr_left fun i _ => hread i
  unfold val
  conv_lhs => rw [hsplit, List.append_assoc, wiresFrom_append]
  change (wiresFrom (C.gates.drop (p+1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n+p) false = _
  rw [initial_val _ _ _ (by simp [hw]), ← hw, he]
  simp [hw]

theorem acts_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ j, val C x j = true → val C y j = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    by_cases hin : j < n
    · let i : Fin n := ⟨j, hin⟩
      simpa only [← val_input C x i, ← val_input C y i] using hxy i (by
        simpa only [← val_input C x i] using hj)
    by_cases hgt : n + C.gates.length ≤ j
    · rw [val_beyond C x hgt] at hj
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ j = n+p := ⟨j-n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hgate := (hC g (List.mem_of_getElem? hg)).1
    have hm (a : ℕ) : operand C x (n+p) a = true → operand C y (n+p) a = true := by
      by_cases ha : a < n+p
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate C x hg] at hj
    rw [val_gate C y hg]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgate
    rcases hgate with h | h
    · simp only [h, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hj ⊢
      exact fun a ha => hm a (hj a ha)
    · simp only [h, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hj ⊢
      obtain ⟨a, ha, he⟩ := hj
      exact ⟨a, ha, hm a he⟩

def WireStep (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ (k : ℕ) (g : Gate), b = n + k ∧ C.gates[k]? = some g ∧ a ∈ g.inputs

def Ancestor (n : ℕ) (C : Circuit) := Relation.TransGen (WireStep n C)

def pairInput {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun k => decide (k = u ∨ k = v)

def singletonInput {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun k => decide (k = u)

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rd (n p a w : ℕ) : ℕ :=
  if w < n + p then w else if w = n + p then a else w - 1

def rdel (n p a : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.take p ++ (C.gates.drop (p + 1)).map
      (fun g => ⟨g.op, g.inputs.map (rd n p a)⟩),
    rd n p a C.output⟩

theorem rdel_length (n p a : ℕ) (C : Circuit) (hp : p < C.gates.length) :
    (rdel n p a C).gates.length + 1 = C.gates.length := by
  simp [rdel]; omega

theorem rdel_get_ge (n p a : ℕ) (C : Circuit) (hp : p < C.gates.length)
    (j : ℕ) (hj : p ≤ j) :
    (rdel n p a C).gates[j]? =
      (C.gates[j + 1]?).map (fun g => (⟨g.op, g.inputs.map (rd n p a)⟩ : Gate)) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega

theorem rd_lt (n p a w : ℕ) (hw : w < n + p) : rd n p a w = w := by
  simp [rd, hw]

theorem rd_eq (n p a : ℕ) : rd n p a (n + p) = a := by
  simp [rd]

theorem rd_gt (n p a w : ℕ) (hw : n + p < w) : rd n p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega

theorem rd_earlier_iff (n p a j i : ℕ) (ha : a < n + p) (hj : p ≤ j) :
    rd n p a i < n + j ↔ i < n + (j + 1) := by
  unfold rd
  split_ifs <;> omega

theorem rdel_monotone {n p a : ℕ} {C : Circuit} (hC : Monotone2 C) :
    Monotone2 (rdel n p a C) := by
  intro g hg
  change g ∈ C.gates.take p ++ _ at hg
  rcases List.mem_append.1 hg with hg | hg
  · exact hC g (List.mem_of_mem_take hg)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨hop, hlen⟩ := hC g0 (List.mem_of_mem_drop hg0)
    exact ⟨hop, by simpa using hlen⟩

theorem rdel_prefix {n : ℕ} (p a : ℕ) (C : Circuit)
    (hp : p < C.gates.length) (x : Fin n → Bool) (w : ℕ) (hw : w < n + p) :
    val (rdel n p a C) x w = val C x w := by
  have hlen : (wiresFrom (C.gates.take p) (List.ofFn x)).length = n + p := by
    simp [wiresFrom_length, Nat.min_eq_left hp.le]
  have he : C.gates = C.gates.take p ++ C.gates.drop p := (List.take_append_drop p C.gates).symm
  unfold val
  change (wiresFrom (C.gates.take p ++ _) (List.ofFn x)).getD w false = _
  rw [wiresFrom_append, initial_val _ _ _ (by omega)]
  conv_rhs => rw [he, wiresFrom_append, initial_val _ _ _ (by omega)]

theorem rdel_agree {n : ℕ} (p a : ℕ) (C : Circuit)
    (hp : p < C.gates.length) (ha : a < n + p) (x : Fin n → Bool)
    (hx : val C x (n + p) = val C x a) :
    ∀ w, val (rdel n p a C) x (rd n p a w) = val C x w := by
  have hlen := rdel_length n p a C hp
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases lt_trichotomy w (n + p) with hw | rfl | hw
    · rw [rd_lt n p a w hw]
      exact rdel_prefix p a C hp x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix p a C hp x a ha
    · rw [rd_gt n p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + (j + 1) := ⟨w - n - 1, by omega⟩
      have he : n + (j + 1) - 1 = n + j := by omega
      rw [he]
      by_cases hjl : j + 1 < C.gates.length
      · let g := C.gates[j + 1]
        have hg : C.gates[j + 1]? = some g := List.getElem?_eq_some_iff.2 ⟨hjl, rfl⟩
        have hg' : (rdel n p a C).gates[j]? =
            some ⟨g.op, g.inputs.map (rd n p a)⟩ := by
          rw [rdel_get_ge n p a C hp j (by omega), hg]
          rfl
        rw [val_gate (rdel n p a C) x hg', val_gate C x hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        change operand (rdel n p a C) x (n + j) (rd n p a i) =
          operand C x (n + (j + 1)) i
        have hiff := rd_earlier_iff n p a j i ha (by omega)
        by_cases hil : i < n + (j + 1)
        · simp only [operand, ite_eq_left hil, ite_eq_left (hiff.2 hil)]
          exact ih i hil
        · simp [operand, hil, mt hiff.1 hil]
      · rw [val_beyond (rdel n p a C) x (by omega), val_beyond C x (by omega)]

theorem rdel_increase {n : ℕ} (p a : ℕ) (C : Circuit) (hC : Monotone2 C)
    (hp : p < C.gates.length) (ha : a < n + p) (x : Fin n → Bool)
    (hx : val C x (n + p) = true → val C x a = true) :
    ∀ w, val C x w = true → val (rdel n p a C) x (rd n p a w) = true := by
  have hlen := rdel_length n p a C hp
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hv
    rcases lt_trichotomy w (n + p) with hw | rfl | hw
    · rw [rd_lt n p a w hw, rdel_prefix p a C hp x w hw]
      exact hv
    · rw [rd_eq, rdel_prefix p a C hp x a ha]
      exact hx hv
    · rw [rd_gt n p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + (j + 1) := ⟨w - n - 1, by omega⟩
      have he : n + (j + 1) - 1 = n + j := by omega
      rw [he]
      by_cases hjl : j + 1 < C.gates.length
      · let g := C.gates[j + 1]
        have hg : C.gates[j + 1]? = some g := List.getElem?_eq_some_iff.2 ⟨hjl, rfl⟩
        have hg' : (rdel n p a C).gates[j]? =
            some ⟨g.op, g.inputs.map (rd n p a)⟩ := by
          rw [rdel_get_ge n p a C hp j (by omega), hg]
          rfl
        have hm (i : ℕ) : operand C x (n + (j + 1)) i = true →
            operand (rdel n p a C) x (n + j) (rd n p a i) = true := by
          intro hv'
          have hil : i < n + (j + 1) := by
            by_contra hc
            simp [operand, hc] at hv'
          have hi' := (rd_earlier_iff n p a j i ha (by omega)).2 hil
          simp only [operand, ite_eq_left hil] at hv'
          simp only [operand, ite_eq_left hi']
          exact ih i hil hv'
        have hop := (hC g (List.mem_of_getElem? hg)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rw [val_gate C x hg] at hv
        rw [val_gate (rdel n p a C) x hg']
        simp only [List.map_map]
        rcases hop with hand | hor
        · simp only [hand, GateOp.eval, List.all_map, Function.comp_apply, id,
            List.all_eq_true] at hv ⊢
          exact fun i hi => hm i (hv i hi)
        · simp only [hor, GateOp.eval, List.any_map, Function.comp_apply, id,
            List.any_eq_true] at hv ⊢
          obtain ⟨i, hi, hi'⟩ := hv
          exact ⟨i, hi, hm i hi'⟩
      · rw [val_beyond C x (by omega)] at hv
        contradiction

theorem delete_and_safe_operand {n : ℕ} {C : Circuit} (hC : Monotone2 C)
    {p a : ℕ} {g : Gate} (hg : C.gates[p]? = some g)
    (hand : g.op = GateOp.and) (hamem : a ∈ g.inputs) (ha : a < n + p)
    (hsafe : ∀ x : Fin n → Bool, val C x a = true → C.eval (List.ofFn x) = true) :
    Monotone2 (rdel n p a C) ∧ (rdel n p a C).size + 1 = C.size ∧
      ∀ x : Fin n → Bool, (rdel n p a C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hp := (List.getElem?_eq_some_iff.1 hg).1
  have himp (x : Fin n → Bool) : val C x (n + p) = true → val C x a = true := by
    intro ht
    rw [val_gate C x hg] at ht
    simp only [hand, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at ht
    simpa [operand, ha] using ht a hamem
  refine ⟨rdel_monotone hC, rdel_length n p a C hp, ?_⟩
  intro x
  by_cases ho : C.eval (List.ofFn x) = true
  · change val (rdel n p a C) x (rd n p a C.output) = C.eval (List.ofFn x)
    rw [ho]
    exact rdel_increase p a C hC hp ha x (himp x) C.output ho
  · have hfalse : C.eval (List.ofFn x) = false := by
      cases hv : C.eval (List.ofFn x) <;> simp_all
    have haf : val C x a = false := by
      cases hv : val C x a
      · rfl
      · exact False.elim (ho (hsafe x hv))
    have hpf : val C x (n + p) = false := by
      cases hv : val C x (n + p)
      · rfl
      · have := himp x hv
        simp [haf] at this
    exact rdel_agree p a C hp ha x (hpf.trans haf.symm) C.output

theorem minimal_no_and_reads_safe {n : ℕ} {C : Circuit}
    (hmin : IsMinimalMonoCircuit n C) {p a : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hand : g.op = GateOp.and)
    (hamem : a ∈ g.inputs) (ha : a < n + p) :
    ¬ (∀ x : Fin n → Bool, val C x a = true → C.eval (List.ofFn x) = true) := by
  intro hsafe
  obtain ⟨hM, hsize, he⟩ := delete_and_safe_operand hmin.1 hg hand hamem ha hsafe
  have hle := hmin.2 (rdel n p a C) hM (funext he)
  omega

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def WireSafe {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C x w = true → F x = true

abbrev SafeGate {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) :=
  {j : Fin C.gates.length // WireSafe F C (n + j.val)}

noncomputable def safeGateCount {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) : ℕ :=
  Nat.card (SafeGate F C)

theorem safeGateCount_le {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) :
    safeGateCount F C ≤ C.size := by
  simpa [safeGateCount, Circuit.size, Nat.card_fin] using
    Nat.card_le_card_of_injective (fun j : SafeGate F C => j.val) Subtype.val_injective

def appendOutputOr (n : ℕ) (C : Circuit) (q : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [C.output, q]⟩], n + C.gates.length⟩

theorem appendOutputOr_eval {n : ℕ} (C : Circuit) (q : ℕ) (x : Fin n → Bool) :
    (appendOutputOr n C q).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || val C x q) := by
  let w := wiresFrom C.gates (List.ofFn x)
  have hw : w.length = n + C.gates.length := by simp [w, wiresFrom_length]
  change (wiresFrom (C.gates ++ [⟨GateOp.or, [C.output, q]⟩]) (List.ofFn x)).getD
    (n + C.gates.length) false = _
  rw [wiresFrom_append]
  change (w ++ [GateOp.or.eval ([C.output, q].map fun i => w.getD i false)]).getD
    (n + C.gates.length) false = (w.getD C.output false || w.getD q false)
  rw [← hw]
  simp [GateOp.eval]

theorem appendOutputOr_prefix {n : ℕ} (C : Circuit) (q : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n + C.gates.length) :
    val (appendOutputOr n C q) x w = val C x w := by
  change (wiresFrom (C.gates ++ _) (List.ofFn x)).getD w false = _
  rw [wiresFrom_append, initial_val _ _ _ (by simpa [wiresFrom_length] using hw)]
  rfl

theorem appendOutputOr_monotone {n : ℕ} {C : Circuit} (hC : Monotone2 C) (q : ℕ) :
    Monotone2 (appendOutputOr n C q) := by
  intro g hg
  change g ∈ C.gates ++ [_] at hg
  rcases List.mem_append.1 hg with hg | hg
  · exact hC g hg
  · simp only [List.mem_singleton] at hg
    subst g
    exact ⟨by simp, by simp⟩

def safeOrLift (n p a q : ℕ) (C : Circuit) : Circuit :=
  appendOutputOr n (rdel n p a C) (rd n p a q)

theorem safeOrLift_size {n p a q : ℕ} {C : Circuit} (hp : p < C.gates.length) :
    (safeOrLift n p a q C).size = C.size := by
  have hl := rdel_length n p a C hp
  simpa [safeOrLift, appendOutputOr, Circuit.size] using hl

theorem safeOrLift_monotone {n p a q : ℕ} {C : Circuit} (hC : Monotone2 C) :
    Monotone2 (safeOrLift n p a q C) :=
  appendOutputOr_monotone (rdel_monotone hC) _

theorem or_agrees_when_safe_false {n : ℕ} {C : Circuit} {p a q : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (x : Fin n → Bool)
    (hfalse : val C x q = false) : val C x (n + p) = val C x a := by
  rw [val_gate C x hg]
  rcases hins with hins | hins <;>
    simp [hor, hins, GateOp.eval, operand, ha, hq, hfalse]

theorem safeOrLift_eval {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    {p a q : ℕ} {g : Gate} (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (hsafe : WireSafe F C q) :
    ∀ x : Fin n → Bool, (safeOrLift n p a q C).eval (List.ofFn x) = F x := by
  have hp := (List.getElem?_eq_some_iff.1 hg).1
  intro x
  rw [safeOrLift, appendOutputOr_eval]
  have hvq : val (rdel n p a C) x (rd n p a q) = val C x q := by
    rw [rd_lt n p a q hq]
    exact rdel_prefix p a C hp x q hq
  rw [hvq]
  cases hval : val C x q with
  | false =>
    have heq := or_agrees_when_safe_false hg hor hins ha hq x hval
    have hh := rdel_agree p a C hp ha x heq C.output
    change (rdel n p a C).eval (List.ofFn x) = C.eval (List.ofFn x) at hh
    simp only [Bool.or_false]
    exact hh.trans (he x)
  | true => simp [hsafe x hval]

theorem safeOrLift_negative_agreement {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    {p a q : ℕ} {g : Gate} (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (hsafe : WireSafe F C q)
    (x : Fin n → Bool) (hneg : F x = false) (w : ℕ)
    (hw : w < n + C.gates.length) (hne : w ≠ n + p) :
    val (safeOrLift n p a q C) x (rd n p a w) = val C x w := by
  have hp := (List.getElem?_eq_some_iff.1 hg).1
  have hlen := rdel_length n p a C hp
  have hfalse : val C x q = false := by
    cases hv : val C x q with
    | false => rfl
    | true => have := hsafe x hv; simp [hneg] at this
  have heq := or_agrees_when_safe_false hg hor hins ha hq x hfalse
  have hbound : rd n p a w < n + (rdel n p a C).gates.length := by
    unfold rd
    split_ifs <;> omega
  rw [safeOrLift, appendOutputOr_prefix _ _ x _ hbound]
  exact rdel_agree p a C hp ha x heq w

theorem safeOrLift_preserves_safe {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    {p a q : ℕ} {g : Gate} (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (hsafe : WireSafe F C q)
    (w : ℕ) (hw : w < n + C.gates.length) (hne : w ≠ n + p)
    (hsw : WireSafe F C w) : WireSafe F (safeOrLift n p a q C) (rd n p a w) := by
  intro x hv
  cases hF : F x with
  | true => rfl
  | false =>
    rw [safeOrLift_negative_agreement hg hor hins ha hq hsafe x hF w hw hne] at hv
    have hh := hsw x hv
    simp [hF] at hh

def shiftGate (p j : ℕ) : ℕ := if j < p then j else j - 1

theorem rd_gate_eq {n p a j : ℕ} (hne : j ≠ p) :
    rd n p a (n + j) = n + shiftGate p j := by
  unfold rd shiftGate
  split_ifs <;> omega

theorem shiftGate_lt {p j k : ℕ} (hp : p < k) (hj : j < k) (hne : j ≠ p) :
    shiftGate p j < k - 1 := by
  unfold shiftGate
  split_ifs <;> omega

theorem shiftGate_injective {p j k : ℕ} (hj : j ≠ p) (hk : k ≠ p)
    (he : shiftGate p j = shiftGate p k) : j = k := by
  unfold shiftGate at he
  split_ifs at he <;> omega

theorem safeOrLift_safe_count {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    {p a q : ℕ} {g : Gate} (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (hsafe : WireSafe F C q)
    (hunsafe : ¬ WireSafe F C (n + p)) :
    safeGateCount F C < safeGateCount F (safeOrLift n p a q C) := by
  classical
  let D := safeOrLift n p a q C
  have hp := (List.getElem?_eq_some_iff.1 hg).1
  have hlen : D.gates.length = C.gates.length := safeOrLift_size hp
  have hneq (j : SafeGate F C) : j.val.val ≠ p := by
    intro hh
    apply hunsafe
    simpa [hh] using j.property
  let inject : SafeGate F C → SafeGate F D := fun j =>
    ⟨⟨shiftGate p j.val.val, by
        rw [hlen]
        have hh := shiftGate_lt hp j.val.isLt (hneq j)
        omega⟩, by
      change WireSafe F (safeOrLift n p a q C) (n + shiftGate p j.val.val)
      rw [← rd_gate_eq (n := n) (a := a) (hneq j)]
      exact safeOrLift_preserves_safe hg hor hins ha hq hsafe (n + j.val.val)
        (by omega) (by intro hh; apply hneq j; omega) j.property⟩
  have hinj : Function.Injective inject := by
    intro j k hh
    have hv := congrArg (fun z : SafeGate F D => z.val.val) hh
    change shiftGate p j.val.val = shiftGate p k.val.val at hv
    apply Subtype.ext
    apply Fin.ext
    exact shiftGate_injective (hneq j) (hneq k) hv
  have hev := safeOrLift_eval he hg hor hins ha hq hsafe
  have hlastSafe : WireSafe F D (n + C.gates.length - 1) := by
    intro x hx
    have hsize := rdel_length n p a C hp
    have hout : D.output = n + C.gates.length - 1 := by
      change n + (rdel n p a C).gates.length = _
      omega
    have hh : D.eval (List.ofFn x) = true := by
      change val D x D.output = true
      rwa [hout]
    exact (hev x).symm.trans hh
  let last : SafeGate F D :=
    ⟨⟨C.gates.length - 1, by rw [hlen]; omega⟩, by
      have heq : n + (C.gates.length - 1) = n + C.gates.length - 1 := by omega
      rw [heq]
      exact hlastSafe⟩
  have hns : ¬ Function.Surjective inject := by
    intro hs
    obtain ⟨j, hj⟩ := hs last
    have hv := congrArg (fun z : SafeGate F D => z.val.val) hj
    change shiftGate p j.val.val = C.gates.length - 1 at hv
    have hh := shiftGate_lt hp j.val.isLt (hneq j)
    omega
  have hh := Fintype.card_lt_of_injective_not_surjective inject hinj hns
  simpa [safeGateCount, Nat.card_eq_fintype_card, D] using hh

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def MaxSafeCount {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ D : Circuit, Monotone2 D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) → D.size = C.size →
    safeGateCount F D ≤ safeGateCount F C

theorem max_safe_or_is_safe {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (hC : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hmax : MaxSafeCount F C) {p a q : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (hsafe : WireSafe F C q) :
    WireSafe F C (n + p) := by
  by_contra hbad
  have hlt := safeOrLift_safe_count he hg hor hins ha hq hsafe hbad
  have hle := hmax (safeOrLift n p a q C) (safeOrLift_monotone hC)
    (safeOrLift_eval he hg hor hins ha hq hsafe)
    (safeOrLift_size (List.getElem?_eq_some_iff.1 hg).1)
  omega

theorem max_safe_reader_is_safe_or {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (hmin : IsMinimalMonoCircuit n C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hmax : MaxSafeCount F C) {p q : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hmem : q ∈ g.inputs) (hq : q < n + p)
    (hsafe : WireSafe F C q) : g.op = GateOp.or ∧ WireSafe F C (n + p) := by
  have hgate := hmin.1 g (List.mem_of_getElem? hg)
  have hop := hgate.1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hand | hor
  · exact False.elim (minimal_no_and_reads_safe hmin hg hand hmem hq
      (fun x hx => (he x).trans (hsafe x hx)))
  refine ⟨hor, ?_⟩
  cases hins : g.inputs with
  | nil => simp [hins] at hmem
  | cons a rest =>
    cases rest with
    | nil =>
      have hqa : q = a := by simpa [hins] using hmem
      subst a
      intro x hx
      rw [val_gate C x hg] at hx
      simp [hor, hins, GateOp.eval, operand, hq] at hx
      exact hsafe x hx
    | cons b tail =>
      have htail : tail.length = 0 := by simpa [hins] using hgate.2
      have hn : tail = [] := by simpa using htail
      subst tail
      have hqb : q = a ∨ q = b := by simpa [hins] using hmem
      rcases hqb with hqa | hqb
      · subst a
        by_cases hb : b < n + p
        · exact max_safe_or_is_safe hmin.1 he hmax hg hor (Or.inl hins) hb hq hsafe
        · intro x hx
          rw [val_gate C x hg] at hx
          simp [hor, hins, GateOp.eval, operand, hb, hq] at hx
          exact hsafe x hx
      · subst b
        by_cases ha : a < n + p
        · exact max_safe_or_is_safe hmin.1 he hmax hg hor (Or.inr hins) ha hq hsafe
        · intro x hx
          rw [val_gate C x hg] at hx
          simp [hor, hins, GateOp.eval, operand, ha, hq] at hx
          exact hsafe x hx

def SafeForwardNormal {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ (q p : ℕ) (g : Gate), C.gates[p]? = some g → q ∈ g.inputs → q < n + p →
    WireSafe F C q → g.op = GateOp.or ∧ WireSafe F C (n + p)

theorem exists_minimum_safe_forward_normal {n : ℕ} (F : (Fin n → Bool) → Bool)
    (C0 : Circuit) (hM0 : Monotone2 C0)
    (he0 : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = F x) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x) ∧
      C.size ≤ C0.size ∧ MaxSafeCount F C ∧ SafeForwardNormal F C := by
  classical
  have hex : ∃ s, ∃ D : Circuit, Monotone2 D ∧ D.size = s ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x := ⟨C0.size, C0, hM0, rfl, he0⟩
  obtain ⟨B, hMB, hsizeB, heB⟩ := Nat.find_spec hex
  have hleast (D : Circuit) (hMD : Monotone2 D)
      (heD : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) : B.size ≤ D.size := by
    rw [hsizeB]
    exact Nat.find_min' hex ⟨D, hMD, rfl, heD⟩
  let P := fun k : ℕ => ∃ D : Circuit, Monotone2 D ∧ D.size = B.size ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) ∧ safeGateCount F D = k
  have hP : P (safeGateCount F B) := ⟨B, hMB, rfl, heB, rfl⟩
  obtain ⟨C, hMC, hsizeC, heC, hcountC⟩ :=
    Nat.findGreatest_spec (safeGateCount_le F B) hP
  have hminC : IsMinimalMonoCircuit n C := by
    refine ⟨hMC, fun D hMD hfun => ?_⟩
    rw [hsizeC]
    apply hleast D hMD
    intro x
    exact (congrFun hfun x).trans (heC x)
  have hmaxC : MaxSafeCount F C := by
    intro D hMD heD hsD
    rw [hcountC]
    apply Nat.le_findGreatest
    · have hh := safeGateCount_le F D
      omega
    · exact ⟨D, hMD, hsD.trans hsizeC, heD, rfl⟩
  refine ⟨C, hminC, heC, ?_, hmaxC, ?_⟩
  · rw [hsizeC]
    exact hleast C0 hM0 he0
  · intro q p g hg hm hq hs
    exact max_safe_reader_is_safe_or hminC heC hmaxC hg hm hq hs

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def CircuitNonconstant (n : ℕ) (C : Circuit) : Prop :=
  ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)

def GateConstant {n : ℕ} (C : Circuit) (p : ℕ) : Prop :=
  ∃ b : Bool, ∀ x : Fin n → Bool, val C x (n + p) = b

theorem minimal_no_alias {n : ℕ} {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    {p a : ℕ} (hp : p < C.gates.length) (ha : a < n + p) :
    ¬ (∀ x : Fin n → Bool, val C x (n + p) = val C x a) := by
  intro heq
  have he : circuitFun n (rdel n p a C) = circuitFun n C := by
    funext x
    exact rdel_agree p a C hp ha x (heq x) C.output
  have hle := hmin.2 (rdel n p a C) (rdel_monotone hmin.1) he
  change C.gates.length ≤ (rdel n p a C).gates.length at hle
  have hlen := rdel_length n p a C hp
  omega

theorem rdel_agree_of_no_reader {n : ℕ} (p a : ℕ) (C : Circuit)
    (hp : p < C.gates.length) (ha : a < n + p)
    (hno : ∀ j g, p < j → C.gates[j]? = some g → n + p ∉ g.inputs)
    (x : Fin n → Bool) :
    ∀ w, w ≠ n + p → val (rdel n p a C) x (rd n p a w) = val C x w := by
  have hlen := rdel_length n p a C hp
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwp
    rcases lt_trichotomy w (n + p) with hw | hw | hw
    · rw [rd_lt n p a w hw]
      exact rdel_prefix p a C hp x w hw
    · exact False.elim (hwp hw)
    · rw [rd_gt n p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + (j + 1) := ⟨w - n - 1, by omega⟩
      have he : n + (j + 1) - 1 = n + j := by omega
      rw [he]
      by_cases hjl : j + 1 < C.gates.length
      · let g := C.gates[j + 1]
        have hg : C.gates[j + 1]? = some g := List.getElem?_eq_some_iff.2 ⟨hjl, rfl⟩
        have hg' : (rdel n p a C).gates[j]? =
            some ⟨g.op, g.inputs.map (rd n p a)⟩ := by
          rw [rdel_get_ge n p a C hp j (by omega), hg]
          rfl
        rw [val_gate (rdel n p a C) x hg', val_gate C x hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        change operand (rdel n p a C) x (n + j) (rd n p a i) =
          operand C x (n + (j + 1)) i
        have hiff := rd_earlier_iff n p a j i ha (by omega)
        by_cases hil : i < n + (j + 1)
        · simp only [operand, ite_eq_left hil, ite_eq_left (hiff.2 hil)]
          apply ih i hil
          intro heq
          exact hno (j + 1) g (by omega) hg (heq ▸ hi)
        · simp [operand, hil, mt hiff.1 hil]
      · rw [val_beyond (rdel n p a C) x (by omega), val_beyond C x (by omega)]

theorem minimal_output_or_later_reader {n : ℕ} {C : Circuit}
    (hn : 0 < n) (hmin : IsMinimalMonoCircuit n C) {p : ℕ} (hp : p < C.gates.length) :
    C.output = n + p ∨ ∃ q g, p < q ∧ C.gates[q]? = some g ∧ n + p ∈ g.inputs := by
  classical
  by_contra h
  push_neg at h
  have hno : ∀ j g, p < j → C.gates[j]? = some g → n + p ∉ g.inputs := by
    intro j g hpj hg
    exact h.2 j g hpj hg
  have he : circuitFun n (rdel n p 0 C) = circuitFun n C := by
    funext x
    exact rdel_agree_of_no_reader p 0 C hp (by omega) hno x C.output h.1
  have hle := hmin.2 (rdel n p 0 C) (rdel_monotone hmin.1) he
  change C.gates.length ≤ (rdel n p 0 C).gates.length at hle
  have hlen := rdel_length n p 0 C hp
  omega

theorem constant_input_forces_constant {n : ℕ} {C : Circuit}
    (hmin : IsMinimalMonoCircuit n C) {q a : ℕ} {g : Gate}
    (hg : C.gates[q]? = some g) (hamem : a ∈ g.inputs) (ha : a < n + q)
    (c : Bool) (hca : ∀ x : Fin n → Bool, val C x a = c) : GateConstant (n := n) C q := by
  classical
  have hq := (List.getElem?_eq_some_iff.mp hg).1
  obtain ⟨hop, hlen⟩ := hmin.1 g (List.mem_of_getElem? hg)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have from_operand (b : ℕ)
      (heq : ∀ x : Fin n → Bool, val C x (n + q) = operand C x (n + q) b) :
      GateConstant (n := n) C q := by
    by_cases hb : b < n + q
    · exact False.elim (minimal_no_alias hmin hq hb (fun x => by
        simpa [operand, hb] using heq x))
    · exact ⟨false, fun x => by rw [heq]; simp [operand, hb]⟩
  cases hins : g.inputs with
  | nil => simp [hins] at hamem
  | cons i rest =>
    cases rest with
    | nil =>
      have hai : a = i := by simpa [hins] using hamem
      subst i
      exact from_operand a (fun x => by
        rw [val_gate C x hg]
        rcases hop with h | h <;> simp [h, hins, GateOp.eval])
    | cons j tail =>
      have ht : tail = [] := by
        have : tail.length = 0 := by simpa [hins] using hlen
        simpa using this
      subst tail
      have hm : a = i ∨ a = j := by simpa [hins] using hamem
      obtain ⟨b, hbin⟩ : ∃ b, g.inputs = [a, b] ∨ g.inputs = [b, a] := by
        rcases hm with rfl | rfl
        · exact ⟨j, Or.inl hins⟩
        · exact ⟨i, Or.inr hins⟩
      have heq (x : Fin n → Bool) : val C x (n + q) =
          if g.op = GateOp.and then c && operand C x (n + q) b
          else c || operand C x (n + q) b := by
        rw [val_gate C x hg]
        rcases hbin with hbin | hbin <;> rcases hop with hop | hop <;>
          simp [hop, hbin, GateOp.eval, operand, ha, hca x, Bool.and_comm, Bool.or_comm]
      cases c with
      | false =>
        rcases hop with hand | hor
        · exact ⟨false, fun x => by rw [heq]; simp [hand]⟩
        · exact from_operand b (fun x => by rw [heq]; simp [hor])
      | true =>
        rcases hop with hand | hor
        · exact from_operand b (fun x => by rw [heq]; simp [hand])
        · exact ⟨true, fun x => by rw [heq]; simp [hor]⟩

theorem minimal_no_constant_gate {n : ℕ} {C : Circuit}
    (hn : 0 < n) (hmin : IsMinimalMonoCircuit n C) (hnc : CircuitNonconstant n C)
    {p : ℕ} (hp : p < C.gates.length) : ¬ GateConstant (n := n) C p := by
  suffices hall : ∀ r p, p < C.gates.length → C.gates.length - p = r →
      ¬ GateConstant (n := n) C p by
    exact hall _ p hp rfl
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro p hp hr hconst
    obtain ⟨b, hb⟩ := hconst
    rcases minimal_output_or_later_reader hn hmin hp with hout | ⟨q, g, hpq, hg, hread⟩
    · obtain ⟨x, y, hxy⟩ := hnc
      apply hxy
      change val C x C.output = val C y C.output
      rw [hout, hb x, hb y]
    · have hq := (List.getElem?_eq_some_iff.mp hg).1
      have hqc := constant_input_forces_constant hmin hg hread (by omega) b hb
      exact ih (C.gates.length - q) (by omega) q hq rfl hqc

def CleanMono (n : ℕ) (C : Circuit) : Prop :=
  ∀ p g, C.gates[p]? = some g → ∃ a b,
    g.inputs = [a, b] ∧ a < n + p ∧ b < n + p ∧ a ≠ b

theorem minimal_clean_mono {n : ℕ} {C : Circuit}
    (hn : 0 < n) (hmin : IsMinimalMonoCircuit n C) (hnc : CircuitNonconstant n C) :
    CleanMono n C := by
  intro p g hg
  have hp := (List.getElem?_eq_some_iff.mp hg).1
  have hconst := minimal_no_constant_gate hn hmin hnc hp
  obtain ⟨hop, hlen⟩ := hmin.1 g (List.mem_of_getElem? hg)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have no_operand (a : ℕ)
      (heq : ∀ x : Fin n → Bool, val C x (n + p) = operand C x (n + p) a) : False := by
    by_cases ha : a < n + p
    · exact minimal_no_alias hmin hp ha (fun x => by simpa [operand, ha] using heq x)
    · exact hconst ⟨false, fun x => by rw [heq]; simp [operand, ha]⟩
  cases hins : g.inputs with
  | nil =>
    exfalso
    rcases hop with hand | hor
    · exact hconst ⟨true, fun x => by rw [val_gate C x hg]; simp [hand, hins, GateOp.eval]⟩
    · exact hconst ⟨false, fun x => by rw [val_gate C x hg]; simp [hor, hins, GateOp.eval]⟩
  | cons a rest =>
    cases rest with
    | nil =>
      exact False.elim (no_operand a (fun x => by
        rw [val_gate C x hg]
        rcases hop with h | h <;> simp [h, hins, GateOp.eval]))
    | cons b tail =>
      have ht : tail = [] := by
        have : tail.length = 0 := by simpa [hins] using hlen
        simpa using this
      subst tail
      have ha : a < n + p := by
        by_contra ha
        rcases hop with hand | hor
        · exact hconst ⟨false, fun x => by
            rw [val_gate C x hg]; simp [hand, hins, GateOp.eval, operand, ha]⟩
        · exact no_operand b (fun x => by
            rw [val_gate C x hg]; simp [hor, hins, GateOp.eval, operand, ha])
      have hb : b < n + p := by
        by_contra hb
        rcases hop with hand | hor
        · exact hconst ⟨false, fun x => by
            rw [val_gate C x hg]; simp [hand, hins, GateOp.eval, operand, hb]⟩
        · exact no_operand a (fun x => by
            rw [val_gate C x hg]; simp [hor, hins, GateOp.eval, operand, hb])
      have hab : a ≠ b := by
        rintro rfl
        apply no_operand a
        intro x
        rw [val_gate C x hg]
        rcases hop with h | h <;> simp [h, hins, GateOp.eval]
      exact ⟨a, b, rfl, ha, hb, hab⟩

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.PrefixBuilder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

theorem getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by simp [List.getD]

end PEqualNP.Outside.L_meta_1031_aux.PrefixBuilder

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Reaches (n : ℕ) (C : Circuit) (a b : ℕ) : Prop := a = b ∨ Ancestor n C a b

def AndFreeAt (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∀ p g, C.gates[p]? = some g → g.op = GateOp.and → ¬ Reaches n C (n + p) w

noncomputable def rawSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => Reaches n C i.val w

@[simp] theorem mem_rawSupport {n : ℕ} {C : Circuit} {w : ℕ} {i : Fin n} :
    i ∈ rawSupport n C w ↔ Reaches n C i.val w := by
  classical
  simp [rawSupport]

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def BadRawSupport {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w : ℕ) : Prop :=
  ∃ u ∈ rawSupport n C w, ∃ v ∈ rawSupport n C w, G.Adj u v

noncomputable def badRawBanks {n : ℕ} (G : SimpleGraph (Fin n))
    (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j =>
    AndFreeAt n C (n + j) ∧ BadRawSupport G C (n + j)

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

@[simp] theorem mem_badRawBanks {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {q : ℕ} :
    q ∈ badRawBanks G C ↔ q < C.gates.length ∧
      AndFreeAt n C (n + q) ∧ BadRawSupport G C (n + q) := by
  classical
  simp [badRawBanks]

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open Finset

noncomputable def gateInputSet (C : Circuit) (j : ℕ) : Finset ℕ :=
  (C.gates.getD j ⟨GateOp.or, []⟩).inputs.toFinset

theorem gateInputSet_of_get {C : Circuit} {j : ℕ} {g : Gate}
    (hg : C.gates[j]? = some g) : gateInputSet C j = g.inputs.toFinset := by
  simp [gateInputSet, List.getD_eq_getElem?_getD, hg]

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.WeightedMatching

open Finset

variable {α : Type*} [DecidableEq α]

noncomputable def independentSetsOn (G : SimpleGraph α) (V : Finset α) : Finset (Finset α) := by
  classical
  exact V.powerset.filter fun S => G.IsIndepSet (S : Set α)

@[simp] theorem mem_independentSetsOn {G : SimpleGraph α} {V S : Finset α} :
    S ∈ independentSetsOn G V ↔ S ⊆ V ∧ G.IsIndepSet (S : Set α) := by
  classical
  simp [independentSetsOn]

end PEqualNP.Outside.L_meta_1031_aux.WeightedMatching

namespace PEqualNP.Outside.L_meta_1031_aux.WeightedMatching

open Finset

variable {α : Type*} [DecidableEq α] {k : ℕ}

def MatchConflict (s t : Fin k → α) (X Y : Finset α) : Prop :=
  ∃ i, (s i ∈ X ∧ t i ∈ Y) ∨ (t i ∈ X ∧ s i ∈ Y)

theorem MatchConflict.symm {s t : Fin k → α} {X Y : Finset α}
    (h : MatchConflict s t X Y) : MatchConflict s t Y X := by
  obtain ⟨i, h | h⟩ := h
  · exact ⟨i, Or.inr ⟨h.2, h.1⟩⟩
  · exact ⟨i, Or.inl ⟨h.2, h.1⟩⟩

noncomputable def leftSet (s : Fin k → α) : Finset α := univ.image s

@[simp] theorem mem_leftSet {s : Fin k → α} {x : α} :
    x ∈ leftSet s ↔ ∃ i, s i = x := by
  classical
  simp [leftSet]

noncomputable def leafIndices (G : SimpleGraph α) (s t : Fin k → α) : Finset (Fin k) := by
  classical
  exact univ.filter fun i => ∀ j, G.Adj (s i) (t j) → i = j

@[simp] theorem mem_leafIndices {G : SimpleGraph α} {s t : Fin k → α} {i : Fin k} :
    i ∈ leafIndices G s t ↔ ∀ j, G.Adj (s i) (t j) → i = j := by
  classical
  simp [leafIndices]

noncomputable def extension (G : SimpleGraph α) (S J : Finset α) : Finset α := by
  classical
  exact J ∪ S.filter (fun u => ∀ v ∈ J, ¬ G.Adj u v)

@[simp] theorem mem_extension {G : SimpleGraph α} {S J : Finset α} {x : α} :
    x ∈ extension G S J ↔ x ∈ J ∨ (x ∈ S ∧ ∀ v ∈ J, ¬ G.Adj x v) := by
  classical
  simp [extension]

@[simp] theorem extension_empty (G : SimpleGraph α) (S : Finset α) :
    extension G S ∅ = S := by
  classical
  simp [extension]

end PEqualNP.Outside.L_meta_1031_aux.WeightedMatching

namespace PEqualNP.Outside.L_meta_1031_aux.WeightedMatching

open Finset

variable {α : Type*} [DecidableEq α] {k r : ℕ}

noncomputable def badClauses (G : SimpleGraph α) (A : Fin r → Finset α) : Finset (Fin r) := by
  classical
  exact univ.filter fun j => ¬ G.IsIndepSet (A j : Set α)

@[simp] theorem mem_badClauses {G : SimpleGraph α} {A : Fin r → Finset α} {j : Fin r} :
    j ∈ badClauses G A ↔ ¬ G.IsIndepSet (A j : Set α) := by
  classical
  simp [badClauses]

end PEqualNP.Outside.L_meta_1031_aux.WeightedMatching

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open Finset

noncomputable def rawBankSet {n : ℕ} (C : Circuit) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun q => AndFreeAt n C (n + q) ∧ P (n + q)

@[simp] theorem mem_rawBankSet {n : ℕ} {C : Circuit} {P : ℕ → Prop} {q : ℕ} :
    q ∈ rawBankSet (n := n) C P ↔ q < C.gates.length ∧ AndFreeAt n C (n + q) ∧ P (n + q) := by
  classical
  simp [rawBankSet]

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.InducedStarChoices

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}

def support (c : Fin k → α) (L : Fin k → Finset α) : Finset α :=
  univ.image c ∪ univ.biUnion L

end PEqualNP.Outside.L_meta_1031_aux.InducedStarChoices

namespace PEqualNP.Outside.L_meta_1031_aux.FourClauseSignatures

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

structure System (G H : SimpleGraph α) where
  sig : α → Finset (Fin 4)
  edge_hits : ∀ u v, H.Adj u v → sig u ∪ sig v = Finset.univ
  independent_rejected : ∀ I : Finset α, G.IsIndepSet (I : Set α) →
    ∃ j : Fin 4, ∀ v ∈ I, j ∉ sig v

end PEqualNP.Outside.L_meta_1031_aux.FourClauseSignatures

namespace PEqualNP.Outside.L_meta_1031_aux.FourClauseSignatures

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

def Active (H : SimpleGraph α) (u : α) : Prop := ∃ v, H.Adj u v

noncomputable def typeClass {G H : SimpleGraph α} (S : System G H)
    (T : Finset (Fin 4)) : Finset α := by
  classical
  exact Finset.univ.filter fun v => Active H v ∧ S.sig v = T

@[simp] theorem mem_typeClass {G H : SimpleGraph α} {S : System G H}
    {T : Finset (Fin 4)} {v : α} :
    v ∈ typeClass S T ↔ Active H v ∧ S.sig v = T := by
  classical
  simp [typeClass]

end PEqualNP.Outside.L_meta_1031_aux.FourClauseSignatures

namespace PEqualNP.Outside.L_meta_1031_aux.FourClauseSignatures

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

noncomputable def System.ofClauses {G H : SimpleGraph α}
    (V : Fin 4 → Finset α)
    (hcover : ∀ j, H.IsVertexCover (V j : Set α))
    (hsound : ∀ I : Finset α, G.IsIndepSet (I : Set α) → ∃ j, Disjoint I (V j)) :
    System G H := by
  classical
  refine {
    sig := fun v => Finset.univ.filter (fun j => v ∈ V j)
    edge_hits := ?_
    independent_rejected := ?_
  }
  · intro u v huv
    apply Finset.eq_univ_of_forall
    intro j
    rcases hcover j huv with hu | hv
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩))
  · intro I hI
    obtain ⟨j,hj⟩ := hsound I hI
    refine ⟨j,?_⟩
    intro v hv hmem
    exact Finset.disjoint_left.mp hj hv (Finset.mem_filter.mp hmem).2

@[simp] theorem System.ofClauses_mem_sig {G H : SimpleGraph α}
    (V : Fin 4 → Finset α)
    (hcover : ∀ j, H.IsVertexCover (V j : Set α))
    (hsound : ∀ I : Finset α, G.IsIndepSet (I : Set α) → ∃ j, Disjoint I (V j))
    (v : α) (j : Fin 4) :
    j ∈ (System.ofClauses V hcover hsound).sig v ↔ v ∈ V j := by
  classical
  simp [System.ofClauses]

end PEqualNP.Outside.L_meta_1031_aux.FourClauseSignatures

namespace PEqualNP.Outside.L_meta_1031_aux.DisjointStarFamily

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

def support (c : ι → α) (L : ι → Finset α) : Finset α :=
  Finset.univ.biUnion fun i => insert (c i) (L i)

end PEqualNP.Outside.L_meta_1031_aux.DisjointStarFamily

namespace PEqualNP.Outside.L_meta_1031_aux

open Finset

variable {ι : Type*} [DecidableEq ι]

def Minterm (f : Finset ι → Bool) (A : Finset ι) : Prop :=
  f A = true ∧ ∀ T ⊆ A, f T = true → T = A

def FeatureMonotone (f : Finset ι → Bool) : Prop :=
  ∀ A B, A ⊆ B → f A = true → f B = true

def FeatureSupported (f : Finset ι → Bool) (S : Finset ι) : Prop :=
  ∀ A, f A = f (A ∩ S)

def MintermRectangle (f : Finset ι → Bool) : Prop :=
  ∀ A B C, Minterm f A → Minterm f B → Minterm f C →
    B ⊆ A ∪ C → A ∩ B ∩ C = ∅ → f ((A ∪ C) \ B) = true

theorem Minterm.subset_support {f : Finset ι → Bool} {A S : Finset ι}
    (h : Minterm f A) (hs : FeatureSupported f S) : A ⊆ S := by
  have he : A ∩ S = A := h.2 (A ∩ S) inter_subset_left ((hs A).symm.trans h.1)
  intro i hi
  exact (mem_inter.mp (he.symm ▸ hi)).2

theorem FeatureSupported.mono {f : Finset ι → Bool} {S T : Finset ι}
    (hs : FeatureSupported f S) (hst : S ⊆ T) : FeatureSupported f T := by
  intro A
  have he : (A ∩ T) ∩ S = A ∩ S := by
    ext i
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hst h.2⟩,h.2⟩⟩
  rw [hs A,hs (A ∩ T),he]

theorem feature_monotone_and {f g : Finset ι → Bool}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g) :
    FeatureMonotone (fun A => f A && g A) := by
  intro A B hab h
  obtain ⟨hfa,hga⟩ := Bool.and_eq_true_iff.mp h
  exact Bool.and_eq_true_iff.mpr ⟨hf A B hab hfa,hg A B hab hga⟩

theorem feature_monotone_or {f g : Finset ι → Bool}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g) :
    FeatureMonotone (fun A => f A || g A) := by
  intro A B hab h
  rcases Bool.or_eq_true_iff.mp h with hfa | hga
  · exact Bool.or_eq_true_iff.mpr (Or.inl (hf A B hab hfa))
  · exact Bool.or_eq_true_iff.mpr (Or.inr (hg A B hab hga))

theorem feature_supported_and {f g : Finset ι → Bool} {S T : Finset ι}
    (hf : FeatureSupported f S) (hg : FeatureSupported g T) :
    FeatureSupported (fun A => f A && g A) (S ∪ T) := by
  intro A
  change (f A && g A) = (f (A ∩ (S ∪ T)) && g (A ∩ (S ∪ T)))
  rw [hf.mono subset_union_left A,hg.mono subset_union_right A]

theorem feature_supported_or {f g : Finset ι → Bool} {S T : Finset ι}
    (hf : FeatureSupported f S) (hg : FeatureSupported g T) :
    FeatureSupported (fun A => f A || g A) (S ∪ T) := by
  intro A
  change (f A || g A) = (f (A ∩ (S ∪ T)) || g (A ∩ (S ∪ T)))
  rw [hf.mono subset_union_left A,hg.mono subset_union_right A]

theorem minterm_and_left {f g : Finset ι → Bool} {S T A : Finset ι}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (h : Minterm (fun X => f X && g X) A) :
    Minterm f (A ∩ S) := by
  obtain ⟨hfa,hga⟩ := Bool.and_eq_true_iff.mp h.1
  refine ⟨(hs A).symm.trans hfa,?_⟩
  intro X hX hfx
  have hsub : X ∪ (A ∩ T) ⊆ A := union_subset (hX.trans inter_subset_left) inter_subset_left
  have htrue : (f (X ∪ (A ∩ T)) && g (X ∪ (A ∩ T))) = true :=
    Bool.and_eq_true_iff.mpr ⟨hf X _ subset_union_left hfx,
      hg (A ∩ T) _ subset_union_right ((ht A).symm.trans hga)⟩
  have he : X ∪ (A ∩ T) = A := h.2 _ hsub htrue
  apply Subset.antisymm hX
  intro i hi
  rcases mem_union.mp (he.symm ▸ (mem_inter.mp hi).1) with hix | hit
  · exact hix
  · exact (Finset.disjoint_left.mp hdis (mem_inter.mp hi).2 (mem_inter.mp hit).2).elim

theorem minterm_and_right {f g : Finset ι → Bool} {S T A : Finset ι}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (h : Minterm (fun X => f X && g X) A) :
    Minterm g (A ∩ T) := by
  apply minterm_and_left hg hf ht hs hdis.symm
  simpa only [Bool.and_comm] using h

theorem minterm_or_cases {f g : Finset ι → Bool} {A : Finset ι}
    (h : Minterm (fun X => f X || g X) A) : Minterm f A ∨ Minterm g A := by
  rcases Bool.or_eq_true_iff.mp h.1 with hfa | hga
  · exact Or.inl ⟨hfa,fun T hT ht => h.2 T hT (Bool.or_eq_true_iff.mpr (Or.inl ht))⟩
  · exact Or.inr ⟨hga,fun T hT ht => h.2 T hT (Bool.or_eq_true_iff.mpr (Or.inr ht))⟩

theorem rectangle_restrict_subset {A B C S : Finset ι} (h : B ⊆ A ∪ C) :
    B ∩ S ⊆ (A ∩ S) ∪ (C ∩ S) := by
  intro i hi
  obtain ⟨hib,his⟩ := mem_inter.mp hi
  rcases mem_union.mp (h hib) with hia | hic
  · exact mem_union_left _ (mem_inter.mpr ⟨hia,his⟩)
  · exact mem_union_right _ (mem_inter.mpr ⟨hic,his⟩)

theorem rectangle_restrict_empty {A B C S : Finset ι} (h : A ∩ B ∩ C = ∅) :
    (A ∩ S) ∩ (B ∩ S) ∩ (C ∩ S) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨hAB,hC⟩ := mem_inter.mp hi
  obtain ⟨hA,hB⟩ := mem_inter.mp hAB
  have hm : i ∈ A ∩ B ∩ C := mem_inter.mpr
    ⟨mem_inter.mpr ⟨(mem_inter.mp hA).1,(mem_inter.mp hB).1⟩,(mem_inter.mp hC).1⟩
  simpa [h] using hm

theorem rectangle_restrict_sdiff {A B C S : Finset ι} :
    ((A ∩ S) ∪ (C ∩ S)) \ (B ∩ S) ⊆ (A ∪ C) \ B := by
  intro i hi
  obtain ⟨hiAC,hnot⟩ := mem_sdiff.mp hi
  have his : i ∈ S := by
    rcases mem_union.mp hiAC with hia | hic
    · exact (mem_inter.mp hia).2
    · exact (mem_inter.mp hic).2
  refine mem_sdiff.mpr ⟨?_,fun hib => hnot (mem_inter.mpr ⟨hib,his⟩)⟩
  rcases mem_union.mp hiAC with hia | hic
  · exact mem_union_left _ (mem_inter.mp hia).1
  · exact mem_union_right _ (mem_inter.mp hic).1

theorem minterm_rectangle_and {f g : Finset ι → Bool} {S T : Finset ι}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (rf : MintermRectangle f) (rg : MintermRectangle g) :
    MintermRectangle (fun A => f A && g A) := by
  intro A B C hA hB hC hsub hempty
  have hleft := rf (A ∩ S) (B ∩ S) (C ∩ S)
    (minterm_and_left hf hg hs ht hdis hA)
    (minterm_and_left hf hg hs ht hdis hB)
    (minterm_and_left hf hg hs ht hdis hC)
    (rectangle_restrict_subset hsub) (rectangle_restrict_empty hempty)
  have hright := rg (A ∩ T) (B ∩ T) (C ∩ T)
    (minterm_and_right hf hg hs ht hdis hA)
    (minterm_and_right hf hg hs ht hdis hB)
    (minterm_and_right hf hg hs ht hdis hC)
    (rectangle_restrict_subset hsub) (rectangle_restrict_empty hempty)
  exact Bool.and_eq_true_iff.mpr ⟨hf _ _ rectangle_restrict_sdiff hleft,
    hg _ _ rectangle_restrict_sdiff hright⟩

theorem minterm_avoids_other_support {f g : Finset ι → Bool}
    {S T A B D : Finset ι} (hf : FeatureMonotone f)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (hA : Minterm f A) (hB : Minterm g B)
    (had : A ⊆ D) : f (D \ B) = true := by
  apply hf A _ ?_ hA.1
  intro i hi
  exact mem_sdiff.mpr ⟨had hi,fun hib => Finset.disjoint_left.mp hdis
    (hA.subset_support hs hi) (hB.subset_support ht hib)⟩

theorem minterm_rectangle_or {f g : Finset ι → Bool} {S T : Finset ι}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (rf : MintermRectangle f) (rg : MintermRectangle g) :
    MintermRectangle (fun A => f A || g A) := by
  intro A B C hA hB hC hsub hempty
  apply Bool.or_eq_true_iff.mpr
  rcases minterm_or_cases hB with hBf | hBg
  · rcases minterm_or_cases hA with hAf | hAg
    · rcases minterm_or_cases hC with hCf | hCg
      · exact Or.inl (rf A B C hAf hBf hCf hsub hempty)
      · exact Or.inr (minterm_avoids_other_support hg ht hs hdis.symm hCg hBf subset_union_right)
    · exact Or.inr (minterm_avoids_other_support hg ht hs hdis.symm hAg hBf subset_union_left)
  · rcases minterm_or_cases hA with hAf | hAg
    · exact Or.inl (minterm_avoids_other_support hf hs ht hdis hAf hBg subset_union_left)
    · rcases minterm_or_cases hC with hCf | hCg
      · exact Or.inl (minterm_avoids_other_support hf hs ht hdis hCf hBg subset_union_right)
      · exact Or.inr (rg A B C hAg hBg hCg hsub hempty)

theorem minterm_literal_iff (i : ι) (A : Finset ι) :
    Minterm (fun X => decide (i ∈ X)) A ↔ A = {i} := by
  constructor
  · intro h
    have hi : i ∈ A := of_decide_eq_true h.1
    exact (h.2 {i} (singleton_subset_iff.mpr hi) (by simp)).symm
  · rintro rfl
    refine ⟨by simp,?_⟩
    intro T hT ht
    apply Subset.antisymm hT
    exact singleton_subset_iff.mpr (of_decide_eq_true ht)

theorem minterm_rectangle_literal (i : ι) :
    MintermRectangle (fun A => decide (i ∈ A)) := by
  intro A B C hA hB hC _ hempty
  have ha := (minterm_literal_iff i A).mp hA
  have hb := (minterm_literal_iff i B).mp hB
  have hc := (minterm_literal_iff i C).mp hC
  simp [ha,hb,hc] at hempty

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open Finset

noncomputable def bankOccurrence {α ι : Type*}
    (W : Finset ι) (B : ι → Finset α) (u : α) : Finset ι := by
  classical
  exact W.filter (fun w => u ∈ B w)

noncomputable def bankFeatures {α ι : Type*}
    (W : Finset ι) (B : ι → Finset α) (I : Finset α) : Finset ι := by
  classical
  exact W.filter (fun w => ∃ u ∈ B w, u ∈ I)

@[simp] theorem mem_bankOccurrence {α ι : Type*}
    (W : Finset ι) (B : ι → Finset α) (u : α) (w : ι) :
    w ∈ bankOccurrence W B u ↔ w ∈ W ∧ u ∈ B w := by
  classical
  simp [bankOccurrence]

@[simp] theorem mem_bankFeatures {α ι : Type*}
    (W : Finset ι) (B : ι → Finset α) (I : Finset α) (w : ι) :
    w ∈ bankFeatures W B I ↔ w ∈ W ∧ ∃ u ∈ B w, u ∈ I := by
  classical
  simp [bankFeatures]

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.RelativeForestCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

def elimState (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) :
    List (Bool ⊕ ℕ) × List Gate :=
  elimPass m (gs.take j) acc

lemma elimState_zero (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc 0 = acc := rfl

lemma elimState_end (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc gs.length = elimPass m gs acc := by
  simp [elimState]

lemma elimState_succ (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    elimState m gs acc (j + 1) = elimStep m (elimState m gs acc j) gs[j] := by
  unfold elimState
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, elimPass_append,
    elimPass_cons, elimPass_nil]

lemma elimState_getD_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j k i : ℕ) (d : Bool ⊕ ℕ) (hjk : j ≤ k) (hk : k ≤ gs.length) (hi : i < acc.1.length + j) :
    (elimState m gs acc k).1.getD i d = (elimState m gs acc j).1.getD i d := by
  have htake : gs.take k = gs.take j ++ (gs.drop j).take (k - j) := by
    have h1 := List.take_add (l := gs) (i := j) (j := k - j)
    rw [show j + (k - j) = k by omega] at h1
    exact h1
  rw [elimState, htake, elimPass_append]
  exact elimPass_getD_lt m i d _ _ (by rw [elimPass_fst_len, List.length_take, Nat.min_eq_left (by omega)]; exact hi)

def elimDropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : Finset ℕ :=
  (Finset.range gs.length).filter (fun j =>
    if hj : j < gs.length then
      (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
        (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
    else false)

lemma elimPass_card_dropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length + (elimDropped m gs acc).card = acc.2.length + gs.length := by
  suffices ∀ k ≤ gs.length,
      (elimState m gs acc k).2.length +
        ((Finset.range k).filter (fun j =>
          if hj : j < gs.length then
            (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
              (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
          else false)).card = acc.2.length + k by
    simpa [elimState_end, elimDropped] using this gs.length le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    simp [elimState_zero]
  | succ k ih =>
    intro hk
    have hklt : k < gs.length := by omega
    have hih := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter (fun j =>
        if hj : j < gs.length then
          (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
            (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
        else false) := by
      simp
    rw [elimState_succ m gs acc k hklt]
    simp only [elimStep, List.length_append, hklt, ↓reduceDIte]
    cases hopt : (simplifyGate gs[k].op (m + (elimState m gs acc k).2.length)
        (gs[k].inputs.map fun i => (elimState m gs acc k).1.getD i (Sum.inl false))).1 with
    | none =>
      simp only [Option.toList_none, List.length_nil, Option.isNone_none, ↓reduceIte,
        Finset.card_insert_of_notMem hnot]
      omega
    | some g =>
      simp only [Option.toList_some, List.length_singleton, Option.isNone_some, Bool.false_eq_true,
        ↓reduceIte]
      omega

lemma mem_elimDropped_of_const (m : ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) (hj : j < gs.length)
    (hnok : NOkGate gs[j]) (i : ℕ) (hi : i ∈ gs[j].inputs)
    (hc : ∃ c, (elimState m gs acc j).1.getD i (Sum.inl false) = Sum.inl c) :
    j ∈ elimDropped m gs acc := by
  rw [elimDropped, Finset.mem_filter, Finset.mem_range]
  refine ⟨hj, ?_⟩
  simp only [hj, ↓reduceDIte]
  obtain ⟨c, hc⟩ := hc
  have hnone : (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
      (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1 = none := by
    apply simplifyGate_none_of_const
    · exact hnok.1.1
    · simpa using hnok.1.2
    · intro h; simpa using hnok.2 h
    · exact ⟨c, List.mem_map.2 ⟨i, hi, hc⟩⟩
  rw [hnone]
  rfl

lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  obtain ⟨g, hg, hkg⟩ := hex
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hmem : j ∈ elimDropped m gs acc := by
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkg
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcard : 1 ≤ (elimDropped m gs acc).card := Finset.one_le_card.2 ⟨j, hmem⟩
  have htot := elimPass_card_dropped m gs acc
  omega

lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  have hsub : (Finset.range gs.length).filter (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)
      ⊆ elimDropped m gs acc := by
    intro j hj'
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    obtain ⟨hj, hkin⟩ := hj'
    simp only [hj, ↓reduceDIte] at hkin
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkin
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcnt : ((Finset.range gs.length).filter
      (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card =
      (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
    clear hsub htwo hc hk hok acc m
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.filter_cons]
      have hbij : ((Finset.range (g :: gs).length).filter
          (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false)).card =
          (if k ∈ g.inputs then 1 else 0) +
          ((Finset.range gs.length).filter
            (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card := by
        have hsplit : (Finset.range (g :: gs).length).filter
            (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false) =
            (if k ∈ g.inputs then {0} else ∅) ∪
            ((Finset.range gs.length).filter
              (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).image (· + 1) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
            List.length_cons]
          cases j with
          | zero =>
            by_cases hk0 : k ∈ g.inputs <;> simp [hk0]
          | succ j =>
            by_cases hk0 : k ∈ g.inputs <;> by_cases hlt : j < gs.length <;> simp [hk0, hlt]
        rw [hsplit, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (fun _ _ h => by omega)]
          split_ifs <;> simp
        · rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_image] at hx2
          obtain ⟨y, _, rfl⟩ := hx2
          split_ifs at hx1 <;> simp at hx1
      rw [hbij, ih]
      by_cases hkg : k ∈ g.inputs <;> simp [hkg] <;> omega
  have hle := Finset.card_le_card hsub
  have htot := elimPass_card_dropped m gs acc
  omega

def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

lemma wiresFrom_agree (gs : List Gate) (B : Set ℕ) (w₁ w₂ : List Bool)
    (hlen : w₁.length = w₂.length) (hB : ∀ b ∈ B, b < w₁.length)
    (hagree : ∀ i ∉ B, w₁.getD i false = w₂.getD i false)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ B) :
    (wiresFrom gs w₁).length = (wiresFrom gs w₂).length ∧
    ∀ i ∉ B, (wiresFrom gs w₁).getD i false = (wiresFrom gs w₂).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact ⟨hlen, hagree⟩
  | cons g gs ih =>
    rw [wiresFrom_cons, wiresFrom_cons]
    have hmap : (g.inputs.map fun i => w₁.getD i false) =
        (g.inputs.map fun i => w₂.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact hagree i (hread g List.mem_cons_self i hi)
    rw [hmap]
    apply ih
    · simp [hlen]
    · intro b hb; simp; have := hB b hb; omega
    · intro i hi
      by_cases hlt : i < w₁.length
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree i hi
      · by_cases heq : i = w₁.length
        · rw [getD_snoc_eq _ _ _ _ heq, getD_snoc_eq _ _ _ _ (by omega)]
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)]
    · intro g' hg'
      exact hread g' (List.mem_cons_of_mem _ hg')

lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

def initVar (m : ℕ) (v : Fin m) (b : Bool) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin m => if i = v then Sum.inl b else Sum.inr (i : ℕ)

lemma elimInv_initVar (m : ℕ) (v : Fin m) (b : Bool) (x : Fin m → Bool) :
    ElimInv m (List.ofFn x) (List.ofFn (Function.update x v b)) (initVar m v b, []) := by
  refine ⟨by simp, by simp [initVar], ?_⟩
  intro i
  by_cases hi : i < m
  · have hget : (initVar m v b).getD i (Sum.inl false) =
        if (⟨i, hi⟩ : Fin m) = v then Sum.inl b else Sum.inr i := by
      rw [initVar, ofFn_getD_lt _ _ _ hi]
    rw [hget]
    by_cases heq : (⟨i, hi⟩ : Fin m) = v
    · simp only [heq, ↓reduceIte, statValid, statVal]
      rw [ofFn_getD_lt _ _ _ hi, heq, Function.update_self]
      exact ⟨trivial, rfl⟩
    · simp only [heq, ↓reduceIte, statValid, statVal, wiresFrom_nil]
      refine ⟨by omega, ?_⟩
      rw [ofFn_getD_lt _ _ _ hi, ofFn_getD_lt _ _ _ hi, Function.update_of_ne heq]
  · rw [List.getD_eq_default _ _ (by simp [initVar]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma elim_one_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m) (b : Bool)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc : ∃ x x' : Fin m → Bool, F (Function.update x v b) ≠ F (Function.update x' v b)) :
    1 ≤ s ∧ HasCircuitSize m (fun x => F (Function.update x v b)) (s - 1) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc
    have h1 := hev (Function.update x v b)
    have h2 := hev (Function.update x' v b)
    have hw1 : (C.wires (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v b))).getD (v : ℕ) false = b
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v b) = b := by
      rw [← h1]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw1
    have e2 : F (Function.update x' v b) = b := by
      rw [← h2]; show (C.wires _).getD C.output false = b; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  have hex : ∃ g ∈ gs, (v : ℕ) ∈ g.inputs := by
    by_contra hno
    have hno' : ∀ g ∈ gs, (v : ℕ) ∉ g.inputs := fun g hg hv => hno ⟨g, hg, hv⟩
    obtain ⟨x, hne⟩ := hdep
    have hag := wiresFrom_agree gs {(v : ℕ)}
      (List.ofFn (Function.update x v false))
      (List.ofFn (Function.update x v true))
      (by simp)
      (by intro u hu; simp at hu; subst hu; simp)
      (by
        intro i hi
        simp at hi
        by_cases hlt : i < m
        · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
            intro h; apply hi; exact congrArg Fin.val h
          rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
              Function.update_of_ne hne', Function.update_of_ne hne']
        · rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp; omega)])
      (by
        intro g hg i hi hmem
        simp at hmem
        subst hmem
        exact hno' g hg hi)
    have hco : C.output ∉ ({(v : ℕ)} : Set ℕ) := by simpa using hout_ne
    have hEq := hag.2 C.output hco
    rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
    exact hne ((hev _).symm.trans (hEq.trans (hev _)))
  set acc := elimPass m gs (initVar m v b, []) with hacc
  have hlen : acc.2.length + 1 ≤ gs.length := by
    have := elimPass_len_lt m (v : ℕ) gs (initVar m v b, []) hnok
      (by simp [initVar])
      ⟨b, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
      hex
    rw [← hacc] at this
    simpa using this
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        F (Function.update x v b) := by
    intro x
    have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
      (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
    rw [← hacc] at hinv
    rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
    exact hev (Function.update x v b)
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr j =>
    refine ⟨by omega, ⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩
    · show acc.2.length ≤ s - 1
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

lemma list_split_unique_filter {α : Type*} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 1) :
    ∃ l₁ a l₂, l = l₁ ++ [a] ++ l₂ ∧ p a = true ∧
      (∀ x ∈ l₁, p x = false) ∧ (∀ x ∈ l₂, p x = false) := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    cases hpx : p x with
    | true =>
      have h0 : (xs.filter p).length = 0 := by
        simp only [List.filter_cons, hpx, ↓reduceIte, List.length_cons] at h
        omega
      have hnil : xs.filter p = [] := List.eq_nil_of_length_eq_zero h0
      refine ⟨[], x, xs, rfl, hpx, by simp, ?_⟩
      intro y hy
      by_contra hpy
      have hpyt : p y = true := by cases hp : p y <;> simp_all
      have : y ∈ xs.filter p := List.mem_filter.2 ⟨hy, hpyt⟩
      rw [hnil] at this
      simp at this
    | false =>
      have h1 : (xs.filter p).length = 1 := by
        simpa [hpx] using h
      obtain ⟨l₁, a, l₂, rfl, hpa, hl₁, hl₂⟩ := ih h1
      refine ⟨x :: l₁, a, l₂, by simp, hpa, ?_, hl₂⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact hpx
      · exact hl₁ y hy'

lemma elim_two_var {m s : ℕ} {F : (Fin m → Bool) → Bool} (v : Fin m)
    (hC : HasCircuitSize m F s)
    (hdep : ∃ x : Fin m → Bool, F (Function.update x v false) ≠ F (Function.update x v true))
    (hnc0 : ∃ x x' : Fin m → Bool,
      F (Function.update x v false) ≠ F (Function.update x' v false))
    (hnc1 : ∃ x x' : Fin m → Bool,
      F (Function.update x v true) ≠ F (Function.update x' v true)) :
    2 ≤ s ∧ (HasCircuitSize m (fun x => F (Function.update x v false)) (s - 2) ∨
      HasCircuitSize m (fun x => F (Function.update x v true)) (s - 2)) := by
  obtain ⟨C, hok, hsz, hev⟩ := hC
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hok g0 hg0)
  have hgs_len : gs.length = C.gates.length := by simp [hgs]
  have hsz' : C.gates.length ≤ s := hsz
  have hout_ne : C.output ≠ (v : ℕ) := by
    intro heq
    obtain ⟨x, x', hne⟩ := hnc0
    have h1 := hev (Function.update x v false)
    have h2 := hev (Function.update x' v false)
    have hw1 : (C.wires (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have hw2 : (C.wires (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false := by
      show (wiresFrom C.gates (List.ofFn (Function.update x' v false))).getD (v : ℕ) false = false
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ v.isLt]
      simp
    have e1 : F (Function.update x v false) = false := by
      rw [← h1]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw1
    have e2 : F (Function.update x' v false) = false := by
      rw [← h2]; show (C.wires _).getD C.output false = false; rw [heq]; exact hw2
    exact hne (e1.trans e2.symm)
  set cnt := (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length with hcnt
  by_cases hge2 : 2 ≤ cnt
  · set acc := elimPass m gs (initVar m v false, []) with hacc
    have hlen : acc.2.length + 2 ≤ gs.length := by
      have := elimPass_len_two m (v : ℕ) gs (initVar m v false, []) hnok
        (by simp [initVar])
        ⟨false, by rw [initVar, ofFn_getD_lt _ _ _ v.isLt]; simp⟩
        (by rw [← hcnt]; exact hge2)
      rw [← hacc] at this
      simpa using this
    have hval : ∀ x : Fin m → Bool,
        statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
          F (Function.update x v false) := by
      intro x
      have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v false, [])
        (fun g hg => (hnok g hg).1) (elimInv_initVar m v false x)
      rw [← hacc] at hinv
      rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
      exact hev (Function.update x v false)
    cases hst : acc.1.getD C.output (Sum.inl false) with
    | inl c =>
      obtain ⟨x, x', hne⟩ := hnc0
      have hx := hval x; have hx' := hval x'
      rw [hst] at hx hx'
      exact absurd (hx.symm.trans hx') hne
    | inr j =>
      refine ⟨by omega, Or.inl ⟨⟨acc.2, j⟩, elimPass_ok m gs _ (by simp), ?_, ?_⟩⟩
      · show acc.2.length ≤ s - 2; omega
      · intro x; have := hval x; rw [hst] at this; exact this
  · by_cases hzero : cnt = 0
    · exfalso
      have hnil : gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) = [] :=
        List.eq_nil_of_length_eq_zero (by rw [← hcnt]; exact hzero)
      obtain ⟨x, hne⟩ := hdep
      have hag := wiresFrom_agree gs {(v : ℕ)}
        (List.ofFn (Function.update x v false))
        (List.ofFn (Function.update x v true))
        (by simp)
        (by intro u hu; simp at hu; subst hu; simp)
        (by
          intro i hi; simp at hi
          by_cases hlt : i < m
          · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
              intro h; apply hi; exact congrArg Fin.val h
            rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                Function.update_of_ne hne', Function.update_of_ne hne']
          · rw [List.getD_eq_default _ _ (by simp; omega),
                List.getD_eq_default _ _ (by simp; omega)])
        (by
          intro g hg i hi hmem
          simp at hmem; subst hmem
          have : g ∈ gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs)) :=
            List.mem_filter.2 ⟨hg, decide_eq_true hi⟩
          rw [hnil] at this; simp at this)
      have hEq := hag.2 C.output (by simpa using hout_ne)
      rw [hgs, wiresFrom_norm, wiresFrom_norm] at hEq
      exact hne ((hev _).symm.trans (hEq.trans (hev _)))
    · have hone : (gs.filter (fun g => decide ((v : ℕ) ∈ g.inputs))).length = 1 := by
        rw [← hcnt]; omega
      have hsp := list_split_unique_filter (fun g => decide ((v : ℕ) ∈ g.inputs)) gs hone
      rcases hsp with ⟨gs₁, g₁, gs₂, hsplit, hg₁in, hgs₁no, hgs₂no⟩
      have hv_in : (v : ℕ) ∈ g₁.inputs := of_decide_eq_true hg₁in
      have hnok₁ : NOkGate g₁ := hnok g₁ (by rw [hsplit]; simp)
      set b : Bool := match g₁.op with | GateOp.or => true | _ => false with hb
      have hncb : ∃ x x' : Fin m → Bool,
          F (Function.update x v b) ≠ F (Function.update x' v b) := by
        cases hbc : b with
        | false => exact hnc0
        | true => exact hnc1
      set acc₁ := elimPass m gs₁ (initVar m v b, []) with hacc₁
      set accM := elimStep m acc₁ g₁ with haccM
      set acc := elimPass m gs₂ accM with hacc
      have hacc_eq : acc = elimPass m gs (initVar m v b, []) := by
        rw [hsplit, elimPass_append, elimPass_append, ← hacc₁, elimPass_cons, elimPass_nil, ← haccM]
      have hacc₁_len : acc₁.1.length = m + gs₁.length := by
        rw [hacc₁, elimPass_fst_len]; simp [initVar]
      have hacc₁_v : acc₁.1.getD (v : ℕ) (Sum.inl false) = Sum.inl b := by
        rw [hacc₁, elimPass_getD_lt _ _ _ _ _ (by simp [initVar])]
        rw [initVar, ofFn_getD_lt _ _ _ v.isLt]
        simp
      have hmid_props : accM.2.length = acc₁.2.length ∧
          ∃ c : Bool, accM.1.getD (m + gs₁.length) (Sum.inl false) = Sum.inl c := by
        have hmem : Sum.inl b ∈ (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) :=
          List.mem_map.2 ⟨(v : ℕ), hv_in, hacc₁_v⟩
        have hres : ∃ c : Bool,
            simplifyGate g₁.op (m + acc₁.2.length)
              (g₁.inputs.map fun i => acc₁.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
          rcases hnok₁.1.1 with hop | hop | hop
          · have : g₁.op = GateOp.and := hop
            have hbf : b = false := by simp [hb, this]
            rw [this]
            rw [hbf] at hmem
            exact ⟨false, simplifyGate_and_false _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.or := hop
            have hbt : b = true := by simp [hb, this]
            rw [this]
            rw [hbt] at hmem
            exact ⟨true, simplifyGate_or_true _ _ (by simp; exact hnok₁.1.2) hmem⟩
          · have : g₁.op = GateOp.not := hop
            have hbf : b = false := by simp [hb, this]
            have hlen1 : g₁.inputs.length ≤ 1 := hnok₁.2 this
            have hsing : g₁.inputs = [(v : ℕ)] := by
              rcases hgi : g₁.inputs with _ | ⟨a, _ | ⟨d, l⟩⟩
              · rw [hgi] at hv_in; simp at hv_in
              · rw [hgi] at hv_in; simp at hv_in; subst hv_in; rfl
              · rw [hgi] at hlen1; simp at hlen1
            rw [this, hsing, List.map_singleton, hacc₁_v, hbf]
            exact ⟨true, simplifyGate_not_const _ false⟩
        obtain ⟨c, hc⟩ := hres
        refine ⟨by simp only [haccM, elimStep, hc, Option.toList_none, List.append_nil], c, ?_⟩
        simp only [haccM, elimStep, hc]
        exact getD_snoc_eq _ _ _ _ hacc₁_len.symm
      have hval : ∀ x : Fin m → Bool,
          statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
            F (Function.update x v b) := by
        intro x
        have hinv := elimInv_pass m (List.ofFn x) gs _ (initVar m v b, [])
          (fun g hg => (hnok g hg).1) (elimInv_initVar m v b x)
        rw [← hacc_eq] at hinv
        rw [(hinv.2.2 C.output).2, hgs, wiresFrom_norm]
        exact hev (Function.update x v b)
      have hout_ne_w1 : C.output ≠ m + gs₁.length := by
        intro heq
        obtain ⟨c, hc⟩ := hmid_props.2
        have hacc_w1 : acc.1.getD C.output (Sum.inl false) = Sum.inl c := by
          rw [heq, hacc, elimPass_getD_lt _ _ _ _ _ (by simp [haccM, elimStep, hacc₁_len])]
          exact hc
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hacc_w1] at hx hx'
        exact hne (hx.symm.trans hx')
      have hex₂ : ∃ g ∈ gs₂, m + gs₁.length ∈ g.inputs := by
        by_contra hno
        have hno' : ∀ g ∈ gs₂, m + gs₁.length ∉ g.inputs := fun g hg hw => hno ⟨g, hg, hw⟩
        obtain ⟨x, hne⟩ := hdep
        have hag₁ := wiresFrom_agree gs₁ {(v : ℕ)}
          (List.ofFn (Function.update x v false))
          (List.ofFn (Function.update x v true))
          (by simp)
          (by intro u hu; simp at hu; subst hu; simp)
          (by
            intro i hi; simp at hi
            by_cases hlt : i < m
            · have hne' : (⟨i, hlt⟩ : Fin m) ≠ v := by
                intro h; apply hi; exact congrArg Fin.val h
              rw [ofFn_getD_lt _ _ _ hlt, ofFn_getD_lt _ _ _ hlt,
                  Function.update_of_ne hne', Function.update_of_ne hne']
            · rw [List.getD_eq_default _ _ (by simp; omega),
                  List.getD_eq_default _ _ (by simp; omega)])
          (by
            intro g hg i hi hmem
            simp at hmem; subst hmem
            have := hgs₁no g hg
            simp [hi] at this)
        set w0 := wiresFrom gs₁ (List.ofFn (Function.update x v false))
        set w1 := wiresFrom gs₁ (List.ofFn (Function.update x v true))
        have hw0_len : w0.length = m + gs₁.length := by simp [w0, wiresFrom_length]
        have hw1_len : w1.length = m + gs₁.length := by simp [w1, wiresFrom_length]
        have hag₂ := wiresFrom_agree gs₂ {(v : ℕ), m + gs₁.length}
          (wiresFrom [g₁] w0) (wiresFrom [g₁] w1)
          (by simp [wiresFrom_length, hw0_len, hw1_len])
          (by
            intro u hu
            rcases hu with rfl | rfl
            · simp [wiresFrom_length, hw0_len]; omega
            · simp [wiresFrom_length, hw0_len])
          (by
            intro i hi
            have hiv : i ≠ (v : ℕ) := fun h => hi (Or.inl h)
            have hiw : i ≠ m + gs₁.length := fun h => hi (Or.inr h)
            simp only [wiresFrom_cons, wiresFrom_nil]
            rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
            exact hag₁.2 i (by simpa using hiv))
          (by
            intro g hg i hi hmem
            rcases hmem with rfl | rfl
            · have := hgs₂no g hg; simp [hi] at this
            · exact hno' g hg hi)
        have hco : C.output ∉ ({(v : ℕ), m + gs₁.length} : Set ℕ) := by
          intro h; rcases h with h | h
          · exact hout_ne h
          · exact hout_ne_w1 h
        have hEq := hag₂.2 C.output hco
        have hrew0 : wiresFrom gs₂ (wiresFrom [g₁] w0) =
            wiresFrom gs (List.ofFn (Function.update x v false)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        have hrew1 : wiresFrom gs₂ (wiresFrom [g₁] w1) =
            wiresFrom gs (List.ofFn (Function.update x v true)) := by
          rw [hsplit, wiresFrom_append, wiresFrom_append]
        rw [hrew0, hrew1, hgs, wiresFrom_norm, wiresFrom_norm] at hEq
        exact hne ((hev _).symm.trans (hEq.trans (hev _)))
      have hlen₂ := elimPass_len_lt m (m + gs₁.length) gs₂ accM
        (fun g hg => hnok g (by rw [hsplit]; simp [hg]))
        (by simp [haccM, elimStep, hacc₁_len])
        hmid_props.2
        hex₂
      rw [← hacc] at hlen₂
      have hlen₁ : acc₁.2.length ≤ gs₁.length := by
        have := elimPass_len m gs₁ (initVar m v b, [])
        rw [← hacc₁] at this; simpa using this
      have hsplit_len : gs.length = gs₁.length + 1 + gs₂.length := by
        rw [hsplit]; simp; omega
      have htot : acc.2.length + 2 ≤ gs.length := by omega
      cases hst : acc.1.getD C.output (Sum.inl false) with
      | inl c =>
        obtain ⟨x, x', hne⟩ := hncb
        have hx := hval x; have hx' := hval x'
        rw [hst] at hx hx'
        exact absurd (hx.symm.trans hx') hne
      | inr j =>
        have hres : HasCircuitSize m (fun x => F (Function.update x v b)) (s - 2) := by
          refine ⟨⟨acc.2, j⟩, ?_, ?_, ?_⟩
          · rw [hacc_eq]; exact elimPass_ok m gs _ (by simp)
          · show acc.2.length ≤ s - 2; omega
          · intro x; have := hval x; rw [hst] at this; exact this
        refine ⟨by omega, ?_⟩
        cases hbc : b with
        | false => rw [hbc] at hres; exact Or.inl hres
        | true => rw [hbc] at hres; exact Or.inr hres

lemma acyclic_leaf_cases {n : ℕ} (G : SimpleGraph (Fin n)) (hAcyc : G.IsAcyclic)
    (hEdge : ∃ u v : Fin n, G.Adj u v) :
    ∃ ℓ p : Fin n, G.Adj ℓ p ∧ (∀ w, G.Adj ℓ w → w = p) ∧
      ((∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj ℓ' p ∧ ∀ w, G.Adj ℓ' w → w = p) ∨
       (∀ w, G.Adj p w → w = ℓ) ∨
       (∃ q : Fin n, q ≠ ℓ ∧ G.Adj p q ∧ ∀ w, G.Adj p w → w = ℓ ∨ w = q)) := by
  classical
  have hlen_lt : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length < n := by
    intro u v P hP
    have h1 : P.support.length ≤ Fintype.card (Fin n) := hP.support_nodup.length_le_card
    rw [P.length_support, Fintype.card_fin] at h1
    omega
  set S : Finset ℕ := (Finset.range n).filter
    (fun k => ∃ u v : Fin n, ∃ P : G.Walk u v, P.IsPath ∧ P.length = k) with hS
  have hS_ne : S.Nonempty := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    refine ⟨1, Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, u₀, v₀,
      SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, ?_, rfl⟩⟩
    · have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
        SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
      exact hlen_lt _ hp
    · exact SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
  set m := S.max' hS_ne with hm
  have hm_mem : m ∈ S := Finset.max'_mem S hS_ne
  have hm_ge : 1 ≤ m := by
    obtain ⟨u₀, v₀, hadj⟩ := hEdge
    have hp : (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil).IsPath :=
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj.ne])
    have h1 : 1 ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt _ hp), u₀, v₀, _, hp, rfl⟩
    exact Finset.le_max' S 1 h1
  have hm_max : ∀ {u v : Fin n} (P : G.Walk u v), P.IsPath → P.length ≤ m := by
    intro u v P hP
    have hmem : P.length ∈ S := Finset.mem_filter.2
      ⟨Finset.mem_range.2 (hlen_lt P hP), u, v, P, hP, rfl⟩
    exact Finset.le_max' S P.length hmem
  obtain ⟨_, ℓ, z, P, hP, hPlen⟩ := Finset.mem_filter.1 hm_mem
  cases P with
  | nil => simp at hPlen; omega
  | @cons _ p _ hlp Q =>
    have hQ : Q.IsPath := hP.of_cons
    have hℓ_not_Q : ℓ ∉ Q.support := by
      have hnd := hP.support_nodup
      simp only [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
      exact hnd.1
    have hℓ_leaf : ∀ w, G.Adj ℓ w → w = p := by
      intro w hlw
      by_cases hw : w ∈ (SimpleGraph.Walk.cons hlp Q).support
      · simpa using hAcyc.eq_snd_of_adj_start hP hlw hw
      · exfalso
        have hP' : (SimpleGraph.Walk.cons hlw.symm (SimpleGraph.Walk.cons hlp Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP hw
        have hle := hm_max _ hP'
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    have hnotQ_leaf : ∀ w, G.Adj p w → w ∉ Q.support → ∀ u, G.Adj w u → u = p := by
      intro w hpw hwQ u hwu
      by_contra hup
      by_cases huQ : u ∈ Q.support
      · set Q' := Q.takeUntil u huQ
        have hQ' : Q'.IsPath := hQ.takeUntil huQ
        have hR : (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).IsPath := by
          refine SimpleGraph.Walk.IsPath.cons
            (SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hwu.ne])) ?_
          simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
            List.not_mem_nil, or_false, not_or]
          exact ⟨hpw.ne, Ne.symm hup⟩
        have heq := (hAcyc.subsingleton_path p u).elim ⟨Q', hQ'⟩ ⟨_, hR⟩
        have hw_in_R : w ∈ (SimpleGraph.Walk.cons hpw (SimpleGraph.Walk.cons hwu SimpleGraph.Walk.nil)).support := by
          simp
        have hw_in_Q' : w ∈ Q'.support := by
          rw [Subtype.mk.inj heq]; exact hw_in_R
        exact hwQ (SimpleGraph.Walk.support_takeUntil_subset_support Q huQ hw_in_Q')
      · have hP1 : (SimpleGraph.Walk.cons hpw.symm Q).IsPath :=
          SimpleGraph.Walk.IsPath.cons hQ hwQ
        have hu_not : u ∉ (SimpleGraph.Walk.cons hpw.symm Q).support := by
          simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
          exact ⟨hwu.ne.symm, huQ⟩
        have hP2 : (SimpleGraph.Walk.cons hwu.symm (SimpleGraph.Walk.cons hpw.symm Q)).IsPath :=
          SimpleGraph.Walk.IsPath.cons hP1 hu_not
        have hle := hm_max _ hP2
        simp only [SimpleGraph.Walk.length_cons] at hPlen hle
        omega
    refine ⟨ℓ, p, hlp, hℓ_leaf, ?_⟩
    cases Q with
    | nil =>
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ G.Adj z ℓ'
      · obtain ⟨ℓ', hne, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.nil : G.Walk z z).support := by
          simp [hadj.ne.symm]
        exact Or.inl ⟨ℓ', hne, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inl ?_)
        intro w hpw
        by_contra hwne
        exact hother ⟨w, hwne, hpw⟩
    | @cons _ q _ hpq Q' =>
      have hq_ne_ℓ : q ≠ ℓ := by
        intro hq
        apply hℓ_not_Q
        rw [← hq]
        simp
      by_cases hother : ∃ ℓ' : Fin n, ℓ' ≠ ℓ ∧ ℓ' ≠ q ∧ G.Adj p ℓ'
      · obtain ⟨ℓ', hne1, hne2, hadj⟩ := hother
        have hnot : ℓ' ∉ (SimpleGraph.Walk.cons hpq Q').support := by
          intro hmem
          exact hne2 (by simpa using hAcyc.eq_snd_of_adj_start hQ hadj hmem)
        exact Or.inl ⟨ℓ', hne1, hadj.symm, hnotQ_leaf ℓ' hadj hnot⟩
      · refine Or.inr (Or.inr ⟨q, hq_ne_ℓ, hpq, ?_⟩)
        intro w hpw
        by_contra hnot
        exact hother ⟨w, fun h => hnot (Or.inl h), fun h => hnot (Or.inr h), hpw⟩

def IsVC {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  ∀ u v : Fin n, G.Adj u v → u ∈ S ∨ v ∈ S

def HasMinVC {n : ℕ} (G : SimpleGraph (Fin n)) (t : ℕ) : Prop :=
  (∃ S : Finset (Fin n), IsVC G S ∧ S.card = t) ∧
  (∀ S : Finset (Fin n), IsVC G S → t ≤ S.card)

lemma hasMinVC_exists {n : ℕ} (G : SimpleGraph (Fin n)) : ∃ t : ℕ, HasMinVC G t := by
  classical
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n), IsVC G S ∧ S.card = k :=
    ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  intro S hS
  exact Nat.find_min' hex ⟨S, hS, rfl⟩

lemma hasMinVC_empty {n t : ℕ} (G : SimpleGraph (Fin n))
    (hempty : ∀ u v : Fin n, ¬ G.Adj u v) (hvc : HasMinVC G t) : t = 0 := by
  have hle : t ≤ (∅ : Finset (Fin n)).card := hvc.2 ∅ (fun u v h => absurd h (hempty u v))
  simpa using hle

def deleteVertexEdges {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    SimpleGraph (Fin n) where
  Adj u v := G.Adj u v ∧ u ≠ p ∧ v ≠ p
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩

lemma deleteVertexEdges_le {n : ℕ} (G : SimpleGraph (Fin n)) (p : Fin n) :
    deleteVertexEdges G p ≤ G :=
  fun _ _ h => h.1

lemma hasMinVC_deleteEdge {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ ≤ t ∧ t ≤ t₁ + 1 := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, hmin₁⟩ := hvc₁
  constructor
  · have hS_sub : IsVC (G.deleteEdges {s(ℓ, p)}) S := fun u v h => hS u v h.1
    rw [← hSc]; exact hmin₁ S hS_sub
  · have hcov : IsVC G (insert p S₁) := by
      intro u v huv
      by_cases hmem : s(u, v) = s(ℓ, p)
      · rw [Sym2.eq_iff] at hmem
        rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S₁)
        · exact Or.inl (hup ▸ Finset.mem_insert_self p S₁)
      · have hadj : (G.deleteEdges {s(ℓ, p)}).Adj u v :=
          SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩
        rcases hS₁ u v hadj with hu | hv
        · exact Or.inl (Finset.mem_insert_of_mem hu)
        · exact Or.inr (Finset.mem_insert_of_mem hv)
    have hle := hmin (insert p S₁) hcov
    have hcard : (insert p S₁).card ≤ S₁.card + 1 := Finset.card_insert_le p S₁
    omega

lemma hasMinVC_deleteLeafEdge_eq {n t t₁ : ℕ} (G : SimpleGraph (Fin n)) (ℓ ℓ' p : Fin n)
    (hℓ'ne : ℓ' ≠ ℓ) (hℓ'p : G.Adj ℓ' p) (hℓ'leaf : ∀ w, G.Adj ℓ' w → w = p)
    (hvc : HasMinVC G t) (hvc₁ : HasMinVC (G.deleteEdges {s(ℓ, p)}) t₁) :
    t₁ = t := by
  have hle : t₁ ≤ t := (hasMinVC_deleteEdge G ℓ p hvc hvc₁).1
  obtain ⟨⟨S₁, hS₁, hS₁c⟩, _⟩ := hvc₁
  have hge : t ≤ t₁ := by
    by_cases hp : p ∈ S₁
    · have hcov : IsVC G S₁ := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
          · exact Or.inr (hvp ▸ hp)
          · exact Or.inl (hup ▸ hp)
        · exact hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩)
      rw [← hS₁c]; exact hvc.2 S₁ hcov
    · have hℓ'in : ℓ' ∈ S₁ := by
        have hne_edge : s(ℓ', p) ≠ s(ℓ, p) := by
          intro heq
          rw [Sym2.eq_iff] at heq
          rcases heq with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hℓ'ne h1
          · exact hℓ'p.ne h1
        have hadj : (G.deleteEdges {s(ℓ, p)}).Adj ℓ' p :=
          SimpleGraph.deleteEdges_adj.2 ⟨hℓ'p, by simpa using hne_edge⟩
        rcases hS₁ ℓ' p hadj with h | h
        · exact h
        · exact absurd h hp
      set S' := insert p (S₁.erase ℓ')
      have hcov : IsVC G S' := by
        intro u v huv
        by_cases hmem : s(u, v) = s(ℓ, p)
        · rw [Sym2.eq_iff] at hmem
          rcases hmem with ⟨_, hvp⟩ | ⟨hup, _⟩
          · exact Or.inr (hvp ▸ Finset.mem_insert_self p _)
          · exact Or.inl (hup ▸ Finset.mem_insert_self p _)
        · rcases hS₁ u v (SimpleGraph.deleteEdges_adj.2 ⟨huv, by simpa using hmem⟩) with hu | hv
          · by_cases huℓ : u = ℓ'
            · subst huℓ
              have hv_eq : v = p := hℓ'leaf v huv
              exact Or.inr (hv_eq ▸ Finset.mem_insert_self p _)
            · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨huℓ, hu⟩))
          · by_cases hvℓ : v = ℓ'
            · subst hvℓ
              have hu_eq : u = p := hℓ'leaf u huv.symm
              exact Or.inl (hu_eq ▸ Finset.mem_insert_self p _)
            · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hvℓ, hv⟩))
      have hcard : S'.card = S₁.card := by
        have hp_not : p ∉ S₁.erase ℓ' := fun h => hp (Finset.mem_of_mem_erase h)
        rw [Finset.card_insert_of_notMem hp_not, Finset.card_erase_of_mem hℓ'in]
        have hpos : 1 ≤ S₁.card := Finset.one_le_card.2 ⟨ℓ', hℓ'in⟩
        omega
      have := hvc.2 S' hcov
      omega
  omega

lemma hasMinVC_deleteVertex {n t t' : ℕ} (G : SimpleGraph (Fin n)) (ℓ p : Fin n)
    (hlp : G.Adj ℓ p) (hleaf : ∀ w, G.Adj ℓ w → w = p)
    (hvc : HasMinVC G t) (hvc' : HasMinVC (deleteVertexEdges G p) t') :
    t' + 1 = t := by
  obtain ⟨⟨S, hS, hSc⟩, hmin⟩ := hvc
  obtain ⟨⟨S', hS', hS'c⟩, hmin'⟩ := hvc'
  have hle : t ≤ t' + 1 := by
    have hcov : IsVC G (insert p S') := by
      intro u v huv
      by_cases hup : u = p
      · exact Or.inl (hup ▸ Finset.mem_insert_self p S')
      · by_cases hvp : v = p
        · exact Or.inr (hvp ▸ Finset.mem_insert_self p S')
        · rcases hS' u v ⟨huv, hup, hvp⟩ with hu | hv
          · exact Or.inl (Finset.mem_insert_of_mem hu)
          · exact Or.inr (Finset.mem_insert_of_mem hv)
    have := hmin (insert p S') hcov
    have := Finset.card_insert_le p S'
    omega
  have hge : t' + 1 ≤ t := by
    by_cases hp : p ∈ S
    · have hcov : IsVC (deleteVertexEdges G p) (S.erase p) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · exact Or.inl (Finset.mem_erase.2 ⟨huv.2.1, hu⟩)
        · exact Or.inr (Finset.mem_erase.2 ⟨huv.2.2, hv⟩)
      have h1 := hmin' (S.erase p) hcov
      have h2 := Finset.card_erase_of_mem hp
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨p, hp⟩
      omega
    · have hℓ : ℓ ∈ S := by
        rcases hS ℓ p hlp with h | h
        · exact h
        · exact absurd h hp
      have hcov : IsVC (deleteVertexEdges G p) (S.erase ℓ) := by
        intro u v huv
        rcases hS u v huv.1 with hu | hv
        · have huℓ : u ≠ ℓ := by
            intro h; subst h; exact huv.2.2 (hleaf v huv.1)
          exact Or.inl (Finset.mem_erase.2 ⟨huℓ, hu⟩)
        · have hvℓ : v ≠ ℓ := by
            intro h; subst h; exact huv.2.1 (hleaf u huv.1.symm)
          exact Or.inr (Finset.mem_erase.2 ⟨hvℓ, hv⟩)
      have h1 := hmin' (S.erase ℓ) hcov
      have h2 := Finset.card_erase_of_mem hℓ
      have hpos : 1 ≤ S.card := Finset.one_le_card.2 ⟨ℓ, hℓ⟩
      omega
  omega

lemma edgeFinset_card_deleteEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (ℓ p : Fin n) (hlp : G.Adj ℓ p) [DecidableRel (G.deleteEdges {s(ℓ, p)}).Adj] :
    (G.deleteEdges {s(ℓ, p)}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (G.deleteEdges {s(ℓ, p)}).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    simp only [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.edgeSet_deleteEdges,
      Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

lemma edgeFinset_card_deleteVertex_deg1 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p : Fin n) (hlp : G.Adj ℓ p)
    (hpdeg : ∀ w, G.Adj p w → w = ℓ) [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 1 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset = G.edgeFinset.erase s(ℓ, p) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, huv⟩
        intro he
        rw [Sym2.eq_iff] at he
        rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact hvp h2
        · exact hup h1
      · rintro ⟨hne, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          exact hne (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, hpdeg v huv⟩)
        · intro hvp; subst hvp
          exact hne (by rw [Sym2.eq_iff]; exact Or.inl ⟨hpdeg u huv.symm, rfl⟩)
  rw [heq]
  have hmem : s(ℓ, p) ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hpos : 1 ≤ G.edgeFinset.card := Finset.one_le_card.2 ⟨s(ℓ, p), hmem⟩
  rw [Finset.card_erase_of_mem hmem]
  omega

lemma edgeFinset_card_deleteVertex_deg2 {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (ℓ p q : Fin n) (hlp : G.Adj ℓ p) (hpq : G.Adj p q)
    (hqne : q ≠ ℓ) (hpdeg : ∀ w, G.Adj p w → w = ℓ ∨ w = q)
    [DecidableRel (deleteVertexEdges G p).Adj] :
    (deleteVertexEdges G p).edgeFinset.card + 2 = G.edgeFinset.card := by
  have heq : (deleteVertexEdges G p).edgeFinset =
      (G.edgeFinset.erase s(ℓ, p)).erase s(p, q) := by
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeFinset, Finset.mem_erase, Finset.mem_erase,
          SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.mem_edgeSet]
      dsimp only [deleteVertexEdges]
      constructor
      · rintro ⟨huv, hup, hvp⟩
        refine ⟨?_, ?_, huv⟩
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, _⟩ | ⟨_, h2⟩
          · exact hup h1
          · exact hvp h2
        · intro he; rw [Sym2.eq_iff] at he
          rcases he with ⟨_, h2⟩ | ⟨h1, _⟩
          · exact hvp h2
          · exact hup h1
      · rintro ⟨hne2, hne1, huv⟩
        refine ⟨huv, ?_, ?_⟩
        · intro hup; subst hup
          rcases hpdeg v huv with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
        · intro hvp; subst hvp
          rcases hpdeg u huv.symm with rfl | rfl
          · exact hne1 (by rw [Sym2.eq_iff]; exact Or.inl ⟨rfl, rfl⟩)
          · exact hne2 (by rw [Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩)
  rw [heq]
  have hmem1 : s(ℓ, p) ∈ G.edgeFinset := by rw [SimpleGraph.mem_edgeFinset]; exact hlp
  have hne_edges : s(p, q) ≠ s(ℓ, p) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hlp.ne h1.symm
    · exact hqne h2
  have hmem2 : s(p, q) ∈ G.edgeFinset.erase s(ℓ, p) :=
    Finset.mem_erase.2 ⟨hne_edges, by rw [SimpleGraph.mem_edgeFinset]; exact hpq⟩
  have hpos2 : 1 ≤ (G.edgeFinset.erase s(ℓ, p)).card := Finset.one_le_card.2 ⟨s(p, q), hmem2⟩
  rw [Finset.card_erase_of_mem hmem2, Finset.card_erase_of_mem hmem1]
  rw [Finset.card_erase_of_mem hmem1] at hpos2
  omega

def forestFun0 {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)

lemma forestFun0_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) :
    forestFun0 K A (fun _ => false) = false := by
  simp [forestFun0]

lemma forestFun0_true {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (hne : A.Nonempty ∨ ∃ u v : Fin n, K.Adj u v) :
    forestFun0 K A (fun _ => true) = true := by
  simp only [forestFun0, decide_eq_true_eq]
  rcases hne with ⟨a, ha⟩ | ⟨u, v, huv⟩
  · exact Or.inl ⟨a, ha, trivial⟩
  · exact Or.inr ⟨u, v, huv, trivial, trivial⟩

lemma forestFun0_update_A {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (a : Fin n) (ha_iso : ∀ v : Fin n, ¬ K.Adj a v) :
    (fun x : Fin n → Bool => forestFun0 K A (Function.update x a false)) =
      forestFun0 K (A.erase a) := by
  funext x
  simp only [forestFun0]
  apply decide_eq_decide.2
  constructor
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · by_cases hba : b = a
      · subst hba; simp at hxb
      · left; exact ⟨b, Finset.mem_erase.2 ⟨hba, hb⟩, by rwa [Function.update_of_ne hba] at hxb⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      rw [Function.update_of_ne hua] at hxu
      rw [Function.update_of_ne hva] at hxv
      exact ⟨u, v, huv, hxu, hxv⟩
  · rintro (⟨b, hb, hxb⟩ | ⟨u, v, huv, hxu, hxv⟩)
    · obtain ⟨hba, hbA⟩ := Finset.mem_erase.1 hb
      left; exact ⟨b, hbA, by rwa [Function.update_of_ne hba]⟩
    · right
      have hua : u ≠ a := fun h => ha_iso v (h ▸ huv)
      have hva : v ≠ a := fun h => ha_iso u (h ▸ huv.symm)
      exact ⟨u, v, huv, by rwa [Function.update_of_ne hua], by rwa [Function.update_of_ne hva]⟩

lemma forestFun0_update_leaf_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (ℓ p : Fin n) (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (K.deleteEdges {s(ℓ, p)}).Adj] :
    (fun x : Fin n → Bool => forestFun0 K ∅ (Function.update x ℓ false)) =
      forestFun0 (K.deleteEdges {s(ℓ, p)}) ∅ := by
  funext x
  simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    have hu : u ≠ ℓ := by intro h; subst h; simp at hxu
    have hv : v ≠ ℓ := by intro h; subst h; simp at hxv
    rw [Function.update_of_ne hu] at hxu
    rw [Function.update_of_ne hv] at hxv
    refine ⟨u, v, SimpleGraph.deleteEdges_adj.2 ⟨huv, ?_⟩, hxu, hxv⟩
    intro hmem
    simp only [Set.mem_singleton_iff, Sym2.eq_iff] at hmem
    rcases hmem with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact hu rfl
    · exact hv rfl
  · rintro ⟨u, v, hadj, hxu, hxv⟩
    obtain ⟨huv, hne⟩ := SimpleGraph.deleteEdges_adj.1 hadj
    have hu : u ≠ ℓ := by
      intro h; subst h
      have hp : v = p := hleaf v huv
      subst hp; exact hne rfl
    have hv : v ≠ ℓ := by
      intro h; subst h
      have hp : u = p := hleaf u huv.symm
      subst hp; exact hne Sym2.eq_swap
    exact ⟨u, v, huv, by rwa [Function.update_of_ne hu], by rwa [Function.update_of_ne hv]⟩

lemma forestFun0_update_leaf_true {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (ℓ p : Fin n) (hlp : K.Adj ℓ p) (hleaf : ∀ w, K.Adj ℓ w → w = p)
    [DecidableRel (deleteVertexEdges K p).Adj] :
    (fun x : Fin n → Bool => forestFun0 K ∅ (Function.update x ℓ true)) =
      forestFun0 (deleteVertexEdges K p) {p} := by
  funext x
  simp only [forestFun0, Finset.notMem_empty, false_and, exists_false, false_or,
    Finset.mem_singleton, exists_eq_left]
  apply decide_eq_decide.2
  constructor
  · rintro ⟨u, v, huv, hxu, hxv⟩
    by_cases hup : u = p
    · subst hup
      left
      rwa [Function.update_of_ne hlp.ne.symm] at hxu
    · by_cases hvp : v = p
      · subst hvp
        left
        rwa [Function.update_of_ne hlp.ne.symm] at hxv
      · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
        have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
        rw [Function.update_of_ne huℓ] at hxu
        rw [Function.update_of_ne hvℓ] at hxv
        exact Or.inr ⟨u, v, ⟨huv, hup, hvp⟩, hxu, hxv⟩
  · rintro (hxp | ⟨u, v, ⟨huv, hup, hvp⟩, hxu, hxv⟩)
    · exact ⟨ℓ, p, hlp, by simp, by rwa [Function.update_of_ne hlp.ne.symm]⟩
    · have huℓ : u ≠ ℓ := fun h => hvp (hleaf v (h ▸ huv))
      have hvℓ : v ≠ ℓ := fun h => hup (hleaf u (h ▸ huv.symm))
      exact ⟨u, v, huv, by rwa [Function.update_of_ne huℓ], by rwa [Function.update_of_ne hvℓ]⟩

end PEqualNP.Outside.L_meta_1031_aux.RelativeForestCore

namespace PEqualNP.Outside.L_meta_1031_aux.RelativeForestCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

structure ForestSandwich {n : ℕ} (H G : SimpleGraph (Fin n))
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    (A : Finset (Fin n)) (F : (Fin n → Bool) → Bool) : Prop where
  lower : ∀ x, forestFun0 H A x = true → F x = true
  upper : ∀ x, F x = true → forestFun0 G A x = true

theorem ForestSandwich.false_of_upper {n : ℕ} {H G : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] [DecidableRel G.Adj] {A : Finset (Fin n)}
    {F : (Fin n → Bool) → Bool} (h : ForestSandwich H G A F)
    (x : Fin n → Bool) (hx : forestFun0 G A x = false) : F x = false := by
  cases hf : F x with
  | false => rfl
  | true =>
      have ht := h.upper x hf
      rw [hx] at ht
      contradiction

theorem ForestSandwich.zero {n : ℕ} {H G : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] [DecidableRel G.Adj] {A : Finset (Fin n)}
    {F : (Fin n → Bool) → Bool} (h : ForestSandwich H G A F) :
    F (fun _ => false) = false :=
  h.false_of_upper _ (forestFun0_false G A)

theorem ForestSandwich.nonconstant {n : ℕ} {H G : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] [DecidableRel G.Adj] {A : Finset (Fin n)}
    {F : (Fin n → Bool) → Bool} (h : ForestSandwich H G A F)
    (hne : A.Nonempty ∨ ∃ u v, H.Adj u v) : ∃ x y, F x ≠ F y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  rw [h.zero, h.lower _ (forestFun0_true H A hne)]
  decide

theorem ForestSandwich.cofactor {n : ℕ} {H G H' G' : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] [DecidableRel G.Adj]
    [DecidableRel H'.Adj] [DecidableRel G'.Adj]
    {A A' : Finset (Fin n)} {F : (Fin n → Bool) → Bool}
    (h : ForestSandwich H G A F) (v : Fin n) (b : Bool)
    (hl : (fun x => forestFun0 H A (Function.update x v b)) = forestFun0 H' A')
    (hu : (fun x => forestFun0 G A (Function.update x v b)) = forestFun0 G' A') :
    ForestSandwich H' G' A' (fun x => F (Function.update x v b)) := by
  constructor
  · intro x hx
    exact h.lower _ ((congrFun hl x).symm ▸ hx)
  · intro x hx
    exact (congrFun hu x) ▸ h.upper _ hx

theorem forestFun0_singleton_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A : Finset (Fin n)) (v : Fin n) (hv : v ∉ A) :
    forestFun0 G A (fun i => decide (i = v)) = false := by
  simp only [forestFun0, decide_eq_false_iff_not]
  rintro (⟨a,ha,hav⟩ | ⟨a,b,hab,hav,hbv⟩)
  · have hav' : a = v := of_decide_eq_true hav
    exact hv (hav' ▸ ha)
  · have hav' : a = v := of_decide_eq_true hav
    have hbv' : b = v := of_decide_eq_true hbv
    subst a
    subst b
    exact G.loopless.irrefl v hab

theorem ForestSandwich.depends_linear {n : ℕ} {H G : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] [DecidableRel G.Adj] {A : Finset (Fin n)}
    {F : (Fin n → Bool) → Bool} (h : ForestSandwich H G A F)
    (a : Fin n) (ha : a ∈ A) :
    ∃ x, F (Function.update x a false) ≠ F (Function.update x a true) := by
  let x : Fin n → Bool := fun _ => false
  have h0 : Function.update x a false = x := by
    funext i
    by_cases hi : i = a <;> simp [x, hi]
  have hf0 : F (Function.update x a false) = false := by
    rw [h0]
    exact h.zero
  have hf1 : F (Function.update x a true) = true := h.lower _ (by
    simp only [forestFun0, decide_eq_true_eq]
    exact Or.inl ⟨a,ha,by simp⟩)
  exact ⟨x,by rw [hf0,hf1]; decide⟩

theorem ForestSandwich.depends_edge {n : ℕ} {H G : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] [DecidableRel G.Adj] {A : Finset (Fin n)}
    {F : (Fin n → Bool) → Bool} (h : ForestSandwich H G A F)
    (hHG : H ≤ G) (hA : ∀ a ∈ A, ∀ v, ¬ G.Adj a v)
    (ℓ p : Fin n) (hlp : H.Adj ℓ p) :
    ∃ x, F (Function.update x ℓ false) ≠ F (Function.update x ℓ true) := by
  let x : Fin n → Bool := fun i => decide (i = p)
  have hpA : p ∉ A := fun hp => hA p hp ℓ (hHG hlp).symm
  have h0 : Function.update x ℓ false = x := by
    funext i
    by_cases hi : i = ℓ
    · subst i
      simp [x,hlp.ne]
    · simp [hi]
  have hf0 : F (Function.update x ℓ false) = false := by
    rw [h0]
    exact h.false_of_upper x (forestFun0_singleton_false G A p hpA)
  have hf1 : F (Function.update x ℓ true) = true := h.lower _ (by
    simp only [forestFun0, decide_eq_true_eq]
    refine Or.inr ⟨ℓ,p,hlp,by simp,?_⟩
    simp [x,hlp.ne.symm])
  exact ⟨x,by rw [hf0,hf1]; decide⟩

theorem cofactor_size_le {n s : ℕ} {F : (Fin n → Bool) → Bool}
    (v : Fin n) (b : Bool) (hC : HasCircuitSize n F s)
    (hnc : ∃ x y, F (Function.update x v b) ≠ F (Function.update y v b)) :
    HasCircuitSize n (fun x => F (Function.update x v b)) s := by
  classical
  by_cases hdep : ∃ x, F (Function.update x v false) ≠ F (Function.update x v true)
  · obtain ⟨_,C,hfan,hsize,hfun⟩ := elim_one_var v b hC hdep hnc
    exact ⟨C,hfan,by omega,hfun⟩
  · have heq : (fun x => F (Function.update x v b)) = F := by
      funext x
      have hsame : F (Function.update x v false) = F (Function.update x v true) :=
        not_ne_iff.mp (fun h => hdep ⟨x,h⟩)
      have hx : Function.update x v (x v) = x := Function.update_eq_self v x
      have hmid : F (Function.update x v b) = F (Function.update x v (x v)) := by
        cases hb : b <;> cases hv : x v
        · rfl
        · exact hsame
        · exact hsame.symm
        · rfl
      exact hmid.trans (congrArg F hx)
    rwa [heq]

theorem forestFun0_update_deleteVertex {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (A : Finset (Fin n)) (v : Fin n) (hv : v ∉ A)
    [DecidableRel (deleteVertexEdges G v).Adj] :
    (fun x => forestFun0 G A (Function.update x v false)) =
      forestFun0 (deleteVertexEdges G v) A := by
  funext x
  simp only [forestFun0]
  apply decide_eq_decide.2
  constructor
  · rintro (⟨a,ha,hxa⟩ | ⟨a,b,hab,hxa,hxb⟩)
    · have hav : a ≠ v := fun he => hv (he ▸ ha)
      exact Or.inl ⟨a,ha,by rwa [Function.update_of_ne hav] at hxa⟩
    · have hav : a ≠ v := by intro he; subst a; simp at hxa
      have hbv : b ≠ v := by intro he; subst b; simp at hxb
      exact Or.inr ⟨a,b,⟨hab,hav,hbv⟩,
        by rwa [Function.update_of_ne hav] at hxa,
        by rwa [Function.update_of_ne hbv] at hxb⟩
  · rintro (⟨a,ha,hxa⟩ | ⟨a,b,⟨hab,hav,hbv⟩,hxa,hxb⟩)
    · have hav : a ≠ v := fun he => hv (he ▸ ha)
      exact Or.inl ⟨a,ha,by rwa [Function.update_of_ne hav]⟩
    · exact Or.inr ⟨a,b,hab,by rwa [Function.update_of_ne hav],
        by rwa [Function.update_of_ne hbv]⟩

theorem deleteVertex_edgecard_lt {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v w : Fin n) (hvw : G.Adj v w)
    [DecidableRel (deleteVertexEdges G v).Adj] :
    (deleteVertexEdges G v).edgeFinset.card < G.edgeFinset.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨SimpleGraph.edgeFinset_mono
    (deleteVertexEdges_le G v), ?_⟩
  intro heq
  have hm : s(v,w) ∈ (deleteVertexEdges G v).edgeFinset := by
    rw [heq]
    exact SimpleGraph.mem_edgeFinset.mpr hvw
  have hd := SimpleGraph.mem_edgeFinset.mp hm
  exact hd.2.1 rfl

theorem ForestSandwich.edge_size_pos {n s : ℕ} {H G : SimpleGraph (Fin n)}
    [DecidableRel H.Adj] [DecidableRel G.Adj] {F : (Fin n → Bool) → Bool}
    (h : ForestSandwich H G ∅ F) (hne : ∃ u v, H.Adj u v)
    (hC : HasCircuitSize n F s) : 1 ≤ s := by
  by_contra hs
  have hs0 : s = 0 := by omega
  subst s
  obtain ⟨C,hfan,hsize,hfun⟩ := hC
  have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero (by
    have hz : C.size = 0 := by omega
    simpa [Circuit.size] using hz)
  have heval : ∀ x, F x = (List.ofFn x).getD C.output false := by
    intro x
    rw [← hfun x]
    simp [Circuit.eval,Circuit.wires,hnil]
  by_cases ho : C.output < n
  · let v : Fin n := ⟨C.output,ho⟩
    let x : Fin n → Bool := fun i => decide (i = v)
    have ht : F x = true := by
      rw [heval,ofFn_getD_lt x false C.output ho]
      simp [x,v]
    have hf : F x = false := h.false_of_upper x
      (forestFun0_singleton_false G ∅ v (by simp))
    rw [ht] at hf
    contradiction
  · have hf : F (fun _ => true) = false := by
      rw [heval,List.getD_eq_default _ _ (by simp; omega)]
    have ht := h.lower _ (forestFun0_true H ∅ (Or.inr hne))
    rw [hf] at ht
    contradiction

end PEqualNP.Outside.L_meta_1031_aux.RelativeForestCore

namespace PEqualNP.Outside.L_meta_1031_aux.RelativeForestCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem relative_forest_sandwich_aux :
    ∀ (budget s : ℕ) {n t : ℕ}
      (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
      (A : Finset (Fin n)) (F : (Fin n → Bool) → Bool),
      s + G.edgeFinset.card = budget →
      G.IsAcyclic → H ≤ G →
      (∀ a ∈ A, ∀ v, ¬ G.Adj a v) →
      HasMinVC H t → ForestSandwich H G A F → HasCircuitSize n F s →
      A.card + H.edgeFinset.card + t ≤ s + 1 := by
  classical
  intro budget
  induction budget using Nat.strong_induction_on with
  | _ budget ih =>
    intro s n t G H _ _ A F hbudget hforest hHG hAiso hvc hSand hC
    by_cases hsmall : A.card + H.edgeFinset.card ≤ 1
    · by_cases hE0 : H.edgeFinset.card = 0
      · have hnoE : ∀ u v, ¬ H.Adj u v := by
          intro u v huv
          have hpos : 0 < H.edgeFinset.card := Finset.card_pos.mpr
            ⟨s(u,v),SimpleGraph.mem_edgeFinset.mpr huv⟩
          omega
        have ht0 := hasMinVC_empty H hnoE hvc
        omega
      · have hE1 : H.edgeFinset.card = 1 := by omega
        have hA0 : A = ∅ := Finset.card_eq_zero.mp (by omega)
        subst A
        obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0 < H.edgeFinset.card by omega)
        induction e using Sym2.ind with
        | _ u v =>
          have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp he
          have hcover : IsVC H {u} := by
            intro a b hab
            have heq : s(a,b) = s(u,v) := Finset.card_le_one.mp (by omega)
              s(a,b) (SimpleGraph.mem_edgeFinset.mpr hab) s(u,v) he
            rw [Sym2.eq_iff] at heq
            rcases heq with ⟨ha,hb⟩ | ⟨ha,hb⟩
            · exact Or.inl (by simpa [ha])
            · exact Or.inr (by simpa [hb])
          have ht : t ≤ 1 := by simpa using hvc.2 {u} hcover
          have hs := hSand.edge_size_pos ⟨u,v,huv⟩ hC
          simp only [Finset.card_empty,zero_add]
          omega
    · by_cases hAne : A.Nonempty
      · obtain ⟨a,ha⟩ := hAne
        have hAisoH : ∀ v, ¬ H.Adj a v := fun v hv => hAiso a ha v (hHG hv)
        have hSand' := hSand.cofactor a false
          (forestFun0_update_A H A a hAisoH)
          (forestFun0_update_A G A a (hAiso a ha))
        have hne' : (A.erase a).Nonempty ∨ ∃ u v, H.Adj u v := by
          by_cases hA2 : 2 ≤ A.card
          · left
            apply Finset.card_pos.mp
            rw [Finset.card_erase_of_mem ha]
            omega
          · right
            have hEpos : 0 < H.edgeFinset.card := by omega
            obtain ⟨e,he⟩ := Finset.card_pos.mp hEpos
            induction e using Sym2.ind with
            | _ u v => exact ⟨u,v,SimpleGraph.mem_edgeFinset.mp he⟩
        obtain ⟨hs1,hC'⟩ := elim_one_var a false hC
          (hSand.depends_linear a ha) (hSand'.nonconstant hne')
        have hih := ih (s - 1 + G.edgeFinset.card) (by omega)
          (s - 1) G H (A.erase a) (fun x => F (Function.update x a false))
          rfl hforest hHG
          (fun b hb v hv => hAiso b (Finset.mem_of_mem_erase hb) v hv)
          hvc hSand' hC'
        have hcard : (A.erase a).card + 1 = A.card := by
          have hpos := Finset.one_le_card.mpr ⟨a,ha⟩
          rw [Finset.card_erase_of_mem ha]
          omega
        omega
      · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAne
        subst A
        have hHedge : ∃ u v, H.Adj u v := by
          have hpos : 0 < H.edgeFinset.card := by
            simp only [Finset.card_empty,zero_add] at hsmall
            omega
          obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
          induction e using Sym2.ind with
          | _ u v => exact ⟨u,v,SimpleGraph.mem_edgeFinset.mp he⟩
        
        by_cases hprune : ∃ v, (∃ w, G.Adj v w) ∧ ∀ w, ¬ H.Adj v w
        · obtain ⟨v,⟨w,hvw⟩,hiso⟩ := hprune
          have hSand' : ForestSandwich H (deleteVertexEdges G v) ∅
              (fun x => F (Function.update x v false)) :=
            hSand.cofactor v false
              (by simpa using forestFun0_update_A H ∅ v hiso)
              (forestFun0_update_deleteVertex G ∅ v (by simp))
          have hC' := cofactor_size_le v false hC
            (hSand'.nonconstant (Or.inr hHedge))
          have hcardlt := deleteVertex_edgecard_lt G v w hvw
          have hHG' : H ≤ deleteVertexEdges G v := by
            intro a b hab
            refine ⟨hHG hab,?_,?_⟩
            · intro hav
              exact hiso b (hav ▸ hab)
            · intro hbv
              exact hiso a (hbv ▸ hab.symm)
          exact ih (s + (deleteVertexEdges G v).edgeFinset.card) (by omega)
            s (deleteVertexEdges G v) H ∅ (fun x => F (Function.update x v false))
            rfl (hforest.anti (deleteVertexEdges_le G v)) hHG' (by simp)
            hvc hSand' hC'
        · have leaf_critical : ∀ ℓ p, G.Adj ℓ p →
              (∀ w, G.Adj ℓ w → w = p) → H.Adj ℓ p := by
            intro ℓ p hlp hleaf
            by_contra hnot
            apply hprune
            refine ⟨ℓ,⟨p,hlp⟩,?_⟩
            intro w hw
            have heq := hleaf w (hHG hw)
            exact hnot (heq ▸ hw)
          obtain ⟨u,v,huv⟩ := hHedge
          obtain ⟨ℓ,p,hGlp,hGleaf,hcases⟩ :=
            acyclic_leaf_cases G hforest ⟨u,v,hHG huv⟩
          have hHlp : H.Adj ℓ p := leaf_critical ℓ p hGlp hGleaf
          have hHleaf : ∀ w, H.Adj ℓ w → w = p := fun w hw => hGleaf w (hHG hw)
          have hdep := hSand.depends_edge hHG (by simp) ℓ p hHlp
          have hSand0 := hSand.cofactor ℓ false
            (forestFun0_update_leaf_false H ℓ p hHleaf)
            (forestFun0_update_leaf_false G ℓ p hGleaf)
          have hSand1 := hSand.cofactor ℓ true
            (forestFun0_update_leaf_true H ℓ p hHlp hHleaf)
            (forestFun0_update_leaf_true G ℓ p hGlp hGleaf)
          have hGcard0 : (G.deleteEdges {s(ℓ,p)}).edgeFinset.card ≤ G.edgeFinset.card :=
            Finset.card_le_card (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _))
          have hGcard1 : (deleteVertexEdges G p).edgeFinset.card ≤ G.edgeFinset.card :=
            Finset.card_le_card (SimpleGraph.edgeFinset_mono (deleteVertexEdges_le G p))
          have hHG0 : H.deleteEdges {s(ℓ,p)} ≤ G.deleteEdges {s(ℓ,p)} := by
            intro a b hab
            exact ⟨hHG hab.1,hab.2⟩
          have hHG1 : deleteVertexEdges H p ≤ deleteVertexEdges G p := by
            intro a b hab
            exact ⟨hHG hab.1,hab.2⟩
          have hnc1 := hSand1.nonconstant (Or.inl (Finset.singleton_nonempty p))
          simp only [Finset.card_empty,zero_add]
          have false_step (k t' : ℕ) (hk : 1 ≤ k) (hks : k ≤ s)
              (hC0 : HasCircuitSize n (fun x => F (Function.update x ℓ false)) (s-k))
              (hvc' : HasMinVC (H.deleteEdges {s(ℓ,p)}) t')
              (hdebit : H.edgeFinset.card + t ≤
                (H.deleteEdges {s(ℓ,p)}).edgeFinset.card + t' + k) :
              H.edgeFinset.card + t ≤ s + 1 := by
            have hih := ih (s-k+(G.deleteEdges {s(ℓ,p)}).edgeFinset.card) (by omega)
              (s-k) (G.deleteEdges {s(ℓ,p)}) (H.deleteEdges {s(ℓ,p)}) ∅
              (fun x => F (Function.update x ℓ false)) rfl
              (hforest.anti (SimpleGraph.deleteEdges_le _)) hHG0 (by simp)
              hvc' hSand0 hC0
            simp only [Finset.card_empty,zero_add] at hih
            omega
          have true_step (k : ℕ) (hk : 1 ≤ k) (hks : k ≤ s)
              (hC1 : HasCircuitSize n (fun x => F (Function.update x ℓ true)) (s-k))
              (hdeg : (deleteVertexEdges H p).edgeFinset.card + k = H.edgeFinset.card) :
              H.edgeFinset.card + t ≤ s + 1 := by
            obtain ⟨t',hvc'⟩ := hasMinVC_exists (deleteVertexEdges H p)
            have ht := hasMinVC_deleteVertex H ℓ p hHlp hHleaf hvc hvc'
            have hih := ih (s-k+(deleteVertexEdges G p).edgeFinset.card) (by omega)
              (s-k) (deleteVertexEdges G p) (deleteVertexEdges H p) {p}
              (fun x => F (Function.update x ℓ true)) rfl
              (hforest.anti (deleteVertexEdges_le G p)) hHG1
              (by
                intro a ha v hv
                have hap : a = p := by simpa using ha
                subst a
                exact hv.2.1 rfl)
              hvc' hSand1 hC1
            simp only [Finset.card_singleton] at hih
            omega
          rcases hcases with ⟨ℓ',hℓ'ne,hGℓ'p,hGℓ'leaf⟩ | hGpdeg1 |
              ⟨q,hqne,hGpq,hGpdeg2⟩
          · have hHℓ'p : H.Adj ℓ' p := leaf_critical ℓ' p hGℓ'p hGℓ'leaf
            have hHℓ'leaf : ∀ w, H.Adj ℓ' w → w = p :=
              fun w hw => hGℓ'leaf w (hHG hw)
            have hne0 : (∅ : Finset (Fin n)).Nonempty ∨
                ∃ a b, (H.deleteEdges {s(ℓ,p)}).Adj a b := by
              right
              refine ⟨ℓ',p,SimpleGraph.deleteEdges_adj.mpr ⟨hHℓ'p,?_⟩⟩
              simp only [Set.mem_singleton_iff,Sym2.eq_iff]
              rintro (⟨h1,_⟩ | ⟨_,h2⟩)
              · exact hℓ'ne h1
              · exact hHlp.ne h2.symm
            obtain ⟨hs1,hC0⟩ := elim_one_var ℓ false hC hdep (hSand0.nonconstant hne0)
            obtain ⟨t',hvc'⟩ := hasMinVC_exists (H.deleteEdges {s(ℓ,p)})
            have ht := hasMinVC_deleteLeafEdge_eq H ℓ ℓ' p hℓ'ne hHℓ'p hHℓ'leaf hvc hvc'
            have he := edgeFinset_card_deleteEdge H ℓ p hHlp
            exact false_step 1 t' (by omega) hs1 hC0 hvc' (by omega)
          · have hHpdeg1 : ∀ w, H.Adj p w → w = ℓ := fun w hw => hGpdeg1 w (hHG hw)
            obtain ⟨hs1,hC1⟩ := elim_one_var ℓ true hC hdep hnc1
            exact true_step 1 (by omega) hs1 hC1
              (edgeFinset_card_deleteVertex_deg1 H ℓ p hHlp hHpdeg1)
          · by_cases hHpq : H.Adj p q
            · have hHpdeg2 : ∀ w, H.Adj p w → w = ℓ ∨ w = q :=
                fun w hw => hGpdeg2 w (hHG hw)
              have hne0 : (∅ : Finset (Fin n)).Nonempty ∨
                  ∃ a b, (H.deleteEdges {s(ℓ,p)}).Adj a b := by
                right
                refine ⟨p,q,SimpleGraph.deleteEdges_adj.mpr ⟨hHpq,?_⟩⟩
                simp only [Set.mem_singleton_iff,Sym2.eq_iff]
                rintro (⟨h1,_⟩ | ⟨_,h2⟩)
                · exact hHlp.ne h1.symm
                · exact hqne h2
              obtain ⟨hs2,hC0 | hC1⟩ := elim_two_var ℓ hC hdep
                (hSand0.nonconstant hne0) hnc1
              · obtain ⟨t',hvc'⟩ := hasMinVC_exists (H.deleteEdges {s(ℓ,p)})
                have ht := (hasMinVC_deleteEdge H ℓ p hvc hvc').2
                have he := edgeFinset_card_deleteEdge H ℓ p hHlp
                exact false_step 2 t' (by omega) hs2 hC0 hvc' (by omega)
              · exact true_step 2 (by omega) hs2 hC1
                  (edgeFinset_card_deleteVertex_deg2 H ℓ p q hHlp hHpq hqne hHpdeg2)
            · have hHpdeg1 : ∀ w, H.Adj p w → w = ℓ := by
                intro w hw
                rcases hGpdeg2 w (hHG hw) with hwl | hwq
                · exact hwl
                · exact False.elim (hHpq (hwq ▸ hw))
              obtain ⟨hs1,hC1⟩ := elim_one_var ℓ true hC hdep hnc1
              exact true_step 1 (by omega) hs1 hC1
                (edgeFinset_card_deleteVertex_deg1 H ℓ p hHlp hHpdeg1)

theorem relative_forest_sandwich {n t s : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (A : Finset (Fin n)) (F : (Fin n → Bool) → Bool)
    (hforest : G.IsAcyclic) (hHG : H ≤ G)
    (hAiso : ∀ a ∈ A, ∀ v, ¬ G.Adj a v)
    (hvc : HasMinVC H t) (hSand : ForestSandwich H G A F)
    (hC : HasCircuitSize n F s) : A.card + H.edgeFinset.card + t ≤ s + 1 :=
  relative_forest_sandwich_aux (s+G.edgeFinset.card) s G H A F
    rfl hforest hHG hAiso hvc hSand hC

end PEqualNP.Outside.L_meta_1031_aux.RelativeForestCore

namespace PEqualNP.Outside.L_meta_1031_aux

open Finset

variable {ι : Type*} [DecidableEq ι]

def QuadraticActive (f : Finset ι → Bool) (i : ι) : Prop :=
  ∃ A : Finset ι, Minterm f A ∧ A.card = 2 ∧ i ∈ A

def LongMintermInactive (f : Finset ι → Bool) : Prop :=
  ∀ A : Finset ι, Minterm f A → 3 ≤ A.card →
    ∃ i ∈ A, ∃ j ∈ A, i ≠ j ∧ ¬ QuadraticActive f i ∧ ¬ QuadraticActive f j

theorem minterm_nonempty_of_zero {f : Finset ι → Bool} {A : Finset ι}
    (hf : f ∅ = false) (hA : Minterm f A) : A.Nonempty := by
  apply Finset.nonempty_iff_ne_empty.mpr
  intro h
  simpa [h,hf] using hA.1

theorem minterm_and_card_split {f g : Finset ι → Bool} {S T A : Finset ι}
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (hA : Minterm (fun X => f X && g X) A) :
    (A ∩ S).card + (A ∩ T).card = A.card := by
  have hsub := hA.subset_support (feature_supported_and hs ht)
  have he : (A ∩ S) ∪ (A ∩ T) = A := by
    apply Finset.Subset.antisymm (union_subset inter_subset_left inter_subset_left)
    intro i hi
    rcases mem_union.mp (hsub hi) with his | hit
    · exact mem_union_left _ (mem_inter.mpr ⟨hi,his⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hi,hit⟩)
  have hd : Disjoint (A ∩ S) (A ∩ T) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact Finset.disjoint_left.mp hdis (mem_inter.mp hi).2 (mem_inter.mp hj).2
  rw [← Finset.card_union_of_disjoint hd,he]

theorem quadratic_active_and_left_singleton {f g : Finset ι → Bool}
    {S T : Finset ι} {i : ι}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (hg0 : g ∅ = false) (hiS : i ∈ S)
    (hi : QuadraticActive (fun X => f X && g X) i) : f {i} = true := by
  obtain ⟨B,hB,hcard,hiB⟩ := hi
  have hL := minterm_and_left hf hg hs ht hdis hB
  have hR := minterm_and_right hf hg hs ht hdis hB
  have hp := Finset.card_pos.mpr (minterm_nonempty_of_zero hg0 hR)
  have hc := minterm_and_card_split hs ht hdis hB
  have hle : (B ∩ S).card ≤ 1 := by omega
  have he : {i} = B ∩ S := Finset.eq_of_subset_of_card_le
    (singleton_subset_iff.mpr (mem_inter.mpr ⟨hiB,hiS⟩)) (by simpa using hle)
  simpa only [← he] using hL.1

theorem minterm_and_large_left_inactive {f g : Finset ι → Bool}
    {S T A : Finset ι}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (hg0 : g ∅ = false)
    (hA : Minterm (fun X => f X && g X) A) (hlarge : 2 ≤ (A ∩ S).card) :
    ∀ i ∈ A ∩ S, ¬ QuadraticActive (fun X => f X && g X) i := by
  intro i hi hactive
  have hsingle := quadratic_active_and_left_singleton hf hg hs ht hdis hg0
    (mem_inter.mp hi).2 hactive
  have hL := minterm_and_left hf hg hs ht hdis hA
  have he : {i} = A ∩ S := hL.2 {i} (singleton_subset_iff.mpr hi) hsingle
  have hc : (A ∩ S).card = 1 := by rw [← he]; simp
  omega

theorem long_minterm_inactive_and {f g : Finset ι → Bool} {S T : Finset ι}
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hdis : Disjoint S T) (hf0 : f ∅ = false) (hg0 : g ∅ = false) :
    LongMintermInactive (fun X => f X && g X) := by
  intro A hA hlarge
  have hc := minterm_and_card_split hs ht hdis hA
  by_cases hleft : 2 ≤ (A ∩ S).card
  · obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (A ∩ S).card)
    have hinactive := minterm_and_large_left_inactive hf hg hs ht hdis hg0 hA hleft
    exact ⟨i,(mem_inter.mp hi).1,j,(mem_inter.mp hj).1,hij,
      hinactive i hi,hinactive j hj⟩
  · have hright : 2 ≤ (A ∩ T).card := by omega
    have hA' : Minterm (fun X => g X && f X) A := by
      simpa only [Bool.and_comm] using hA
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (A ∩ T).card)
    have hinactive := minterm_and_large_left_inactive hg hf ht hs hdis.symm hf0 hA' hright
    refine ⟨i,(mem_inter.mp hi).1,j,(mem_inter.mp hj).1,hij,?_,?_⟩
    · simpa only [Bool.and_comm] using hinactive i hi
    · simpa only [Bool.and_comm] using hinactive j hj

theorem quadratic_active_or_left {f g : Finset ι → Bool} {S T : Finset ι} {i : ι}
    (ht : FeatureSupported g T) (hdis : Disjoint S T) (hiS : i ∈ S)
    (hi : QuadraticActive (fun X => f X || g X) i) : QuadraticActive f i := by
  obtain ⟨A,hA,hcard,hiA⟩ := hi
  rcases minterm_or_cases hA with hF | hG
  · exact ⟨A,hF,hcard,hiA⟩
  · exact (Finset.disjoint_left.mp hdis hiS (hG.subset_support ht hiA)).elim

theorem long_minterm_inactive_or {f g : Finset ι → Bool} {S T : Finset ι}
    (hs : FeatureSupported f S) (ht : FeatureSupported g T) (hdis : Disjoint S T)
    (hF : LongMintermInactive f) (hG : LongMintermInactive g) :
    LongMintermInactive (fun X => f X || g X) := by
  intro A hA hlarge
  rcases minterm_or_cases hA with hAf | hAg
  · obtain ⟨i,hi,j,hj,hij,hif,hjf⟩ := hF A hAf hlarge
    exact ⟨i,hi,j,hj,hij,
      fun h => hif (quadratic_active_or_left ht hdis (hAf.subset_support hs hi) h),
      fun h => hjf (quadratic_active_or_left ht hdis (hAf.subset_support hs hj) h)⟩
  · obtain ⟨i,hi,j,hj,hij,hig,hjg⟩ := hG A hAg hlarge
    refine ⟨i,hi,j,hj,hij,?_,?_⟩
    · intro h
      apply hig
      apply quadratic_active_or_left hs hdis.symm (hAg.subset_support ht hi)
      simpa only [Bool.or_comm] using h
    · intro h
      apply hjg
      apply quadratic_active_or_left hs hdis.symm (hAg.subset_support ht hj)
      simpa only [Bool.or_comm] using h

theorem long_minterm_inactive_literal (i : ι) :
    LongMintermInactive (fun X => decide (i ∈ X)) := by
  intro A hA hlarge
  have he := (minterm_literal_iff i A).mp hA
  simp [he] at hlarge

theorem LongMintermInactive.quadratic {f : Finset ι → Bool} {S : Finset ι}
    (hprop : LongMintermInactive f) (hs : FeatureSupported f S)
    (h0 : f ∅ = false) (h1 : ∀ i, f {i} = false)
    (hactive : ∀ i ∈ S, QuadraticActive f i)
    {A : Finset ι} (hA : Minterm f A) : A.card = 2 := by
  have hpos := Finset.card_pos.mpr (minterm_nonempty_of_zero h0 hA)
  have hsmall : A.card ≤ 2 := by
    by_contra h
    obtain ⟨i,hi,j,hj,hij,hif,hjf⟩ := hprop A hA (by omega)
    exact hif (hactive i (hA.subset_support hs hi))
  have hne : A.card ≠ 1 := by
    intro hc
    obtain ⟨i,he⟩ := Finset.card_eq_one.mp hc
    have ht := hA.1
    simpa [he,h1] using ht
  omega

theorem quadratic_active_or_other_support {f g : Finset ι → Bool}
    {T : Finset ι} {i : ι} (ht : FeatureSupported g T)
    (hnot : ¬ QuadraticActive f i)
    (hi : QuadraticActive (fun X => f X || g X) i) : i ∈ T := by
  obtain ⟨A,hA,hcard,hiA⟩ := hi
  rcases minterm_or_cases hA with hF | hG
  · exact (hnot ⟨A,hF,hcard,hiA⟩).elim
  · exact hG.subset_support ht hiA

theorem one_overlap_or_minterm_card_le_two {f g : Finset ι → Bool}
    {S T : Finset ι} {z : ι}
    (hs : FeatureSupported f S) (ht : FeatureSupported g T)
    (hinter : ∀ i ∈ S, i ∈ T → i = z)
    (hF : LongMintermInactive f) (hG : LongMintermInactive g)
    (hactive : ∀ i ∈ S ∪ T, QuadraticActive (fun X => f X || g X) i)
    {A : Finset ι} (hA : Minterm (fun X => f X || g X) A) : A.card ≤ 2 := by
  by_contra hsmall
  have hlarge : 3 ≤ A.card := by omega
  rcases minterm_or_cases hA with hAf | hAg
  · obtain ⟨i,hi,j,hj,hij,hif,hjf⟩ := hF A hAf hlarge
    have hiS := hAf.subset_support hs hi
    have hjS := hAf.subset_support hs hj
    have hiT := quadratic_active_or_other_support ht hif
      (hactive i (mem_union_left _ hiS))
    have hjT := quadratic_active_or_other_support ht hjf
      (hactive j (mem_union_left _ hjS))
    exact hij ((hinter i hiS hiT).trans (hinter j hjS hjT).symm)
  · obtain ⟨i,hi,j,hj,hij,hig,hjg⟩ := hG A hAg hlarge
    have hiT := hAg.subset_support ht hi
    have hjT := hAg.subset_support ht hj
    have hiS : i ∈ S := quadratic_active_or_other_support hs hig (by
      simpa only [Bool.or_comm] using hactive i (mem_union_right _ hiT))
    have hjS : j ∈ S := quadratic_active_or_other_support hs hjg (by
      simpa only [Bool.or_comm] using hactive j (mem_union_right _ hjT))
    exact hij ((hinter i hiS hiT).trans (hinter j hjS hjT).symm)

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem feature_exists_minterm_subset (f : Finset ι → Bool)
    {T : Finset ι} (hT : f T = true) : ∃ S ⊆ T, Minterm f S := by
  classical
  let P : ℕ → Prop := fun k => ∃ S : Finset ι, S ⊆ T ∧ S.card = k ∧ f S = true
  have hex : ∃ k, P k := ⟨T.card,T,Finset.Subset.refl T,rfl,hT⟩
  obtain ⟨S,hST,hcard,hs⟩ := Nat.find_spec hex
  refine ⟨S,hST,hs,?_⟩
  intro R hRS hr
  have hmin := Nat.find_min' hex
    (show P R.card from ⟨R,hRS.trans hST,rfl,hr⟩)
  exact Finset.eq_of_subset_of_card_le hRS (by omega)

theorem feature_supported_singleton_outside {f : Finset ι → Bool} {S : Finset ι}
    (hs : FeatureSupported f S) {u : ι} (hu : u ∉ S) : f {u} = f ∅ := by
  have hempty : ({u} : Finset ι) ∩ S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxu,hxS⟩ := Finset.mem_inter.mp hx
    exact hu ((Finset.mem_singleton.mp hxu) ▸ hxS)
  rw [hs {u},hempty]

theorem feature_supported_pair_left_outside {f : Finset ι → Bool} {S : Finset ι}
    (hs : FeatureSupported f S) {u v : ι} (hu : u ∉ S) : f {u,v} = f {v} := by
  have he : ({u,v} : Finset ι) ∩ S = ({v} : Finset ι) ∩ S := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨hxu | hxv,hxS⟩
      · subst x
        exact (hu hxS).elim
      · exact ⟨hxv,hxS⟩
    · rintro ⟨hxv,hxS⟩
      exact ⟨Or.inr hxv,hxS⟩
  rw [hs {u,v},hs {v},he]

theorem feature_minterm_pair {f : Finset ι → Bool}
    (hf : FeatureMonotone f) {u v : ι}
    (hu : f {u} = false) (hv : f {v} = false) (huv : f {u,v} = true) :
    Minterm f {u,v} := by
  refine ⟨huv,?_⟩
  intro T hT ht
  have huT : u ∈ T := by
    by_contra hn
    have hsub : T ⊆ {v} := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with hxu | hxv
      · exact (hn (hxu ▸ hx)).elim
      · exact hxv
    have hh := hf T {v} hsub ht
    rw [hv] at hh
    contradiction
  have hvT : v ∈ T := by
    by_contra hn
    have hsub : T ⊆ {u} := by
      intro x hx
      rcases Finset.mem_insert.mp (hT hx) with hxu | hxv
      · exact Finset.mem_singleton.mpr hxu
      · have hxv' := Finset.mem_singleton.mp hxv
        exact (hn (hxv' ▸ hx)).elim
    have hh := hf T {u} hsub ht
    rw [hu] at hh
    contradiction
  exact Finset.Subset.antisymm hT (Finset.insert_subset huT (Finset.singleton_subset_iff.mpr hvT))

theorem rectangle_star_rows_minterm_card_le_one {f : Finset ι → Bool}
    (hf : FeatureMonotone f) (hr : MintermRectangle f) {z : ι}
    (hz : f {z} = false) {T : Finset ι} (hT : Minterm f T) (hzT : z ∉ T)
    (hrows : ∀ a ∈ T, f {z,a} = true) : T.card ≤ 1 := by
  classical
  by_contra hnot
  have htwo : 1 < T.card := by omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp htwo
  have hsingle : ∀ x ∈ T, f {x} = false := by
    intro x hx
    cases hfx : f {x} with
    | false => rfl
    | true =>
      have he := hT.2 {x} (Finset.singleton_subset_iff.mpr hx) hfx
      have hc := congrArg Finset.card he
      simp only [Finset.card_singleton] at hc
      omega
  have hza := feature_minterm_pair hf hz (hsingle a ha) (hrows a ha)
  have hzb := feature_minterm_pair hf hz (hsingle b hb) (hrows b hb)
  have hsub : ({z,b} : Finset ι) ⊆ {z,a} ∪ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hxz | hxb
    · subst x
      exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    · exact Finset.mem_union_right _ ((Finset.mem_singleton.mp hxb).symm ▸ hb)
  have hint : (({z,a} : Finset ι) ∩ {z,b}) ∩ T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxAB,hxT⟩ := Finset.mem_inter.mp hx
    obtain ⟨hxA,hxB⟩ := Finset.mem_inter.mp hxAB
    rcases Finset.mem_insert.mp hxA with hxz | hxa
    · exact hzT (hxz ▸ hxT)
    · have hxa' := Finset.mem_singleton.mp hxa
      rcases Finset.mem_insert.mp hxB with hxz | hxb
      · exact hzT (hxz ▸ hxT)
      · exact hab (hxa'.symm.trans (Finset.mem_singleton.mp hxb))
  have hrect := hr {z,a} {z,b} T hza hzb hT hsub hint
  have hsmall : (({z,a} : Finset ι) ∪ T) \ {z,b} ⊆ T.erase b := by
    intro x hx
    obtain ⟨hxU,hxnot⟩ := Finset.mem_sdiff.mp hx
    have hxb : x ≠ b := by
      intro he
      subst x
      exact hxnot (by simp)
    refine Finset.mem_erase.mpr ⟨hxb,?_⟩
    rcases Finset.mem_union.mp hxU with hxA | hxT
    · rcases Finset.mem_insert.mp hxA with hxz | hxa
      · subst x
        exact (hxnot (by simp)).elim
      · exact (Finset.mem_singleton.mp hxa).symm ▸ ha
    · exact hxT
  have htrue := hf _ _ hsmall hrect
  have he := hT.2 (T.erase b) (Finset.erase_subset _ _) htrue
  have hbb : b ∈ T.erase b := he.symm ▸ hb
  exact (Finset.notMem_erase b T) hbb

theorem rectangle_star_rows_extract_singleton {f : Finset ι → Bool}
    (hf : FeatureMonotone f) (hr : MintermRectangle f)
    (hf0 : f ∅ = false) {z : ι} (hz : f {z} = false)
    {A T : Finset ι} (hs : FeatureSupported f (insert z A))
    (hrows : ∀ a ∈ A, f {z,a} = true)
    (hT : f T = true) (hzT : z ∉ T) : ∃ a ∈ T, f {a} = true := by
  obtain ⟨R,hRT,hR⟩ := feature_exists_minterm_subset f hT
  have hzR : z ∉ R := fun h => hzT (hRT h)
  have hRs : R ⊆ insert z A := hR.subset_support hs
  have hc : R.card ≤ 1 := rectangle_star_rows_minterm_card_le_one hf hr hz hR hzR
    (fun a ha => hrows a (by
      rcases Finset.mem_insert.mp (hRs ha) with haz | haA
      · exact (hzR (haz ▸ ha)).elim
      · exact haA))
  have hne : R.Nonempty := by
    by_contra hn
    have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hh := hR.1
    rw [he,hf0] at hh
    contradiction
  obtain ⟨a,ha⟩ := hne
  have he : R = {a} := Finset.eq_singleton_iff_unique_mem.mpr
    ⟨ha,fun b hb => Finset.card_le_one_iff.mp hc hb ha⟩
  exact ⟨a,hRT ha,he ▸ hR.1⟩

theorem repeated_literal_and_quadratic_of_orientation
    {f g : Finset ι → Bool} {z : ι} {A B : Finset ι}
    (hAB : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B)
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hfs : FeatureSupported f (insert z A)) (hgs : FeatureSupported g (insert z B))
    (hf0 : f ∅ = false) (hg0 : g ∅ = false)
    (hr : MintermRectangle f) (hfz : f {z} = false) (hgz : g {z} = true)
    (hactive : ∀ u ∈ insert z (A ∪ B), ∃ v ∈ insert z (A ∪ B),
      u ≠ v ∧ (f {u,v} && g {u,v}) = true) :
    ∀ T, Minterm (fun X => f X && g X) T → T.card = 2 := by
  classical
  have hAnB : ∀ a ∈ A, a ∉ insert z B := by
    intro a ha hmem
    rcases Finset.mem_insert.mp hmem with haz | haB
    · exact hzA (haz ▸ ha)
    · exact Finset.disjoint_left.mp hAB ha haB
  have hBnA : ∀ b ∈ B, b ∉ insert z A := by
    intro b hb hmem
    rcases Finset.mem_insert.mp hmem with hbz | hbA
    · exact hzB (hbz ▸ hb)
    · exact Finset.disjoint_left.mp hAB hbA hb
  have hBsingle : ∀ b ∈ B, g {b} = true := by
    intro b hb
    obtain ⟨v,hv,_hbv,hpair⟩ := hactive b
      (Finset.mem_insert_of_mem (Finset.mem_union_right _ hb))
    obtain ⟨hfbv,hgbv⟩ := Bool.and_eq_true_iff.mp hpair
    have hfv : f {v} = true :=
      (feature_supported_pair_left_outside hfs (hBnA b hb)).symm.trans hfbv
    have hvA : v ∈ A := by
      rcases Finset.mem_insert.mp hv with hvz | hvAB
      · subst v
        rw [hfz] at hfv
        contradiction
      · rcases Finset.mem_union.mp hvAB with hvA | hvB
        · exact hvA
        · rw [feature_supported_singleton_outside hfs (hBnA v hvB),hf0] at hfv
          contradiction
    have he : g {b,v} = g {b} := by
      rw [Finset.pair_comm]
      exact feature_supported_pair_left_outside hgs (hAnB v hvA)
    exact he.symm.trans hgbv
  have hArows : ∀ a ∈ A, f {z,a} = true := by
    intro a ha
    obtain ⟨v,hv,_hav,hpair⟩ := hactive a
      (Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
    obtain ⟨hfav,hgav⟩ := Bool.and_eq_true_iff.mp hpair
    rcases Finset.mem_insert.mp hv with hvz | hvAB
    · subst v
      simpa only [Finset.pair_comm] using hfav
    · rcases Finset.mem_union.mp hvAB with hvA | hvB
      · have hgv : g {v} = true :=
          (feature_supported_pair_left_outside hgs (hAnB a ha)).symm.trans hgav
        rw [feature_supported_singleton_outside hgs (hAnB v hvA),hg0] at hgv
        contradiction
      · have he : f {a,v} = f {a} := by
          rw [Finset.pair_comm]
          exact feature_supported_pair_left_outside hfs (hBnA v hvB)
        exact hf {a} {z,a} (by simp) (he.symm.trans hfav)
  intro T hT
  have hTf : f T = true := (Bool.and_eq_true_iff.mp hT.1).1
  have hTg : g T = true := (Bool.and_eq_true_iff.mp hT.1).2
  by_cases hzT : z ∈ T
  · have hex : ∃ a ∈ T, a ∈ A := by
      by_contra hn
      have hsub : T ∩ insert z A ⊆ {z} := by
        intro a ha
        obtain ⟨haT,haS⟩ := Finset.mem_inter.mp ha
        rcases Finset.mem_insert.mp haS with haz | haA
        · exact Finset.mem_singleton.mpr haz
        · exact (hn ⟨a,haT,haA⟩).elim
      have hh := hf _ _ hsub ((hfs T).symm.trans hTf)
      rw [hfz] at hh
      contradiction
    obtain ⟨a,haT,haA⟩ := hex
    have hK : (f {z,a} && g {z,a}) = true := Bool.and_eq_true_iff.mpr
      ⟨hArows a haA,hg {z} {z,a} (by simp) hgz⟩
    have he := hT.2 {z,a}
      (Finset.insert_subset hzT (Finset.singleton_subset_iff.mpr haT)) hK
    have hza : z ≠ a := fun e => hzA (e.symm ▸ haA)
    rw [← he,Finset.card_pair hza]
  · obtain ⟨a,haT,hfa⟩ := rectangle_star_rows_extract_singleton
      hf hr hf0 hfz hfs hArows hTf hzT
    have hex : ∃ b ∈ T, b ∈ B := by
      by_contra hn
      have he : T ∩ insert z B = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨hbT,hbS⟩ := Finset.mem_inter.mp hb
        rcases Finset.mem_insert.mp hbS with hbz | hbB
        · exact hzT (hbz ▸ hbT)
        · exact hn ⟨b,hbT,hbB⟩
      have hh := (hgs T).symm.trans hTg
      rw [he,hg0] at hh
      contradiction
    obtain ⟨b,hbT,hbB⟩ := hex
    have haA : a ∈ A := by
      by_contra hn
      have haS : a ∉ insert z A := by
        intro hm
        rcases Finset.mem_insert.mp hm with haz | haA
        · exact hzT (haz ▸ haT)
        · exact hn haA
      rw [feature_supported_singleton_outside hfs haS,hf0] at hfa
      contradiction
    have hK : (f {a,b} && g {a,b}) = true := Bool.and_eq_true_iff.mpr
      ⟨hf {a} {a,b} (by simp) hfa,hg {b} {a,b} (by simp) (hBsingle b hbB)⟩
    have he := hT.2 {a,b}
      (Finset.insert_subset haT (Finset.singleton_subset_iff.mpr hbT)) hK
    have hab : a ≠ b := fun e => Finset.disjoint_left.mp hAB (e ▸ haA) hbB
    rw [← he,Finset.card_pair hab]

theorem repeated_literal_and_quadratic
    {f g : Finset ι → Bool} {z : ι} {A B : Finset ι}
    (hAB : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B)
    (hf : FeatureMonotone f) (hg : FeatureMonotone g)
    (hfs : FeatureSupported f (insert z A)) (hgs : FeatureSupported g (insert z B))
    (hf0 : f ∅ = false) (hg0 : g ∅ = false)
    (hrf : MintermRectangle f) (hrg : MintermRectangle g)
    (hzfalse : (f {z} && g {z}) = false)
    (hactive : ∀ u ∈ insert z (A ∪ B), ∃ v ∈ insert z (A ∪ B),
      u ≠ v ∧ (f {u,v} && g {u,v}) = true) :
    ∀ T, Minterm (fun X => f X && g X) T → T.card = 2 := by
  classical
  by_cases hfz : f {z} = true
  · have hgz : g {z} = false := by simpa only [hfz,Bool.true_and] using hzfalse
    have hactive' : ∀ u ∈ insert z (B ∪ A), ∃ v ∈ insert z (B ∪ A),
        u ≠ v ∧ (g {u,v} && f {u,v}) = true := by
      intro u hu
      obtain ⟨v,hv,hne,hpair⟩ := hactive u (by simpa only [Finset.union_comm] using hu)
      exact ⟨v,by simpa only [Finset.union_comm] using hv,hne,
        by simpa only [Bool.and_comm] using hpair⟩
    intro T hT
    apply repeated_literal_and_quadratic_of_orientation hAB.symm hzB hzA
      hg hf hgs hfs hg0 hf0 hrg hgz hfz hactive' T
    simpa only [Bool.and_comm] using hT
  · have hfz' : f {z} = false := by
      cases he : f {z} <;> simp_all
    obtain ⟨v,hv,hzv,hpair⟩ := hactive z (Finset.mem_insert_self _ _)
    obtain ⟨hfv,hgv⟩ := Bool.and_eq_true_iff.mp hpair
    have hgz : g {z} = true := by
      rcases Finset.mem_insert.mp hv with hvz | hvAB
      · exact (hzv hvz.symm).elim
      · rcases Finset.mem_union.mp hvAB with hvA | hvB
        · have hvS : v ∉ insert z B := by
            intro hm
            rcases Finset.mem_insert.mp hm with hvz | hvB
            · exact hzA (hvz ▸ hvA)
            · exact Finset.disjoint_left.mp hAB hvA hvB
          have he : g {z,v} = g {z} := by
            rw [Finset.pair_comm]
            exact feature_supported_pair_left_outside hgs hvS
          exact he.symm.trans hgv
        · have hvS : v ∉ insert z A := by
            intro hm
            rcases Finset.mem_insert.mp hm with hvz | hvA
            · exact hzB (hvz ▸ hvB)
            · exact Finset.disjoint_left.mp hAB hvA hvB
          have he : f {z,v} = f {z} := by
            rw [Finset.pair_comm]
            exact feature_supported_pair_left_outside hfs hvS
          have hh := he.symm.trans hfv
          rw [hfz'] at hh
          contradiction
    exact repeated_literal_and_quadratic_of_orientation hAB hzA hzB
      hf hg hfs hgs hf0 hg0 hrf hfz' hgz hactive

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticSubstitution

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

structure Data (h : Finset α → Bool) (P : Bool → Finset β → Bool) : Prop where
  inner_zero : h ∅ = false
  zero : P false ∅ = false
  inner_singleton : ∀ a, P (h {a}) ∅ = false
  outer_singleton : ∀ b, P false {b} = false
  inner_pairs : ∀ a,
    (∃ a', a' ≠ a ∧ P (h {a,a'}) ∅ = true) ∨
      ∃ b, P (h {a}) {b} = true
  outer_pairs : ∀ b,
    (∃ b', b' ≠ b ∧ P false {b,b'} = true) ∨
      ∃ a, P (h {a}) {b} = true

end PEqualNP.Outside.L_meta_1031_aux.QuadraticSubstitution

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset

noncomputable def gateReaders (C : Circuit) (w : ℕ) : Finset ℕ := by
  classical
  exact (range C.gates.length).filter (fun j => w ∈ gateInputSet C j)

@[simp] theorem mem_gateReaders {C : Circuit} {w j : ℕ} :
    j ∈ gateReaders C w ↔ j < C.gates.length ∧ w ∈ gateInputSet C j := by
  classical
  simp [gateReaders]

theorem clean_gate_input_card {n : ℕ} {C : Circuit} (hc : CleanMono n C)
    {j : ℕ} (hj : j < C.gates.length) : (gateInputSet C j).card = 2 := by
  have hget : C.gates[j]? = some (C.gates.get ⟨j,hj⟩) :=
    List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
  obtain ⟨a,b,hi,_,_,hab⟩ := hc j _ hget
  rw [gateInputSet_of_get hget,hi]
  simp [hab]

theorem clean_gate_input_before_last {n : ℕ} {C : Circuit} (hc : CleanMono n C)
    (hlast : C.output + 1 = n + C.gates.length)
    {j : ℕ} (hj : j < C.gates.length) : gateInputSet C j ⊆ range C.output := by
  have hget : C.gates[j]? = some (C.gates.get ⟨j,hj⟩) :=
    List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
  obtain ⟨a,b,hi,ha,hb,_⟩ := hc j _ hget
  intro w hw
  rw [gateInputSet_of_get hget,hi] at hw
  have hw' : w = a ∨ w = b := by simpa using hw
  apply mem_range.mpr
  rcases hw' with rfl | rfl <;> omega

theorem clean_reader_sum {n : ℕ} {C : Circuit} (hc : CleanMono n C)
    (hlast : C.output + 1 = n + C.gates.length) :
    (∑ w ∈ range C.output, (gateReaders C w).card) = 2 * C.gates.length := by
  classical
  have hfilter : ∀ j ∈ range C.gates.length,
      (range C.output).filter (fun w => w ∈ gateInputSet C j) = gateInputSet C j := by
    intro j hj
    apply Finset.ext
    intro w
    simp only [mem_filter]
    exact ⟨fun h => h.2,fun h =>
      ⟨clean_gate_input_before_last hc hlast (mem_range.mp hj) h,h⟩⟩
  calc
    (∑ w ∈ range C.output, (gateReaders C w).card) =
        ∑ w ∈ range C.output, ∑ j ∈ range C.gates.length,
          if w ∈ gateInputSet C j then 1 else 0 := by
      simp only [gateReaders,Finset.card_eq_sum_ones,Finset.sum_filter]
    _ = ∑ j ∈ range C.gates.length, ∑ w ∈ range C.output,
          if w ∈ gateInputSet C j then 1 else 0 := Finset.sum_comm
    _ = ∑ j ∈ range C.gates.length, (gateInputSet C j).card := by
      apply Finset.sum_congr rfl
      intro j hj
      have hh := congrArg Finset.card (hfilter j hj)
      simpa only [Finset.card_eq_sum_ones,Finset.sum_filter] using hh
    _ = ∑ _j ∈ range C.gates.length, 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      exact clean_gate_input_card hc (mem_range.mp hj)
    _ = 2 * C.gates.length := by simp [Nat.mul_comm]

theorem positive_sum_card_all_one {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (hpos : ∀ i ∈ S, 1 ≤ f i)
    (hsum : (∑ i ∈ S, f i) = S.card) : ∀ i ∈ S, f i = 1 := by
  have heq : (∑ _i ∈ S, 1) = ∑ i ∈ S, f i := by simpa using hsum.symm
  have hh := (Finset.sum_eq_sum_iff_of_le hpos).mp heq
  exact fun i hi => (hh i hi).symm

theorem positive_sum_card_add_one {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (hpos : ∀ i ∈ S, 1 ≤ f i)
    (hsum : (∑ i ∈ S, f i) = S.card + 1) :
    ∃ z ∈ S, f z = 2 ∧ ∀ i ∈ S, i ≠ z → f i = 1 := by
  classical
  have hex : ∃ z ∈ S, 2 ≤ f z := by
    by_contra hn
    push_neg at hn
    have hall : ∀ i ∈ S, f i = 1 := by
      intro i hi
      have := hpos i hi
      have := hn i hi
      omega
    have he : (∑ i ∈ S, f i) = S.card := by simp only [Finset.sum_congr rfl hall]; simp
    omega
  obtain ⟨z,hz,hz2⟩ := hex
  have hsplit := Finset.sum_erase_add S f hz
  have hcard := Finset.card_erase_of_mem hz
  have hcardpos : 0 < S.card := Finset.card_pos.mpr ⟨z,hz⟩
  have herase : (S.erase z).card ≤ ∑ i ∈ S.erase z, f i := by
    calc
      (S.erase z).card = ∑ _i ∈ S.erase z, 1 := by simp
      _ ≤ ∑ i ∈ S.erase z, f i := Finset.sum_le_sum
        (fun i hi => hpos i (Finset.mem_of_mem_erase hi))
  have hzval : f z = 2 := by omega
  have heq : (∑ i ∈ S.erase z, f i) = (S.erase z).card := by omega
  refine ⟨z,hz,hzval,?_⟩
  intro i hi hiz
  exact positive_sum_card_all_one (S.erase z) f
    (fun j hj => hpos j (Finset.mem_of_mem_erase hj)) heq i
    (Finset.mem_erase.mpr ⟨hiz,hi⟩)

theorem clean_live_one_surplus_readers {n : ℕ} {C : Circuit}
    (hc : CleanMono n C) (hlast : C.output + 1 = n + C.gates.length)
    (hlive : ∀ w < C.output, (gateReaders C w).Nonempty)
    (hsize : C.gates.length ≤ n) :
    (C.gates.length + 1 = n ∧ ∀ w < C.output, (gateReaders C w).card = 1) ∨
    (C.gates.length = n ∧ ∃ z < C.output, (gateReaders C z).card = 2 ∧
      ∀ w < C.output, w ≠ z → (gateReaders C w).card = 1) := by
  classical
  have hsum := clean_reader_sum hc hlast
  have hpos : ∀ w ∈ range C.output, 1 ≤ (gateReaders C w).card := by
    intro w hw
    exact Finset.card_pos.mpr (hlive w (mem_range.mp hw))
  have hlow : C.output ≤ 2 * C.gates.length := by
    calc
      C.output = ∑ _w ∈ range C.output, 1 := by simp
      _ ≤ ∑ w ∈ range C.output, (gateReaders C w).card := Finset.sum_le_sum hpos
      _ = 2 * C.gates.length := hsum
  by_cases heq : C.gates.length = n
  · right
    refine ⟨heq,?_⟩
    have htotal : (∑ w ∈ range C.output, (gateReaders C w).card) =
        (range C.output).card + 1 := by simp only [card_range]; omega
    obtain ⟨z,hz,hzval,hother⟩ := positive_sum_card_add_one
      (range C.output) (fun w => (gateReaders C w).card) hpos htotal
    exact ⟨z,mem_range.mp hz,hzval,fun w hw hne => hother w (mem_range.mpr hw) hne⟩
  · left
    have hsize' : C.gates.length + 1 = n := by omega
    refine ⟨hsize',?_⟩
    have htotal : (∑ w ∈ range C.output, (gateReaders C w).card) =
        (range C.output).card := by simp only [card_range]; omega
    exact fun w hw => positive_sum_card_all_one (range C.output)
      (fun w => (gateReaders C w).card) hpos htotal w (mem_range.mpr hw)

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset

theorem val_agree_without_primary_reader {n : ℕ} {C : Circuit} (u : Fin n)
    (hread : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → u.val ∉ g.inputs)
    {x y : Fin n → Bool} (hxy : ∀ i, i ≠ u → x i = y i)
    {w : ℕ} (hw : w ≠ u.val) : val C x w = val C y w := by
  suffices hall : ∀ w, w ≠ u.val → val C x w = val C y w from hall w hw
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwu
    by_cases hwn : w < n
    · let i : Fin n := ⟨w,hwn⟩
      have hi : i ≠ u := by
        intro he
        exact hwu (congrArg Fin.val he)
      exact (val_input C x i).trans ((hxy i hi).trans (val_input C y i).symm)
    by_cases hwb : n + C.gates.length ≤ w
    · rw [val_beyond C x hwb,val_beyond C y hwb]
    obtain ⟨p,hp,rfl⟩ : ∃ p, p < C.gates.length ∧ w = n+p :=
      ⟨w-n,by omega,by omega⟩
    have hget : C.gates[p]? = some (C.gates.get ⟨p,hp⟩) :=
      List.getElem?_eq_some_iff.mpr ⟨hp,rfl⟩
    rw [val_gate C x hget,val_gate C y hget]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hiu : i ≠ u.val := by
      intro he
      exact hread p _ hget (he ▸ hi)
    by_cases hie : i < n+p
    · simp only [operand,ite_eq_left hie]
      exact ih i hie hiu
    · simp [operand,hie]

theorem singleton_reject_output_internal {n : ℕ} {C : Circuit}
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false) :
    n ≤ C.output := by
  by_contra hn
  have hout : C.output < n := by omega
  let u : Fin n := ⟨C.output,hout⟩
  have hv := val_input C (singletonInput u) u
  have hs := hsingle u
  change val C (singletonInput u) C.output = false at hs
  have ht : val C (singletonInput u) C.output = true := by
    simpa [singletonInput] using hv
  rw [hs] at ht
  contradiction

theorem quadratic_active_gate_nonempty {n : ℕ} {C : Circuit} (hn : 0 < n)
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false)
    (hpairs : ∀ u : Fin n, ∃ v : Fin n,
      C.eval (List.ofFn (pairInput u v)) = true) :
    0 < C.gates.length := by
  have hint := singleton_reject_output_internal hsingle
  obtain ⟨v,hpair⟩ := hpairs ⟨0,hn⟩
  by_contra hz
  have hlen : C.gates.length = 0 := by omega
  have hf := val_beyond C (pairInput ⟨0,hn⟩ v) (by omega : n+C.gates.length ≤ C.output)
  change val C (pairInput ⟨0,hn⟩ v) C.output = true at hpair
  rw [hf] at hpair
  contradiction

theorem minimal_positive_output_last {n : ℕ} {C : Circuit}
    (hn : 0 < n) (hmin : IsMinimalMonoCircuit n C) (hg : 0 < C.gates.length) :
    C.output + 1 = n + C.gates.length := by
  have hp : C.gates.length - 1 < C.gates.length := by omega
  rcases minimal_output_or_later_reader hn hmin hp with hout | ⟨q,g,hpq,hq,_⟩
  · omega
  · have hq' := (List.getElem?_eq_some_iff.mp hq).1
    omega

theorem quadratic_active_primary_reader {n : ℕ} {C : Circuit}
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false)
    (hpairs : ∀ u : Fin n, ∃ v : Fin n,
      C.eval (List.ofFn (pairInput u v)) = true) (u : Fin n) :
    (gateReaders C u.val).Nonempty := by
  classical
  obtain ⟨v,hpair⟩ := hpairs u
  by_contra hn
  have hno : ∀ (j : ℕ) (g : Gate), C.gates[j]? = some g → u.val ∉ g.inputs := by
    intro j g hg hu
    apply hn
    refine ⟨j,mem_gateReaders.mpr ⟨(List.getElem?_eq_some_iff.mp hg).1,?_⟩⟩
    rw [gateInputSet_of_get hg]
    simpa using hu
  have hint := singleton_reject_output_internal hsingle
  have hagree : val C (pairInput u v) C.output = val C (singletonInput v) C.output := by
    apply val_agree_without_primary_reader u hno ?_ (by have := u.isLt; omega)
    intro i hi
    simp [pairInput,singletonInput,hi]
  change C.eval (List.ofFn (pairInput u v)) = C.eval (List.ofFn (singletonInput v)) at hagree
  rw [hpair,hsingle v] at hagree
  contradiction

theorem minimum_quadratic_activity_one_surplus {n : ℕ} {C : Circuit}
    (hn : 0 < n) (hmin : IsMinimalMonoCircuit n C)
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false)
    (hpairs : ∀ u : Fin n, ∃ v : Fin n,
      C.eval (List.ofFn (pairInput u v)) = true)
    (hsize : C.gates.length ≤ n) :
    CleanMono n C ∧ C.output + 1 = n + C.gates.length ∧
    (∀ w < C.output, (gateReaders C w).Nonempty) ∧
    ((C.gates.length + 1 = n ∧ ∀ w < C.output, (gateReaders C w).card = 1) ∨
    (C.gates.length = n ∧ ∃ z < C.output, (gateReaders C z).card = 2 ∧
      ∀ w < C.output, w ≠ z → (gateReaders C w).card = 1)) := by
  have hg := quadratic_active_gate_nonempty hn hsingle hpairs
  have hlast := minimal_positive_output_last hn hmin hg
  have hnc : CircuitNonconstant n C := by
    obtain ⟨v,hpair⟩ := hpairs ⟨0,hn⟩
    refine ⟨singletonInput v,pairInput ⟨0,hn⟩ v,?_⟩
    rw [hsingle v,hpair]
    decide
  have hc := minimal_clean_mono hn hmin hnc
  have hlive : ∀ w < C.output, (gateReaders C w).Nonempty := by
    intro w hw
    by_cases hwn : w < n
    · exact quadratic_active_primary_reader hsingle hpairs ⟨w,hwn⟩
    · obtain ⟨p,hp,rfl⟩ : ∃ p, p < C.gates.length ∧ w = n+p :=
        ⟨w-n,by omega,by omega⟩
      rcases minimal_output_or_later_reader hn hmin hp with hout | ⟨q,g,_,hq,hread⟩
      · omega
      · refine ⟨q,mem_gateReaders.mpr ⟨(List.getElem?_eq_some_iff.mp hq).1,?_⟩⟩
        rw [gateInputSet_of_get hq]
        simpa using hread
  exact ⟨hc,hlast,hlive,clean_live_one_surplus_readers hc hlast hlive hsize⟩

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

open Finset

inductive Expr (ι : Type*) where
  | zero : Expr ι
  | input : ι → Expr ι
  | conj : Expr ι → Expr ι → Expr ι
  | disj : Expr ι → Expr ι → Expr ι

variable {ι : Type*} [DecidableEq ι]

def Expr.eval : Expr ι → Finset ι → Bool
  | .zero, _ => false
  | .input i, S => decide (i ∈ S)
  | .conj p q, S => p.eval S && q.eval S
  | .disj p q, S => p.eval S || q.eval S

def Expr.support : Expr ι → Finset ι
  | .zero => ∅
  | .input i => {i}
  | .conj p q => p.support ∪ q.support
  | .disj p q => p.support ∪ q.support

def Expr.ReadOnce : Expr ι → Prop
  | .zero => True
  | .input _ => True
  | .conj p q => p.ReadOnce ∧ q.ReadOnce ∧ Disjoint p.support q.support
  | .disj p q => p.ReadOnce ∧ q.ReadOnce ∧ Disjoint p.support q.support

def Expr.occurrences : Expr ι → ι → ℕ
  | .zero, _ => 0
  | .input j, i => if i = j then 1 else 0
  | .conj p q, i => p.occurrences i + q.occurrences i
  | .disj p q, i => p.occurrences i + q.occurrences i

theorem Expr.eval_monotone (e : Expr ι) : FeatureMonotone e.eval := by
  induction e with
  | zero => intro A B h hfalse; contradiction
  | input i =>
    intro A B hAB hA
    exact decide_eq_true (hAB (of_decide_eq_true hA))
  | conj p q hp hq => exact feature_monotone_and hp hq
  | disj p q hp hq => exact feature_monotone_or hp hq

theorem Expr.eval_supported (e : Expr ι) : FeatureSupported e.eval e.support := by
  induction e with
  | zero => intro A; rfl
  | input i => intro A; simp [Expr.eval,Expr.support]
  | conj p q hp hq => exact feature_supported_and hp hq
  | disj p q hp hq => exact feature_supported_or hp hq

theorem Expr.eval_empty (e : Expr ι) : e.eval ∅ = false := by
  induction e <;> simp_all [Expr.eval]

theorem Expr.readOnce_rectangle (e : Expr ι) (h : e.ReadOnce) :
    MintermRectangle e.eval := by
  induction e with
  | zero =>
    intro A B C hA hB hC hsub hint
    have hf : false = true := hA.1
    contradiction
  | input i => exact minterm_rectangle_literal i
  | conj p q hp hq =>
    exact minterm_rectangle_and p.eval_monotone q.eval_monotone
      p.eval_supported q.eval_supported h.2.2 (hp h.1) (hq h.2.1)
  | disj p q hp hq =>
    exact minterm_rectangle_or p.eval_monotone q.eval_monotone
      p.eval_supported q.eval_supported h.2.2 (hp h.1) (hq h.2.1)

theorem Expr.readOnce_longInactive (e : Expr ι) (h : e.ReadOnce) :
    LongMintermInactive e.eval := by
  induction e with
  | zero =>
    intro A hA hlarge
    have hf : false = true := hA.1
    contradiction
  | input i => exact long_minterm_inactive_literal i
  | conj p q hp hq =>
    exact long_minterm_inactive_and p.eval_monotone q.eval_monotone
      p.eval_supported q.eval_supported h.2.2 p.eval_empty q.eval_empty
  | disj p q hp hq =>
    exact long_minterm_inactive_or p.eval_supported q.eval_supported h.2.2
      (hp h.1) (hq h.2.1)

theorem Expr.readOnce_quadratic (e : Expr ι) (hr : e.ReadOnce)
    (h1 : ∀ i, e.eval {i} = false)
    (ha : ∀ i ∈ e.support, QuadraticActive e.eval i)
    {A : Finset ι} (hA : Minterm e.eval A) : A.card = 2 :=
  e.readOnce_longInactive hr |>.quadratic e.eval_supported e.eval_empty h1 ha hA

theorem Expr.mem_support_iff_occurrences (e : Expr ι) (i : ι) :
    i ∈ e.support ↔ 0 < e.occurrences i := by
  induction e with
  | zero => simp [Expr.support,Expr.occurrences]
  | input j => by_cases h : i = j <;> simp [Expr.support,Expr.occurrences,h]
  | conj p q hp hq =>
    simp only [Expr.support,Finset.mem_union,Expr.occurrences,hp,hq]
    omega
  | disj p q hp hq =>
    simp only [Expr.support,Finset.mem_union,Expr.occurrences,hp,hq]
    omega

theorem occurrences_sum_le_one_of_disjoint {p q : Expr ι}
    (hp : ∀ i, p.occurrences i ≤ 1) (hq : ∀ i, q.occurrences i ≤ 1)
    (hd : Disjoint p.support q.support) (i : ι) :
    p.occurrences i + q.occurrences i ≤ 1 := by
  have hpi := hp i
  have hqi := hq i
  by_cases hz : p.occurrences i = 0
  · omega
  · have hip := (p.mem_support_iff_occurrences i).mpr (by omega)
    have hqz : q.occurrences i = 0 := by
      by_contra h
      exact Finset.disjoint_left.mp hd hip
        ((q.mem_support_iff_occurrences i).mpr (by omega))
    omega

theorem disjoint_of_occurrences_sum_le_one {p q : Expr ι}
    (h : ∀ i, p.occurrences i + q.occurrences i ≤ 1) :
    Disjoint p.support q.support := by
  apply Finset.disjoint_left.mpr
  intro i hip hiq
  have hp := (p.mem_support_iff_occurrences i).mp hip
  have hq := (q.mem_support_iff_occurrences i).mp hiq
  have hi := h i
  omega

theorem Expr.readOnce_iff_occurrences (e : Expr ι) :
    e.ReadOnce ↔ ∀ i, e.occurrences i ≤ 1 := by
  induction e with
  | zero => simp [Expr.ReadOnce,Expr.occurrences]
  | input j =>
    constructor
    · intro h i
      by_cases hij : i = j <;> simp [Expr.occurrences,hij]
    · intro h
      trivial
  | conj p q hp hq =>
    constructor
    · intro h i
      exact occurrences_sum_le_one_of_disjoint (hp.mp h.1) (hq.mp h.2.1) h.2.2 i
    · intro h
      have hsum : ∀ i, p.occurrences i + q.occurrences i ≤ 1 := h
      exact ⟨hp.mpr (fun i => by have hi := hsum i; omega),
        hq.mpr (fun i => by have hi := hsum i; omega),
        disjoint_of_occurrences_sum_le_one hsum⟩
  | disj p q hp hq =>
    constructor
    · intro h i
      exact occurrences_sum_le_one_of_disjoint (hp.mp h.1) (hq.mp h.2.1) h.2.2 i
    · intro h
      have hsum : ∀ i, p.occurrences i + q.occurrences i ≤ 1 := h
      exact ⟨hp.mpr (fun i => by have hi := hsum i; omega),
        hq.mpr (fun i => by have hi := hsum i; omega),
        disjoint_of_occurrences_sum_le_one hsum⟩

def Expr.erase (z : ι) : Expr ι → Expr ι
  | .zero => .zero
  | .input i => if i = z then .zero else .input i
  | .conj p q => .conj (p.erase z) (q.erase z)
  | .disj p q => .disj (p.erase z) (q.erase z)

theorem Expr.erase_occurrences (e : Expr ι) (z i : ι) :
    (e.erase z).occurrences i = if i = z then 0 else e.occurrences i := by
  induction e with
  | zero => simp [Expr.erase,Expr.occurrences]
  | input j =>
    by_cases hj : j = z
    · subst j
      by_cases hi : i = z <;> simp [Expr.erase,Expr.occurrences,hi]
    · by_cases hi : i = z
      · subst i
        have hne : z ≠ j := Ne.symm hj
        simp [Expr.erase,Expr.occurrences,hj,hne]
      · simp [Expr.erase,Expr.occurrences,hj,hi]
  | conj p q hp hq =>
    simp only [Expr.erase,Expr.occurrences,hp,hq]
    by_cases hi : i = z <;> simp [hi]
  | disj p q hp hq =>
    simp only [Expr.erase,Expr.occurrences,hp,hq]
    by_cases hi : i = z <;> simp [hi]

theorem Expr.erase_readOnce (e : Expr ι) (z : ι)
    (h : ∀ i, i ≠ z → e.occurrences i ≤ 1) : (e.erase z).ReadOnce := by
  apply (Expr.readOnce_iff_occurrences (e.erase z)).mpr
  intro i
  rw [e.erase_occurrences z i]
  by_cases hi : i = z
  · simp [hi]
  · simpa [hi] using h i hi

theorem Expr.erase_eval (e : Expr ι) (z : ι) (S : Finset ι) :
    (e.erase z).eval S = e.eval (S.erase z) := by
  induction e with
  | zero => rfl
  | input i =>
    by_cases hi : i = z
    · subst i
      simp [Expr.erase,Expr.eval]
    · simp [Expr.erase,Expr.eval,hi]
  | conj p q hp hq => simp only [Expr.erase,Expr.eval,hp,hq]
  | disj p q hp hq => simp only [Expr.erase,Expr.eval,hp,hq]

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem quadraticActive_pair_witness {f : Finset ι → Bool} {S : Finset ι}
    (hs : FeatureSupported f S) {i : ι} (h : QuadraticActive f i) :
    ∃ j ∈ S, i ≠ j ∧ f {i,j} = true := by
  obtain ⟨T,hT,hcard,hi⟩ := h
  obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp hcard
  have hsub := hT.subset_support hs
  have haT : a ∈ T := by simp [he]
  have hbT : b ∈ T := by simp [he]
  rw [he] at hi
  rcases Finset.mem_insert.mp hi with hia | hib
  · subst i
    exact ⟨b,hsub hbT,hab,he ▸ hT.1⟩
  · have hib' := Finset.mem_singleton.mp hib
    subst i
    refine ⟨a,hsub haT,Ne.symm hab,?_⟩
    simpa only [he,Finset.pair_comm] using hT.1

theorem minterm_card_two_of_le {f : Finset ι → Bool} {A : Finset ι}
    (h0 : f ∅ = false) (h1 : ∀ i, f {i} = false)
    (hA : Minterm f A) (hsmall : A.card ≤ 2) : A.card = 2 := by
  have hpos := Finset.card_pos.mpr (minterm_nonempty_of_zero h0 hA)
  have hne : A.card ≠ 1 := by
    intro hc
    obtain ⟨i,he⟩ := Finset.card_eq_one.mp hc
    have ht := hA.1
    simpa [he,h1] using ht
  omega

theorem one_overlap_of_other_counts (p q : Expr ι) (z : ι)
    (h : ∀ i, i ≠ z → p.occurrences i + q.occurrences i ≤ 1) :
    ∀ i ∈ p.support, i ∈ q.support → i = z := by
  intro i hip hiq
  by_contra hiz
  have hp := (p.mem_support_iff_occurrences i).mp hip
  have hq := (q.mem_support_iff_occurrences i).mp hiq
  have hi := h i hiz
  omega

theorem disjoint_of_one_overlap_not_both (p q : Expr ι) (z : ι)
    (h : ∀ i ∈ p.support, i ∈ q.support → i = z)
    (hb : ¬ (z ∈ p.support ∧ z ∈ q.support)) : Disjoint p.support q.support := by
  apply Finset.disjoint_left.mpr
  intro i hip hiq
  have hiz := h i hip hiq
  exact hb ⟨hiz ▸ hip,hiz ▸ hiq⟩

theorem readOnce_children_of_twice (p q : Expr ι) (z : ι)
    (hz : p.occurrences z + q.occurrences z ≤ 2)
    (ho : ∀ i, i ≠ z → p.occurrences i + q.occurrences i ≤ 1)
    (hb : z ∈ p.support ∧ z ∈ q.support) : p.ReadOnce ∧ q.ReadOnce := by
  have hpz := (p.mem_support_iff_occurrences z).mp hb.1
  have hqz := (q.mem_support_iff_occurrences z).mp hb.2
  constructor
  · apply (p.readOnce_iff_occurrences).mpr
    intro i
    by_cases hiz : i = z
    · subst i; omega
    · have hi := ho i hiz; omega
  · apply (q.readOnce_iff_occurrences).mpr
    intro i
    by_cases hiz : i = z
    · subst i; omega
    · have hi := ho i hiz; omega

theorem one_overlap_and_quadratic (p q : Expr ι) (z : ι)
    (hp : p.ReadOnce) (hq : q.ReadOnce)
    (hb : z ∈ p.support ∧ z ∈ q.support)
    (hi : ∀ i ∈ p.support, i ∈ q.support → i = z)
    (h1 : ∀ i, (p.eval {i} && q.eval {i}) = false)
    (ha : ∀ i ∈ p.support ∪ q.support,
      QuadraticActive (fun X => p.eval X && q.eval X) i)
    {T : Finset ι} (hT : Minterm (fun X => p.eval X && q.eval X) T) : T.card = 2 := by
  have hd : Disjoint (p.support.erase z) (q.support.erase z) := by
    apply Finset.disjoint_left.mpr
    intro i hip hiq
    exact (Finset.mem_erase.mp hip).1
      (hi i (Finset.mem_erase.mp hip).2 (Finset.mem_erase.mp hiq).2)
  have hps : FeatureSupported p.eval (insert z (p.support.erase z)) := by
    simpa only [Finset.insert_erase hb.1] using p.eval_supported
  have hqs : FeatureSupported q.eval (insert z (q.support.erase z)) := by
    simpa only [Finset.insert_erase hb.2] using q.eval_supported
  have hU : insert z (p.support.erase z ∪ q.support.erase z) =
      p.support ∪ q.support := by
    rw [Finset.insert_union_distrib,Finset.insert_erase hb.1,Finset.insert_erase hb.2]
  apply repeated_literal_and_quadratic hd (Finset.notMem_erase _ _) (Finset.notMem_erase _ _)
    p.eval_monotone q.eval_monotone hps hqs p.eval_empty q.eval_empty
    (p.readOnce_rectangle hp) (q.readOnce_rectangle hq) (h1 z) ?_ T hT
  intro i hiU
  have hiU' : i ∈ p.support ∪ q.support := hU ▸ hiU
  obtain ⟨j,hj,hij,hpair⟩ := quadraticActive_pair_witness
    (feature_supported_and p.eval_supported q.eval_supported) (ha i hiU')
  exact ⟨j,hU.symm ▸ hj,hij,hpair⟩

theorem Expr.oneRepeated_quadratic (e : Expr ι) (z : ι) :
    e.occurrences z ≤ 2 →
    (∀ i, i ≠ z → e.occurrences i ≤ 1) →
    (∀ i, e.eval {i} = false) →
    (∀ i ∈ e.support, QuadraticActive e.eval i) →
    ∀ A, Minterm e.eval A → A.card = 2 := by
  induction e with
  | zero =>
    intro hz ho h1 ha A hA
    have hf : false = true := hA.1
    contradiction
  | input i =>
    intro hz ho h1 ha A hA
    have hf := h1 i
    simp [Expr.eval] at hf
  | conj p q ihp ihq =>
    intro hz ho h1 ha A hA
    have hi := one_overlap_of_other_counts p q z ho
    by_cases hb : z ∈ p.support ∧ z ∈ q.support
    · obtain ⟨hpr,hqr⟩ := readOnce_children_of_twice p q z hz ho hb
      exact one_overlap_and_quadratic p q z hpr hqr hb hi h1 ha hA
    · have hd := disjoint_of_one_overlap_not_both p q z hi hb
      have hprop := long_minterm_inactive_and p.eval_monotone q.eval_monotone
        p.eval_supported q.eval_supported hd p.eval_empty q.eval_empty
      exact hprop.quadratic (feature_supported_and p.eval_supported q.eval_supported)
        (by simp [Expr.eval_empty]) h1 ha hA
  | disj p q ihp ihq =>
    intro hz ho h1 ha A hA
    have hi := one_overlap_of_other_counts p q z ho
    by_cases hb : z ∈ p.support ∧ z ∈ q.support
    · obtain ⟨hpr,hqr⟩ := readOnce_children_of_twice p q z hz ho hb
      have hsmall := one_overlap_or_minterm_card_le_two p.eval_supported q.eval_supported hi
        (p.readOnce_longInactive hpr) (q.readOnce_longInactive hqr) ha hA
      exact minterm_card_two_of_le (Expr.eval_empty (.disj p q)) h1 hA hsmall
    · have hd := disjoint_of_one_overlap_not_both p q z hi hb
      have hp1 : ∀ i, p.eval {i} = false := by
        intro i
        have hroot := h1 i
        change (p.eval {i} || q.eval {i}) = false at hroot
        cases hv : p.eval {i} <;> simp_all
      have hq1 : ∀ i, q.eval {i} = false := by
        intro i
        have hroot := h1 i
        change (p.eval {i} || q.eval {i}) = false at hroot
        cases hv : q.eval {i} <;> simp_all
      have hpa : ∀ i ∈ p.support, QuadraticActive p.eval i := by
        intro i hip
        exact quadratic_active_or_left q.eval_supported hd hip
          (ha i (Finset.mem_union_left _ hip))
      have hqa : ∀ i ∈ q.support, QuadraticActive q.eval i := by
        intro i hiq
        apply quadratic_active_or_left p.eval_supported hd.symm hiq
        simpa only [Expr.eval,Bool.or_comm] using ha i (Finset.mem_union_right _ hiq)
      change p.occurrences z + q.occurrences z ≤ 2 at hz
      rcases minterm_or_cases hA with hAp | hAq
      · apply ihp (by omega) ?_ hp1 hpa A hAp
        intro i hiz
        have hh := ho i hiz
        change p.occurrences i + q.occurrences i ≤ 1 at hh
        omega
      · apply ihq (by omega) ?_ hq1 hqa A hAq
        intro i hiz
        have hh := ho i hiz
        change p.occurrences i + q.occurrences i ≤ 1 at hh
        omega

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.NeighborhoodBankCounting

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [DecidableEq ι]

def CrossMatching (G : SimpleGraph α) (S T : Finset α) : Prop :=
  (∀ x ∈ S, ∀ y ∈ T, ∀ z ∈ T, G.Adj x y → G.Adj x z → y = z) ∧
  (∀ y ∈ T, ∀ x ∈ S, ∀ z ∈ S, G.Adj y x → G.Adj y z → x = z)

theorem CrossMatching.mono {G : SimpleGraph α} {S T S' T' : Finset α}
    (h : CrossMatching G S T) (hS : S' ⊆ S) (hT : T' ⊆ T) :
    CrossMatching G S' T' := by
  constructor
  · intro x hx y hy z hz hxy hxz
    exact h.1 x (hS hx) y (hT hy) z (hT hz) hxy hxz
  · intro y hy x hx z hz hyx hyz
    exact h.2 y (hT hy) x (hS hx) z (hS hz) hyx hyz

end PEqualNP.Outside.L_meta_1031_aux.NeighborhoodBankCounting

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

open Finset

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def Expr.evalWith : Expr ι → (ι → Bool) → Bool
  | .zero, _ => false
  | .input i, x => x i
  | .conj p q, x => p.evalWith x && q.evalWith x
  | .disj p q, x => p.evalWith x || q.evalWith x

theorem Expr.eval_eq_evalWith (e : Expr ι) (S : Finset ι) :
    e.eval S = e.evalWith (fun i => decide (i ∈ S)) := by
  induction e <;> simp_all [Expr.eval,Expr.evalWith]

theorem Expr.evalWith_congr (e : Expr ι) (x y : ι → Bool) :
    (∀ i ∈ e.support, x i = y i) → e.evalWith x = e.evalWith y := by
  induction e with
  | zero => intro h; rfl
  | input i => intro h; exact h i (by simp [Expr.support])
  | conj p q hp hq =>
    intro h
    simp only [Expr.evalWith]
    rw [hp (fun i hi => h i (mem_union_left _ hi)),
      hq (fun i hi => h i (mem_union_right _ hi))]
  | disj p q hp hq =>
    intro h
    simp only [Expr.evalWith]
    rw [hp (fun i hi => h i (mem_union_left _ hi)),
      hq (fun i hi => h i (mem_union_right _ hi))]

theorem Expr.evalWith_mono (e : Expr ι) (x y : ι → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    e.evalWith x = true → e.evalWith y = true := by
  induction e with
  | zero => intro h; contradiction
  | input i => exact hxy i
  | conj p q hp hq =>
    intro h
    obtain ⟨hpx,hqx⟩ := Bool.and_eq_true_iff.mp h
    exact Bool.and_eq_true_iff.mpr ⟨hp hpx,hq hqx⟩
  | disj p q hp hq =>
    intro h
    rcases Bool.or_eq_true_iff.mp h with hpx | hqx
    · exact Bool.or_eq_true_iff.mpr (Or.inl (hp hpx))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (hq hqx))

theorem Expr.evalWith_eq_eval_filter (e : Expr ι) (x : ι → Bool) :
    e.evalWith x = e.eval (e.support.filter (fun i => x i = true)) := by
  rw [e.eval_eq_evalWith]
  apply e.evalWith_congr
  intro i hi
  cases hx : x i <;> simp [hi,hx]

def Expr.bind (σ : ι → Expr κ) : Expr ι → Expr κ
  | .zero => .zero
  | .input i => σ i
  | .conj p q => .conj (p.bind σ) (q.bind σ)
  | .disj p q => .disj (p.bind σ) (q.bind σ)

theorem Expr.bind_evalWith (e : Expr ι) (σ : ι → Expr κ) (x : κ → Bool) :
    (e.bind σ).evalWith x = e.evalWith (fun i => (σ i).evalWith x) := by
  induction e <;> simp_all [Expr.bind,Expr.evalWith]

theorem Expr.bind_eval (e : Expr ι) (σ : ι → Expr κ) (S : Finset κ) :
    (e.bind σ).eval S = e.evalWith (fun i => (σ i).eval S) := by
  rw [Expr.eval_eq_evalWith,Expr.bind_evalWith]
  apply e.evalWith_congr
  intro i hi
  exact ((σ i).eval_eq_evalWith S).symm

def Expr.plug (e : Expr ι) (z : ι) (h : Expr ι) : Expr ι :=
  e.bind (fun i => if i = z then h else Expr.input i)

def Expr.outer (e : Expr ι) (z : ι) (b : Bool) (S : Finset ι) : Bool :=
  e.evalWith (fun i => if i = z then b else decide (i ∈ S))

theorem Expr.plug_eval (e : Expr ι) (z : ι) (h : Expr ι) (S : Finset ι) :
    (e.plug z h).eval S = e.outer z (h.eval S) S := by
  rw [Expr.plug,Expr.bind_eval]
  apply e.evalWith_congr
  intro i hi
  by_cases hiz : i = z <;> simp [Expr.outer,Expr.eval,hiz]

theorem Expr.outer_false (e : Expr ι) (z : ι) (S : Finset ι) :
    e.outer z false S = e.eval (S.erase z) := by
  rw [Expr.outer,e.eval_eq_evalWith]
  apply e.evalWith_congr
  intro i hi
  by_cases hiz : i = z
  · subst i
    simp
  · simp [hiz]

theorem Expr.outer_supported (e : Expr ι) (z : ι) (b : Bool) :
    FeatureSupported (e.outer z b) (e.support.erase z) := by
  intro S
  apply e.evalWith_congr
  intro i hi
  by_cases hiz : i = z
  · simp [hiz]
  · simp [hiz,hi]

theorem Expr.outer_monotone (e : Expr ι) (z : ι) (b : Bool) :
    FeatureMonotone (e.outer z b) := by
  intro S T hST
  apply e.evalWith_mono
  intro i hi
  by_cases hiz : i = z
  · simpa [hiz] using hi
  · simp only [ite_eq_right hiz] at hi ⊢
    exact decide_eq_true (hST (of_decide_eq_true hi))

theorem Expr.outer_false_erase (e : Expr ι) (z : ι) (S : Finset ι) :
    e.outer z false S = (e.erase z).eval S := by
  rw [e.outer_false,e.erase_eval]

theorem Expr.outer_false_empty (e : Expr ι) (z : ι) : e.outer z false ∅ = false := by
  rw [e.outer_false]
  simp only [Finset.erase_empty,Expr.eval_empty]

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset

open QuadraticExpr

def CutStep (n : ℕ) (C : Circuit) (top z a b : ℕ) : Prop :=
  WireStep n C a b ∧ b ≤ top ∧ a ≠ z

abbrev CutReaches (n : ℕ) (C : Circuit) (top z : ℕ) :=
  Relation.ReflTransGen (CutStep n C top z)

theorem cutReaches_le {n top z a b : ℕ} {C : Circuit}
    (h : CutReaches n C top z a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail h hs ih => exact ih.trans hs.1.1.le

theorem cutReaches_from_stop {n top z b : ℕ} {C : Circuit}
    (h : CutReaches n C top z z b) : z = b := by
  rcases Relation.ReflTransGen.cases_head h with he | ⟨a,ha,_⟩
  · exact he
  · exact (ha.2.2 rfl).elim

theorem cutReaches_mono {n top z top' z' a b : ℕ} {C : Circuit}
    (hstep : ∀ i j, CutStep n C top z i j → CutStep n C top' z' i j)
    (h : CutReaches n C top z a b) : CutReaches n C top' z' a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h hs ih => exact ih.tail (hstep _ _ hs)

theorem cutStep_right_unique {n top z : ℕ} {C : Circuit}
    (hread : ∀ w < top, w ≠ z → (gateReaders C w).card ≤ 1) :
    Relator.RightUnique (CutStep n C top z) := by
  intro a b c hab hac
  obtain ⟨⟨hablt,j,g,hbj,hg,ham⟩,hbtop,haz⟩ := hab
  obtain ⟨⟨_,k,h,hck,hh,han⟩,_,_⟩ := hac
  have hj : j ∈ gateReaders C a := mem_gateReaders.mpr
    ⟨(List.getElem?_eq_some_iff.mp hg).1,by
      rw [gateInputSet_of_get hg]
      simpa using ham⟩
  have hk : k ∈ gateReaders C a := mem_gateReaders.mpr
    ⟨(List.getElem?_eq_some_iff.mp hh).1,by
      rw [gateInputSet_of_get hh]
      simpa using han⟩
  have hjk := Finset.card_le_one_iff.mp
    (hread a (hablt.trans_le hbtop) haz) hj hk
  omega

theorem cut_no_common_source {n top z a b r w : ℕ} {C : Circuit}
    (huniq : Relator.RightUnique (CutStep n C top z))
    (har : CutStep n C top z a r) (hbr : CutStep n C top z b r)
    (hab : a ≠ b) (hwa : CutReaches n C top z w a)
    (hwb : CutReaches n C top z w b) : False := by
  rcases Relation.ReflTransGen.total_of_right_unique huniq hwa hwb with hp | hp
  · rcases Relation.ReflTransGen.cases_head hp with he | ⟨c,hac,hcb⟩
    · exact hab he
    · have hcr : c = r := huniq hac har
      have hle := cutReaches_le hcb
      have hlt := hbr.1.1
      omega
  · rcases Relation.ReflTransGen.cases_head hp with he | ⟨c,hbc,hca⟩
    · exact hab he.symm
    · have hcr : c = r := huniq hbc hbr
      have hle := cutReaches_le hca
      have hlt := har.1.1
      omega

structure CutModel (n : ℕ) (C : Circuit) (top z t : ℕ) where
  expr : Expr ℕ
  gates : Finset ℕ
  nodes : ∀ j ∈ gates,
    j < C.gates.length ∧ n+j ≤ t ∧ n+j ≠ z ∧
      CutReaches n C top z (n+j) t
  halt : t = z → expr = .input z ∧ gates = ∅
  sources : ∀ u ∈ expr.support, u < n ∨ u = z
  source_le : ∀ u ∈ expr.support, u ≤ t
  source_path : ∀ u ∈ expr.support, u ≠ z → CutReaches n C top z u t
  balance : ∀ u, (u < n ∨ u = z) →
    expr.occurrences u = (if u = t then 1 else 0) +
      ∑ j ∈ gates, if u ∈ gateInputSet C j then 1 else 0
  semantics : ∀ (x : Fin n → Bool) (S : Finset ℕ),
    (∀ u ∈ expr.support, decide (u ∈ S) = val C x u) →
    expr.eval S = val C x t

theorem cut_model_exists {n top z : ℕ} {C : Circuit}
    (hC : Monotone2 C) (hc : CleanMono n C)
    (htop : top < n + C.gates.length)
    (huniq : Relator.RightUnique (CutStep n C top z)) :
    ∀ t, t ≤ top → Nonempty (CutModel n C top z t) := by
  classical
  intro t
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro ht
    by_cases hstop : t < n ∨ t = z
    · refine ⟨{
        expr := .input t
        gates := ∅
        nodes := by simp
        halt := ?_
        sources := ?_
        source_le := ?_
        source_path := ?_
        balance := ?_
        semantics := ?_ }⟩
      · intro htz
        subst t
        exact ⟨rfl,rfl⟩
      · intro u hu
        have hut : u = t := by simpa [Expr.support] using hu
        simpa [hut] using hstop
      · intro u hu
        have hut : u = t := by simpa [Expr.support] using hu
        omega
      · intro u hu _
        have hut : u = t := by simpa [Expr.support] using hu
        subst u
        exact Relation.ReflTransGen.refl
      · intro u _
        simp [Expr.occurrences]
      · intro x S hs
        exact hs t (by simp [Expr.support])
    · have htn : n ≤ t := by omega
      have htz : t ≠ z := by tauto
      let j := t - n
      have htj : t = n+j := by dsimp [j]; omega
      have hj : j < C.gates.length := by omega
      let g := C.gates.get ⟨j,hj⟩
      have hg : C.gates[j]? = some g :=
        List.getElem?_eq_some_iff.mpr ⟨hj,rfl⟩
      obtain ⟨a,b,hins,ha,hb,hab⟩ := hc j g hg
      have hat : a < t := by omega
      have hbt : b < t := by omega
      obtain ⟨ma⟩ := ih a hat (hat.le.trans ht)
      obtain ⟨mb⟩ := ih b hbt (hbt.le.trans ht)
      have ham : a ∈ g.inputs := by simp [hins]
      have hbm : b ∈ g.inputs := by simp [hins]
      have har (haz : a ≠ z) : CutStep n C top z a t :=
        ⟨⟨hat,j,g,htj,hg,ham⟩,ht,haz⟩
      have hbr (hbz : b ≠ z) : CutStep n C top z b t :=
        ⟨⟨hbt,j,g,htj,hg,hbm⟩,ht,hbz⟩
      have ha_active {k : ℕ} (hk : k ∈ ma.gates) : a ≠ z := by
        intro he
        rw [(ma.halt he).2] at hk
        simpa using hk
      have hb_active {k : ℕ} (hk : k ∈ mb.gates) : b ≠ z := by
        intro he
        rw [(mb.halt he).2] at hk
        simpa using hk
      have hdis : Disjoint ma.gates mb.gates := by
        apply Finset.disjoint_left.mpr
        intro k hka hkb
        exact cut_no_common_source huniq (har (ha_active hka))
          (hbr (hb_active hkb)) hab (ma.nodes k hka).2.2.2
          (mb.nodes k hkb).2.2.2
      have hjnot : j ∉ ma.gates ∪ mb.gates := by
        intro hm
        rcases Finset.mem_union.mp hm with hm | hm
        · have hh := (ma.nodes j hm).2.1
          omega
        · have hh := (mb.nodes j hm).2.1
          omega
      let e : Expr ℕ := if g.op = .and then
        .conj ma.expr mb.expr else .disj ma.expr mb.expr
      have hes : e.support = ma.expr.support ∪ mb.expr.support := by
        dsimp [e]
        split <;> rfl
      have heo (u : ℕ) : e.occurrences u =
          ma.expr.occurrences u + mb.expr.occurrences u := by
        dsimp [e]
        split <;> rfl
      refine ⟨{
        expr := e
        gates := insert j (ma.gates ∪ mb.gates)
        nodes := ?_
        halt := ?_
        sources := ?_
        source_le := ?_
        source_path := ?_
        balance := ?_
        semantics := ?_ }⟩
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact ⟨hj,by omega,by omega,by
            simpa only [htj] using
              (Relation.ReflTransGen.refl : CutReaches n C top z t t)⟩
        · rcases Finset.mem_union.mp hk with hk | hk
          · obtain ⟨hkg,hkle,hkz,hkp⟩ := ma.nodes k hk
            exact ⟨hkg,hkle.trans hat.le,hkz,hkp.tail (har (ha_active hk))⟩
          · obtain ⟨hkg,hkle,hkz,hkp⟩ := mb.nodes k hk
            exact ⟨hkg,hkle.trans hbt.le,hkz,hkp.tail (hbr (hb_active hk))⟩
      · exact fun he => (htz he).elim
      · intro u hu
        rw [hes] at hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact ma.sources u hu
        · exact mb.sources u hu
      · intro u hu
        rw [hes] at hu
        rcases Finset.mem_union.mp hu with hu | hu
        · exact (ma.source_le u hu).trans hat.le
        · exact (mb.source_le u hu).trans hbt.le
      · intro u hu huz
        rw [hes] at hu
        rcases Finset.mem_union.mp hu with hu | hu
        · have haz : a ≠ z := by
            intro he
            rw [(ma.halt he).1] at hu
            have huz' : u = z := by simpa [Expr.support] using hu
            exact huz huz'
          exact (ma.source_path u hu huz).tail (har haz)
        · have hbz : b ≠ z := by
            intro he
            rw [(mb.halt he).1] at hu
            have huz' : u = z := by simpa [Expr.support] using hu
            exact huz huz'
          exact (mb.source_path u hu huz).tail (hbr hbz)
      · intro u hu
        have hut : u ≠ t := by rcases hu with hu | rfl <;> omega
        have hgate : (if u ∈ gateInputSet C j then 1 else 0) =
            (if u = a then 1 else 0) + (if u = b then 1 else 0) := by
          rw [gateInputSet_of_get hg]
          by_cases hua : u = a
          · subst u
            simp [hins,hab]
          · by_cases hub : u = b
            · subst u
              simp [hins,Ne.symm hab]
            · simp [hins,hua,hub]
        rw [heo,ma.balance u hu,mb.balance u hu]
        rw [Finset.sum_insert hjnot,Finset.sum_union hdis]
        rw [if_neg hut,hgate]
        omega
      · intro x S hs
        have hsa : ∀ u ∈ ma.expr.support, decide (u ∈ S) = val C x u := by
          intro u hu
          exact hs u (by rw [hes]; exact Finset.mem_union_left _ hu)
        have hsb : ∀ u ∈ mb.expr.support, decide (u ∈ S) = val C x u := by
          intro u hu
          exact hs u (by rw [hes]; exact Finset.mem_union_right _ hu)
        have hop := (hC g (List.mem_of_getElem? hg)).1
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · simp [e,hop,Expr.eval,ma.semantics x S hsa,mb.semantics x S hsb,
            htj,val_gate C x hg,hins,GateOp.eval,operand,ha,hb]
        · simp [e,hop,Expr.eval,ma.semantics x S hsa,mb.semantics x S hsb,
            htj,val_gate C x hg,hins,GateOp.eval,operand,ha,hb]

theorem CutModel.reader_bound {n top z t u : ℕ} {C : Circuit}
    (m : CutModel n C top z t) (hu : u < n ∨ u = z) (hut : u ≠ t) :
    m.expr.occurrences u ≤ (gateReaders C u).card := by
  classical
  rw [m.balance u hu,if_neg hut,zero_add]
  have hcard : (∑ j ∈ m.gates, if u ∈ gateInputSet C j then 1 else 0) =
      (m.gates.filter (fun j => u ∈ gateInputSet C j)).card := by
    simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [hcard]
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hj,huj⟩ := Finset.mem_filter.mp hj
  exact mem_gateReaders.mpr ⟨(m.nodes j hj).1,huj⟩

theorem CutModel.boundary_root_count {n top z t : ℕ} {C : Circuit}
    (m : CutModel n C top z t) (ht : t < n ∨ t = z) :
    m.expr.occurrences t = 1 := by
  classical
  rcases ht with ht | ht
  · have hnil : m.gates = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hle := (m.nodes j hj).2.1
      omega
    simpa [hnil] using m.balance t (Or.inl ht)
  · rw [(m.halt ht).1]
    simp [Expr.occurrences,ht]

theorem CutModel.readOnce_of_earlier_readers {n top z t : ℕ} {C : Circuit}
    (m : CutModel n C top z t) (htz : t < z)
    (hread : ∀ u < t, (gateReaders C u).card ≤ 1) : m.expr.ReadOnce := by
  apply (Expr.readOnce_iff_occurrences m.expr).mpr
  intro u
  by_cases hu : u ∈ m.expr.support
  · have hul := m.source_le u hu
    have huraw : u < n := by
      rcases m.sources u hu with h | h
      · exact h
      · omega
    by_cases hut : u = t
    · subst u
      exact (m.boundary_root_count (Or.inl huraw)).le
    · exact (m.reader_bound (Or.inl huraw) hut).trans (hread u (by omega))
  · by_contra hn
    exact hu ((m.expr.mem_support_iff_occurrences u).mpr (by omega))

theorem CutModel.evalWith {n top z t : ℕ} {C : Circuit}
    (m : CutModel n C top z t) (x : Fin n → Bool) :
    m.expr.evalWith (val C x) = val C x t := by
  rw [m.expr.evalWith_eq_eval_filter]
  apply m.semantics
  intro u hu
  cases hv : val C x u <;> simp [hu,hv]

theorem wire_readOnce_expression {n t : ℕ} {C : Circuit}
    (hC : Monotone2 C) (hc : CleanMono n C)
    (ht : t < n + C.gates.length)
    (hread : ∀ w < t, (gateReaders C w).card ≤ 1) :
    ∃ e : Expr ℕ, e.ReadOnce ∧ e.support ⊆ range n ∧
      ∀ x : Fin n → Bool, e.evalWith (val C x) = val C x t := by
  classical
  have huniq : Relator.RightUnique (CutStep n C t (t+1)) :=
    cutStep_right_unique (fun w hw _ => hread w hw)
  obtain ⟨m⟩ := cut_model_exists hC hc ht huniq t le_rfl
  refine ⟨m.expr,m.readOnce_of_earlier_readers (by omega) hread,?_,m.evalWith⟩
  intro u hu
  have hul := m.source_le u hu
  rcases m.sources u hu with huraw | hcut
  · exact Finset.mem_range.mpr huraw
  · omega

theorem one_shared_wire_expression {n z : ℕ} {C : Circuit}
    (hC : Monotone2 C) (hc : CleanMono n C)
    (hlast : C.output + 1 = n + C.gates.length)
    (hz : z < C.output) (hzread : (gateReaders C z).card ≤ 2)
    (hread : ∀ w < C.output, w ≠ z → (gateReaders C w).card ≤ 1) :
    ∃ inner outer : Expr ℕ,
      inner.ReadOnce ∧ inner.support ⊆ range n ∧
      outer.support ⊆ insert z (range n) ∧
      outer.occurrences z ≤ 2 ∧
      (∀ u, u ≠ z → outer.occurrences u ≤ 1) ∧
      Disjoint inner.support (outer.support.erase z) ∧
      (∀ x : Fin n → Bool, inner.evalWith (val C x) = val C x z) ∧
      (∀ x : Fin n → Bool, outer.evalWith (val C x) = val C x C.output) := by
  classical
  have hout : C.output < n + C.gates.length := by omega
  have hzin : z < n + C.gates.length := by omega
  have hinnerread : ∀ w < z, (gateReaders C w).card ≤ 1 := by
    intro w hw
    exact hread w (by omega) (by omega)
  have hiuniq : Relator.RightUnique (CutStep n C z (z+1)) :=
    cutStep_right_unique (fun w hw _ => hinnerread w hw)
  have houniq : Relator.RightUnique (CutStep n C C.output z) :=
    cutStep_right_unique hread
  obtain ⟨mi⟩ := cut_model_exists hC hc hzin hiuniq z le_rfl
  obtain ⟨mo⟩ := cut_model_exists hC hc hout houniq C.output le_rfl
  have hisub : mi.expr.support ⊆ range n := by
    intro u hu
    have hul := mi.source_le u hu
    rcases mi.sources u hu with hraw | hcut
    · exact Finset.mem_range.mpr hraw
    · omega
  refine ⟨mi.expr,mo.expr,mi.readOnce_of_earlier_readers (by omega) hinnerread,
    hisub,?_,?_,?_,?_,mi.evalWith,mo.evalWith⟩
  · intro u hu
    rcases mo.sources u hu with hraw | hcut
    · exact Finset.mem_insert_of_mem (Finset.mem_range.mpr hraw)
    · exact Finset.mem_insert.mpr (Or.inl hcut)
  · exact (mo.reader_bound (Or.inr rfl) (by omega)).trans hzread
  · intro u huz
    by_cases hu : u ∈ mo.expr.support
    · have hul := mo.source_le u hu
      have huraw : u < n := (mo.sources u hu).resolve_right huz
      by_cases hut : u = C.output
      · subst u
        exact (mo.boundary_root_count (Or.inl huraw)).le
      · exact (mo.reader_bound (Or.inl huraw) hut).trans
          (hread u (by omega) huz)
    · by_contra hn
      exact hu ((mo.expr.mem_support_iff_occurrences u).mpr (by omega))
  · apply Finset.disjoint_left.mpr
    intro u hui huo
    obtain ⟨huz,huo⟩ := Finset.mem_erase.mp huo
    have hule := mi.source_le u hui
    have hipath := mi.source_path u hui (by omega)
    have hipath' : CutReaches n C C.output z u z := by
      apply cutReaches_mono (top := z) (z := z+1) ?_ hipath
      intro a b hs
      have hslt := hs.1.1
      have hscap := hs.2.1
      exact ⟨hs.1,by omega,by omega⟩
    have hopath := mo.source_path u huo huz
    rcases Relation.ReflTransGen.total_of_right_unique houniq hipath' hopath with hp | hp
    · have he := cutReaches_from_stop hp
      omega
    · have he := cutReaches_le hp
      omega

end PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem Expr.erase_support (e : Expr ι) (z : ι) :
    (e.erase z).support = e.support.erase z := by
  ext i
  rw [(e.erase z).mem_support_iff_occurrences,e.erase_occurrences]
  by_cases hiz : i = z
  · simp [hiz]
  · simpa [hiz] using (e.mem_support_iff_occurrences i).symm

theorem Expr.plug_supported (e : Expr ι) (z : ι) (h : Expr ι) :
    FeatureSupported (e.plug z h).eval (h.support ∪ e.support.erase z) := by
  intro S
  rw [e.plug_eval,e.plug_eval]
  have he := h.eval_supported.mono
    (show h.support ⊆ h.support ∪ e.support.erase z from subset_union_left) S
  rw [he]
  exact (e.outer_supported z (h.eval (S ∩ (h.support ∪ e.support.erase z)))).mono
    subset_union_right S

theorem Expr.linear_on_support (h : Expr ι)
    (h1 : ∀ i ∈ h.support, h.eval {i} = true) :
    ∀ S, h.eval S = decide (S ∩ h.support).Nonempty := by
  intro S
  by_cases hn : (S ∩ h.support).Nonempty
  · obtain ⟨i,hi⟩ := hn
    have ht := h.eval_monotone {i} S
      (singleton_subset_iff.mpr (mem_inter.mp hi).1) (h1 i (mem_inter.mp hi).2)
    simp [ht,show (S ∩ h.support).Nonempty from ⟨i,hi⟩]
  · have he : S ∩ h.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [h.eval_supported S,he,h.eval_empty]
    simp

theorem Expr.missing_singleton_outer_atom (e h : Expr ι) (z : ι)
    (hd : Disjoint h.support (e.support.erase z))
    (h1 : ∀ i, (e.plug z h).eval {i} = false)
    {i : ι} (hi : i ∈ h.support) (hmissing : h.eval {i} = false)
    (hactive : QuadraticActive (e.plug z h).eval i) : e.outer z true ∅ = true := by
  obtain ⟨j,hj,hij,hpair⟩ := quadraticActive_pair_witness (e.plug_supported z h) hactive
  have hiY : i ∉ e.support.erase z := fun hm => Finset.disjoint_left.mp hd hi hm
  by_cases hjX : j ∈ h.support
  · have hjY : j ∉ e.support.erase z := fun hm => Finset.disjoint_left.mp hd hjX hm
    have ho (b : Bool) : e.outer z b {i,j} = e.outer z b ∅ := by
      rw [feature_supported_pair_left_outside (e.outer_supported z b) hiY,
        feature_supported_singleton_outside (e.outer_supported z b) hjY]
    rw [e.plug_eval,ho] at hpair
    cases hb : h.eval {i,j} with
    | false => rw [hb,e.outer_false_empty] at hpair; contradiction
    | true => simpa only [hb] using hpair
  · have hj0 : h.eval {j} = false := by
      rw [feature_supported_singleton_outside h.eval_supported hjX,h.eval_empty]
    have hp0 : h.eval {i,j} = false := by
      rw [Finset.pair_comm,feature_supported_pair_left_outside h.eval_supported hjX,hmissing]
    have hs := h1 j
    rw [e.plug_eval,hj0] at hs
    rw [e.plug_eval,hp0,
      feature_supported_pair_left_outside (e.outer_supported z false) hiY,hs] at hpair
    contradiction

theorem Expr.plug_absorbed (e h : Expr ι) (z : ι)
    (hatom : e.outer z true ∅ = true) (S : Finset ι) :
    (e.plug z h).eval S = (h.eval S || (e.erase z).eval S) := by
  rw [e.plug_eval]
  cases hh : h.eval S with
  | false => simp only [Bool.false_or]; exact e.outer_false_erase z S
  | true =>
    have ht := e.outer_monotone z true ∅ S (empty_subset _) hatom
    simp [ht]

theorem Expr.nonlinear_plug_quadratic (e h : Expr ι) (z : ι)
    (hr : h.ReadOnce)
    (ho : ∀ i, i ≠ z → e.occurrences i ≤ 1)
    (hd : Disjoint h.support (e.support.erase z))
    (h1 : ∀ i, (e.plug z h).eval {i} = false)
    (ha : ∀ i ∈ h.support ∪ e.support.erase z,
      QuadraticActive (e.plug z h).eval i)
    (hm : ∃ i ∈ h.support, h.eval {i} = false)
    {A : Finset ι} (hA : Minterm (e.plug z h).eval A) : A.card = 2 := by
  obtain ⟨i,hi,hif⟩ := hm
  have hatom := e.missing_singleton_outer_atom h z hd h1 hi hif
    (ha i (mem_union_left _ hi))
  let r : Expr ι := .disj h (e.erase z)
  have hrRead : r.ReadOnce := by
    refine ⟨hr,e.erase_readOnce z ho,?_⟩
    rw [e.erase_support]
    exact hd
  have heval : r.eval = (e.plug z h).eval := by
    funext S
    exact (e.plug_absorbed h z hatom S).symm
  have hsupport : r.support = h.support ∪ e.support.erase z := by
    change h.support ∪ (e.erase z).support = h.support ∪ e.support.erase z
    rw [e.erase_support]
  have hr1 : ∀ j, r.eval {j} = false := by
    intro j
    rw [heval]
    exact h1 j
  have hra : ∀ j ∈ r.support, QuadraticActive r.eval j := by
    intro j hj
    rw [heval]
    exact ha j (hsupport ▸ hj)
  apply r.readOnce_quadratic hrRead hr1 hra
  simpa only [heval] using hA

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem Expr.linear_plug_eval_image (e h : Expr ι) (z : ι)
    (hlinear : ∀ S, h.eval S = decide (S ∩ h.support).Nonempty)
    (hd : Disjoint h.support (e.support.erase z))
    {S : Finset ι} (hS : S ⊆ h.support ∪ e.support.erase z) :
    (e.plug z h).eval S =
      e.eval (S.image (fun i => if i ∈ h.support then z else i)) := by
  classical
  rw [e.plug_eval,Expr.outer,e.eval_eq_evalWith]
  apply e.evalWith_congr
  intro i hi
  by_cases hiz : i = z
  · subst i
    simp only [if_pos rfl]
    have he : z ∈ S.image (fun j => if j ∈ h.support then z else j) ↔
        (S ∩ h.support).Nonempty := by
      constructor
      · intro hm
        obtain ⟨j,hj,hjz⟩ := mem_image.mp hm
        by_cases hjX : j ∈ h.support
        · exact ⟨j,mem_inter.mpr ⟨hj,hjX⟩⟩
        · have hjY : j ∈ e.support.erase z :=
            (mem_union.mp (hS hj)).resolve_left hjX
          have hjne : j ≠ z := (mem_erase.mp hjY).1
          simp only [if_neg hjX] at hjz
          exact (hjne hjz).elim
      · rintro ⟨j,hj⟩
        obtain ⟨hjS,hjX⟩ := mem_inter.mp hj
        exact mem_image.mpr ⟨j,hjS,by simp only [if_pos hjX]⟩
    rw [hlinear S]
    simp [he]
  · have hiY : i ∈ e.support.erase z := mem_erase.mpr ⟨hiz,hi⟩
    have hiX : i ∉ h.support := fun hm => disjoint_left.mp hd hm hiY
    have he : i ∈ S.image (fun j => if j ∈ h.support then z else j) ↔ i ∈ S := by
      constructor
      · intro hm
        obtain ⟨j,hj,hji⟩ := mem_image.mp hm
        by_cases hjX : j ∈ h.support
        · simp only [if_pos hjX] at hji
          exact (hiz hji.symm).elim
        · simp only [if_neg hjX] at hji
          exact hji ▸ hj
      · intro hm
        exact mem_image.mpr ⟨i,hm,by simp only [if_neg hiX]⟩
    simp only [if_neg hiz,he]

theorem Expr.linear_plug_quadratic (e h : Expr ι) (z : ι)
    (hz : e.occurrences z ≤ 2)
    (ho : ∀ i, i ≠ z → e.occurrences i ≤ 1)
    (hlinear : ∀ S, h.eval S = decide (S ∩ h.support).Nonempty)
    (hd : Disjoint h.support (e.support.erase z))
    (h1 : ∀ i, (e.plug z h).eval {i} = false)
    (ha : ∀ i ∈ h.support ∪ e.support.erase z,
      QuadraticActive (e.plug z h).eval i)
    {A : Finset ι} (hA : Minterm (e.plug z h).eval A) : A.card = 2 := by
  classical
  by_cases hempty : h.support = ∅
  · have heval (S : Finset ι) : (e.plug z h).eval S = (e.erase z).eval S := by
      have hh : h.eval S = false := by
        rw [hlinear S,hempty]
        simp
      rw [e.plug_eval,hh,e.outer_false_erase]
    have hfun : (e.plug z h).eval = (e.erase z).eval := funext heval
    have he1 : ∀ i, (e.erase z).eval {i} = false := by
      intro i
      rw [← heval {i}]
      exact h1 i
    have hea : ∀ i ∈ (e.erase z).support, QuadraticActive (e.erase z).eval i := by
      intro i hi
      rw [e.erase_support] at hi
      simpa only [hfun] using ha i (mem_union_right h.support hi)
    exact (e.erase z).readOnce_quadratic (e.erase_readOnce z ho) he1 hea
      (by simpa only [hfun] using hA)
  · obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let ρ : ι → ι := fun i => if i ∈ h.support then z else i
    have hρX : ∀ i ∈ h.support, ρ i = z := by
      intro i hi
      simp only [ρ,if_pos hi]
    have hρY : ∀ i ∈ e.support.erase z, ρ i = i := by
      intro i hi
      have hiX : i ∉ h.support := fun hm => disjoint_left.mp hd hm hi
      simp only [ρ,if_neg hiX]
    have heval (S : Finset ι) (hS : S ⊆ h.support ∪ e.support.erase z) :
        (e.plug z h).eval S = e.eval (S.image ρ) :=
      e.linear_plug_eval_image h z hlinear hd hS
    have he1 : ∀ i, e.eval {i} = false := by
      intro i
      by_cases hiz : i = z
      · subst i
        have hh := h1 x
        rw [heval {x} (singleton_subset_iff.mpr (mem_union_left _ hx))] at hh
        simpa only [image_singleton,hρX x hx] using hh
      · by_cases hi : i ∈ e.support
        · have hiY : i ∈ e.support.erase z := mem_erase.mpr ⟨hiz,hi⟩
          have hh := h1 i
          rw [heval {i} (singleton_subset_iff.mpr (mem_union_right _ hiY))] at hh
          simpa only [image_singleton,hρY i hiY] using hh
        · rw [feature_supported_singleton_outside e.eval_supported hi,e.eval_empty]
    have hmapactive : ∀ i ∈ h.support ∪ e.support.erase z,
        QuadraticActive e.eval (ρ i) := by
      intro i hi
      obtain ⟨j,hj,hij,hpair⟩ := quadraticActive_pair_witness
        (e.plug_supported z h) (ha i hi)
      have hsub : ({i,j} : Finset ι) ⊆ h.support ∪ e.support.erase z :=
        insert_subset_iff.mpr ⟨hi,singleton_subset_iff.mpr hj⟩
      rw [heval {i,j} hsub] at hpair
      have hpair' : e.eval {ρ i,ρ j} = true := by
        simpa only [image_insert,image_singleton] using hpair
      have hne : ρ i ≠ ρ j := by
        intro he
        simpa [he,he1 (ρ j)] using hpair'
      refine ⟨{ρ i,ρ j},feature_minterm_pair e.eval_monotone
        (he1 (ρ i)) (he1 (ρ j)) hpair',?_,?_⟩
      · simp [hne]
      · simp
    have hea : ∀ i ∈ e.support, QuadraticActive e.eval i := by
      intro i hi
      by_cases hiz : i = z
      · subst i
        simpa only [hρX x hx] using hmapactive x (mem_union_left _ hx)
      · have hiY : i ∈ e.support.erase z := mem_erase.mpr ⟨hiz,hi⟩
        simpa only [hρY i hiY] using hmapactive i (mem_union_right _ hiY)
    have hequad := e.oneRepeated_quadratic z hz ho he1 hea
    have hAsub : A ⊆ h.support ∪ e.support.erase z :=
      hA.subset_support (e.plug_supported z h)
    have himage : e.eval (A.image ρ) = true := by
      rw [← heval A hAsub]
      exact hA.1
    obtain ⟨T,hTsub,hT⟩ := feature_exists_minterm_subset e.eval himage
    obtain ⟨a,b,hab,hTab⟩ := card_eq_two.mp (hequad T hT)
    have haimage : a ∈ A.image ρ := hTsub (by simp [hTab])
    have hbimage : b ∈ A.image ρ := hTsub (by simp [hTab])
    obtain ⟨u,hu,hua⟩ := mem_image.mp haimage
    obtain ⟨v,hv,hvb⟩ := mem_image.mp hbimage
    have huv : u ≠ v := by
      intro he
      exact hab (hua.symm.trans ((congrArg ρ he).trans hvb))
    have hpairsub : ({u,v} : Finset ι) ⊆ A :=
      insert_subset_iff.mpr ⟨hu,singleton_subset_iff.mpr hv⟩
    have hpair : (e.plug z h).eval {u,v} = true := by
      rw [heval {u,v} (hpairsub.trans hAsub)]
      simpa only [image_insert,image_singleton,hua,hvb,hTab] using hT.1
    have heq : ({u,v} : Finset ι) = A := hA.2 {u,v} hpairsub hpair
    rw [← heq]
    simp [huv]

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem Expr.sharedReadOnce_quadratic (e h : Expr ι) (z : ι)
    (hr : h.ReadOnce) (hz : e.occurrences z ≤ 2)
    (ho : ∀ i, i ≠ z → e.occurrences i ≤ 1)
    (hd : Disjoint h.support (e.support.erase z))
    (h1 : ∀ i, (e.plug z h).eval {i} = false)
    (ha : ∀ i ∈ h.support ∪ e.support.erase z,
      QuadraticActive (e.plug z h).eval i) :
    ∀ A, Minterm (e.plug z h).eval A → A.card = 2 := by
  classical
  by_cases hs : ∀ i ∈ h.support, h.eval {i} = true
  · intro A hA
    exact e.linear_plug_quadratic h z hz ho (h.linear_on_support hs) hd h1 ha hA
  · push_neg at hs
    obtain ⟨i,hi,hnot⟩ := hs
    have hf : h.eval {i} = false := by
      cases he : h.eval {i} with
      | false => rfl
      | true => exact (hnot he).elim
    intro A hA
    exact e.nonlinear_plug_quadratic h z hr ho hd h1 ha ⟨i,hi,hf⟩ hA

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset

open QuadraticExpr

def inputOfSet (n : ℕ) (S : Finset ℕ) : Fin n → Bool :=
  fun u => decide (u.val ∈ S)

noncomputable def activeInputSet {n : ℕ} (x : Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun u => x u = true)).image Fin.val

theorem mem_activeInputSet {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    u.val ∈ activeInputSet x ↔ x u = true := by
  classical
  constructor
  · intro hu
    obtain ⟨v,hv,hvu⟩ := Finset.mem_image.mp hu
    have he : v = u := Fin.ext hvu
    subst v
    exact (Finset.mem_filter.mp hv).2
  · intro hu
    exact Finset.mem_image.mpr ⟨u,Finset.mem_filter.mpr ⟨Finset.mem_univ u,hu⟩,rfl⟩

theorem activeInputSet_subset_range {n : ℕ} (x : Fin n → Bool) :
    activeInputSet x ⊆ range n := by
  classical
  intro a ha
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_range.mpr u.isLt

theorem inputOfSet_activeInputSet {n : ℕ} (x : Fin n → Bool) :
    inputOfSet n (activeInputSet x) = x := by
  funext u
  cases hx : x u <;> simp [inputOfSet,mem_activeInputSet,hx]

theorem inputOfSet_singleton {n : ℕ} (u : Fin n) :
    inputOfSet n {u.val} = singletonInput u := by
  funext i
  simp [inputOfSet,singletonInput,Fin.ext_iff]

theorem inputOfSet_pair {n : ℕ} (u v : Fin n) :
    inputOfSet n {u.val,v.val} = pairInput u v := by
  funext i
  simp [inputOfSet,pairInput,Fin.ext_iff]

theorem raw_wire_eval {n t : ℕ} {C : Circuit} (e : Expr ℕ)
    (hraw : e.support ⊆ range n)
    (hmodel : ∀ x : Fin n → Bool, e.evalWith (val C x) = val C x t)
    (S : Finset ℕ) : e.eval S = val C (inputOfSet n S) t := by
  rw [e.eval_eq_evalWith]
  calc
    e.evalWith (fun i => decide (i ∈ S)) =
        e.evalWith (val C (inputOfSet n S)) := by
      apply e.evalWith_congr
      intro u hu
      have hun : u < n := Finset.mem_range.mp (hraw hu)
      exact (val_input C (inputOfSet n S) ⟨u,hun⟩).symm
    _ = val C (inputOfSet n S) t := hmodel _

theorem raw_plug_eval {n z : ℕ} {C : Circuit} (outer inner : Expr ℕ)
    (hiraw : inner.support ⊆ range n)
    (horaw : outer.support ⊆ insert z (range n))
    (hi : ∀ x : Fin n → Bool, inner.evalWith (val C x) = val C x z)
    (ho : ∀ x : Fin n → Bool,
      outer.evalWith (val C x) = val C x C.output)
    (S : Finset ℕ) :
    (outer.plug z inner).eval S = C.eval (List.ofFn (inputOfSet n S)) := by
  rw [outer.plug_eval]
  unfold Expr.outer
  calc
    outer.evalWith (fun i => if i = z then inner.eval S else decide (i ∈ S)) =
        outer.evalWith (val C (inputOfSet n S)) := by
      apply outer.evalWith_congr
      intro u hu
      by_cases huz : u = z
      · subst u
        simp only [if_pos rfl]
        exact raw_wire_eval inner hiraw hi S
      · simp only [if_neg huz]
        have hun : u < n := Finset.mem_range.mp
          ((Finset.mem_insert.mp (horaw hu)).resolve_left huz)
        exact (val_input C (inputOfSet n S) ⟨u,hun⟩).symm
    _ = val C (inputOfSet n S) C.output := ho _
    _ = C.eval (List.ofFn (inputOfSet n S)) := rfl

theorem raw_expression_singletons {n : ℕ} {C : Circuit} (e : Expr ℕ)
    (hmodel : ∀ S, e.eval S = C.eval (List.ofFn (inputOfSet n S)))
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false) :
    ∀ u : ℕ, e.eval {u} = false := by
  intro u
  by_cases hun : u < n
  · let i : Fin n := ⟨u,hun⟩
    have hx : inputOfSet n {u} = singletonInput i := inputOfSet_singleton i
    rw [hmodel,hx,hsingle]
  · have hx : inputOfSet n {u} = inputOfSet n ∅ := by
      funext i
      have hiu : i.val ≠ u := by have := i.isLt; omega
      simp [inputOfSet,hiu]
    rw [hmodel,hx,← hmodel ∅,e.eval_empty]

theorem raw_expression_quadratic_active {n : ℕ} {C : Circuit} (e : Expr ℕ)
    (hmodel : ∀ S, e.eval S = C.eval (List.ofFn (inputOfSet n S)))
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false)
    (hpairs : ∀ u : Fin n, ∃ v : Fin n,
      C.eval (List.ofFn (pairInput u v)) = true) :
    ∀ u < n, QuadraticActive e.eval u := by
  intro u hun
  let i : Fin n := ⟨u,hun⟩
  obtain ⟨v,hpair⟩ := hpairs i
  have h1 := raw_expression_singletons e hmodel hsingle
  have hepair : e.eval {u,v.val} = true := by
    rw [hmodel]
    have hx : inputOfSet n {u,v.val} = pairInput i v := inputOfSet_pair i v
    rw [hx]
    exact hpair
  have huv : u ≠ v.val := by
    intro he
    simpa [← he,h1] using hepair
  exact ⟨{u,v.val},feature_minterm_pair e.eval_monotone (h1 u) (h1 v.val) hepair,
    by simp [huv],by simp⟩

theorem expression_accepted_pair {n : ℕ} {C : Circuit} (e : Expr ℕ)
    (hmodel : ∀ S, e.eval S = C.eval (List.ofFn (inputOfSet n S)))
    (hquad : ∀ A, Minterm e.eval A → A.card = 2)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true) :
    ∃ u v : Fin n, u ≠ v ∧ x u = true ∧ x v = true ∧
      C.eval (List.ofFn (pairInput u v)) = true := by
  classical
  have ht : e.eval (activeInputSet x) = true := by
    rw [hmodel,inputOfSet_activeInputSet]
    exact hx
  obtain ⟨A,hAS,hA⟩ := feature_exists_minterm_subset e.eval ht
  obtain ⟨a,b,hab,hAeq⟩ := Finset.card_eq_two.mp (hquad A hA)
  have haS : a ∈ activeInputSet x := hAS (by simp [hAeq])
  have hbS : b ∈ activeInputSet x := hAS (by simp [hAeq])
  have han : a < n := Finset.mem_range.mp (activeInputSet_subset_range x haS)
  have hbn : b < n := Finset.mem_range.mp (activeInputSet_subset_range x hbS)
  let u : Fin n := ⟨a,han⟩
  let v : Fin n := ⟨b,hbn⟩
  refine ⟨u,v,?_,(mem_activeInputSet x u).mp haS,
    (mem_activeInputSet x v).mp hbS,?_⟩
  · intro he
    exact hab (congrArg Fin.val he)
  · have hp := hA.1
    rw [hAeq,hmodel] at hp
    have hi : inputOfSet n {a,b} = pairInput u v := inputOfSet_pair u v
    simpa only [hi] using hp

theorem minimum_one_surplus_accepted_pair {n : ℕ} {C : Circuit}
    (hn : 0 < n) (hmin : IsMinimalMonoCircuit n C)
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false)
    (hpairs : ∀ u : Fin n, ∃ v : Fin n,
      C.eval (List.ofFn (pairInput u v)) = true)
    (hsize : C.gates.length ≤ n)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true) :
    ∃ u v : Fin n, u ≠ v ∧ x u = true ∧ x v = true ∧
      C.eval (List.ofFn (pairInput u v)) = true := by
  classical
  obtain ⟨hc,hlast,_,hcases⟩ := minimum_quadratic_activity_one_surplus
    hn hmin hsingle hpairs hsize
  rcases hcases with ⟨_,hread⟩ | ⟨_,z,hz,hzread,hread⟩
  · obtain ⟨e,hro,hraw,hval⟩ := wire_readOnce_expression hmin.1 hc
      (by omega : C.output < n+C.gates.length) (fun w hw => (hread w hw).le)
    have hmodel : ∀ S, e.eval S = C.eval (List.ofFn (inputOfSet n S)) := by
      intro S
      exact raw_wire_eval e hraw hval S
    have h1 := raw_expression_singletons e hmodel hsingle
    have ha := raw_expression_quadratic_active e hmodel hsingle hpairs
    apply expression_accepted_pair e hmodel ?_ x hx
    intro A hA
    exact e.readOnce_quadratic hro h1
      (fun u hu => ha u (Finset.mem_range.mp (hraw hu))) hA
  · obtain ⟨inner,outer,hro,hiraw,horaw,hzcount,hother,hdis,hival,hoval⟩ :=
      one_shared_wire_expression hmin.1 hc hlast hz hzread.le
        (fun w hw hne => (hread w hw hne).le)
    let e := outer.plug z inner
    have hmodel : ∀ S, e.eval S = C.eval (List.ofFn (inputOfSet n S)) :=
      raw_plug_eval outer inner hiraw horaw hival hoval
    have h1 := raw_expression_singletons e hmodel hsingle
    have ha := raw_expression_quadratic_active e hmodel hsingle hpairs
    have hU : inner.support ∪ outer.support.erase z ⊆ range n := by
      intro u hu
      rcases Finset.mem_union.mp hu with hu | hu
      · exact hiraw hu
      · obtain ⟨huz,hu⟩ := Finset.mem_erase.mp hu
        exact (Finset.mem_insert.mp (horaw hu)).resolve_left huz
    apply expression_accepted_pair e hmodel ?_ x hx
    intro A hA
    exact outer.sharedReadOnce_quadratic inner z hro hzcount hother hdis h1
      (fun u hu => ha u (Finset.mem_range.mp (hU hu))) A hA

end PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Finset

open RelativeForestCore

def acceptedPairGraph (n : ℕ) (C : Circuit) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ C.eval (List.ofFn (pairInput u v)) = true
  symm := by
    constructor
    intro u v h
    refine ⟨Ne.symm h.1,?_⟩
    have he : pairInput v u = pairInput u v := by
      funext i
      simp [pairInput,or_comm]
    rw [he]
    exact h.2
  loopless := by constructor; intro u h; exact h.1 rfl

theorem forestFun0_pair_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u v : Fin n) :
    forestFun0 G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [forestFun0,decide_eq_true_eq]
  constructor
  · rintro (⟨a,ha,_⟩ | ⟨a,b,hab,ha,hb⟩)
    · simpa using ha
    · have ha' : a = u ∨ a = v := of_decide_eq_true ha
      have hb' : b = u ∨ b = v := of_decide_eq_true hb
      rcases ha' with hau | hav
      · subst a
        rcases hb' with hbu | hbv
        · subst b
          exact (hab.ne rfl).elim
        · subst b
          exact hab
      · subst a
        rcases hb' with hbu | hbv
        · subst b
          exact hab.symm
        · subst b
          exact (hab.ne rfl).elim
  · intro huv
    exact Or.inr ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩

theorem monotone_self_size {n : ℕ} {C : Circuit} (hC : Monotone2 C) :
    HasCircuitSize n (fun x => C.eval (List.ofFn x)) C.gates.length := by
  refine ⟨C,?_,le_rfl,fun _ => rfl⟩
  intro g hg
  obtain ⟨hop,hsize⟩ := hC g hg
  refine ⟨?_,hsize⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
  tauto

theorem relative_forest_exact_pairs {n t : ℕ} {C : Circuit}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hC : Monotone2 C) (hforest : G.IsAcyclic) (hvc : HasMinVC H t)
    (hSand : ForestSandwich H G ∅ (fun x => C.eval (List.ofFn x)))
    (hbudget : C.gates.length + 1 ≤ H.edgeFinset.card + t) :
    ∀ u v : Fin n, u ≠ v →
      (C.eval (List.ofFn (pairInput u v)) = true ↔ H.Adj u v) := by
  classical
  let K := acceptedPairGraph n C
  have hHK : H ≤ K := by
    intro u v huv
    exact ⟨huv.ne,hSand.lower _ ((forestFun0_pair_iff H u v).mpr huv)⟩
  have hKG : K ≤ G := by
    intro u v huv
    exact (forestFun0_pair_iff G u v).mp (hSand.upper _ huv.2)
  have hKSand : ForestSandwich K G ∅ (fun x => C.eval (List.ofFn x)) := by
    constructor
    · intro x hx
      rcases of_decide_eq_true hx with ⟨a,ha,_⟩ | ⟨u,v,huv,hxu,hxv⟩
      · simpa using ha
      · have hxy : ∀ i, pairInput u v i = true → x i = true := by
          intro i hi
          rcases (of_decide_eq_true hi : i = u ∨ i = v) with rfl | rfl
          · exact hxu
          · exact hxv
        exact acts_mono hC hxy C.output huv.2
    · exact hSand.upper
  obtain ⟨tK,hvcK⟩ := hasMinVC_exists K
  have hcover : t ≤ tK := by
    obtain ⟨S,hS,hcard⟩ := hvcK.1
    have ht := hvc.2 S (fun u v huv => hS u v (hHK huv))
    simpa only [hcard] using ht
  have hlower := relative_forest_sandwich G K ∅
    (fun x => C.eval (List.ofFn x)) hforest hKG (by simp) hvcK hKSand
    (monotone_self_size hC)
  simp only [Finset.card_empty,zero_add] at hlower
  have hsub : H.edgeFinset ⊆ K.edgeFinset := SimpleGraph.edgeFinset_mono hHK
  have hcards := Finset.card_le_card hsub
  have hedge : H.edgeFinset = K.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  intro u v huv
  constructor
  · intro hp
    have hmem : s(u,v) ∈ K.edgeFinset := SimpleGraph.mem_edgeFinset.mpr ⟨huv,hp⟩
    rw [← hedge] at hmem
    exact SimpleGraph.mem_edgeFinset.mp hmem
  · intro hH
    exact (hHK hH).2

theorem relative_forest_one_surplus_equality {n t : ℕ} {C : Circuit}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hn : 0 < n) (hmin : IsMinimalMonoCircuit n C)
    (hforest : G.IsAcyclic) (hvc : HasMinVC H t)
    (hSand : ForestSandwich H G ∅ (fun x => C.eval (List.ofFn x)))
    (hactive : ∀ u : Fin n, ∃ v : Fin n, H.Adj u v)
    (hbudget : C.gates.length + 1 ≤ H.edgeFinset.card + t)
    (hsize : C.gates.length ≤ n) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = forestFun0 H ∅ x := by
  have hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false := by
    intro u
    exact hSand.false_of_upper _ (forestFun0_singleton_false G ∅ u (by simp))
  have hpairs : ∀ u : Fin n, ∃ v : Fin n,
      C.eval (List.ofFn (pairInput u v)) = true := by
    intro u
    obtain ⟨v,huv⟩ := hactive u
    exact ⟨v,hSand.lower _ ((forestFun0_pair_iff H u v).mpr huv)⟩
  have hexact := relative_forest_exact_pairs G H hmin.1 hforest hvc hSand hbudget
  intro x
  cases hcval : C.eval (List.ofFn x) with
  | false =>
    cases hhval : forestFun0 H ∅ x with
    | false => rfl
    | true =>
      have ht := hSand.lower x hhval
      rw [hcval] at ht
      contradiction
  | true =>
    have htrue : forestFun0 H ∅ x = true := by
      obtain ⟨u,v,huv,hxu,hxv,hpair⟩ :=
        minimum_one_surplus_accepted_pair hn hmin hsingle hpairs hsize x hcval
      apply decide_eq_true
      exact Or.inr ⟨u,v,(hexact u v huv).mp hpair,hxu,hxv⟩
    exact htrue.symm

end PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem one_surplus_accepted_pair {n : ℕ} {C : Circuit}
    (hn : 0 < n) (hC : Monotone2 C)
    (hsingle : ∀ u : Fin n, C.eval (List.ofFn (singletonInput u)) = false)
    (hpairs : ∀ u : Fin n, ∃ v : Fin n,
      C.eval (List.ofFn (pairInput u v)) = true)
    (hsize : C.gates.length ≤ n)
    (x : Fin n → Bool) (hx : C.eval (List.ofFn x) = true) :
    ∃ u v : Fin n, u ≠ v ∧ x u = true ∧ x v = true ∧
      C.eval (List.ofFn (pairInput u v)) = true := by
  obtain ⟨D,hmin,he,hDC,_,_⟩ := exists_minimum_safe_forward_normal
    (fun y : Fin n → Bool => C.eval (List.ofFn y)) C hC (fun _ => rfl)
  have hsingleD : ∀ u : Fin n, D.eval (List.ofFn (singletonInput u)) = false := by
    intro u
    rw [he]
    exact hsingle u
  have hpairsD : ∀ u : Fin n, ∃ v : Fin n,
      D.eval (List.ofFn (pairInput u v)) = true := by
    intro u
    obtain ⟨v,hv⟩ := hpairs u
    exact ⟨v,(he _).trans hv⟩
  have hsizeD : D.gates.length ≤ n := hDC.trans hsize
  obtain ⟨u,v,huv,hxu,hxv,hpair⟩ := minimum_one_surplus_accepted_pair
    hn hmin hsingleD hpairsD hsizeD x ((he x).trans hx)
  exact ⟨u,v,huv,hxu,hxv,(he _).symm.trans hpair⟩

end PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open RelativeForestCore

theorem relative_forest_small_circuit_equality {n t : ℕ} {C : Circuit}
    (G H : SimpleGraph (Fin n)) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hn : 0 < n) (hC : Monotone2 C)
    (hforest : G.IsAcyclic) (hvc : HasMinVC H t)
    (hSand : ForestSandwich H G ∅ (fun x => C.eval (List.ofFn x)))
    (hactive : ∀ u : Fin n, ∃ v : Fin n, H.Adj u v)
    (hbudget : C.gates.length + 1 ≤ H.edgeFinset.card + t)
    (hsize : C.gates.length ≤ n) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = forestFun0 H ∅ x := by
  obtain ⟨D,hmin,he,hDC,_,_⟩ := exists_minimum_safe_forward_normal
    (fun y : Fin n → Bool => C.eval (List.ofFn y)) C hC (fun _ => rfl)
  change D.gates.length ≤ C.gates.length at hDC
  have hSandD : ForestSandwich H G ∅ (fun x => D.eval (List.ofFn x)) := by
    constructor
    · intro x hx
      exact (he x).trans (hSand.lower x hx)
    · intro x hx
      exact hSand.upper x ((he x).symm.trans hx)
  have hD := relative_forest_one_surplus_equality G H hn hmin hforest hvc
    hSandD hactive (by omega) (hDC.trans hsize)
  intro x
  exact (he x).symm.trans (hD x)

end PEqualNP.Outside.L_meta_1031_aux.QuadraticCircuit

