import Mathlib.Combinatorics.SimpleGraph.Star

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

theorem indep_not_adj {G : SimpleGraph α} {I : Finset α}
    (hI : G.IsIndepSet (I : Set α)) {u v : α} (hu : u ∈ I) (hv : v ∈ I) :
    ¬ G.Adj u v := by
  intro h
  exact hI hu hv h.ne h

theorem indep_subset {G : SimpleGraph α} {I U : Finset α}
    (hI : G.IsIndepSet (I : Set α)) (hUI : U ⊆ I) : G.IsIndepSet (U : Set α) := by
  intro u hu v hv hne
  exact hI (hUI hu) (hUI hv) hne

end PEqualNP.Outside.L_meta_1031_aux.RelativeClause

namespace PEqualNP.Outside.L_meta_1031_aux.RelativeClause

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

def TriangleFree (G : SimpleGraph α) : Prop :=
  ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a → False

def FourCycleFree (G : SimpleGraph α) : Prop :=
  ∀ a b c d, a ≠ c → b ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False

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

theorem edge_open_neighborhoods_indep {G : SimpleGraph α}
    (h3 : TriangleFree G) (h4 : FourCycleFree G) {u v : α} (huv : G.Adj u v) :
    G.IsIndepSet ((((neighbors G u).erase v) ∪ ((neighbors G v).erase u) : Finset α) : Set α) := by
  intro a ha b hb hne hab
  change a ∈ (neighbors G u).erase v ∪ (neighbors G v).erase u at ha
  change b ∈ (neighbors G u).erase v ∪ (neighbors G v).erase u at hb
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨hav, hau⟩ := Finset.mem_erase.mp ha
    have hua := mem_neighbors.mp hau
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨_, hbu⟩ := Finset.mem_erase.mp hb
      exact h3 u a b hua hab (mem_neighbors.mp hbu).symm
    · obtain ⟨hbu, hbv⟩ := Finset.mem_erase.mp hb
      exact h4 u a b v hbu.symm hav hua hab (mem_neighbors.mp hbv).symm huv.symm
  · obtain ⟨hau, hav⟩ := Finset.mem_erase.mp ha
    have hva := mem_neighbors.mp hav
    rcases Finset.mem_union.mp hb with hb | hb
    · obtain ⟨hbv, hbu⟩ := Finset.mem_erase.mp hb
      exact h4 v a b u hbv.symm hau hva hab (mem_neighbors.mp hbu).symm huv
    · obtain ⟨_, hbv⟩ := Finset.mem_erase.mp hb
      exact h3 v a b hva hab (mem_neighbors.mp hbv).symm

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

def OwnsPair {n : ℕ} (C : Circuit) (t : ℕ) (u v : Fin n) : Prop :=
  val C (pairInput u v) (n + t) = true ∧
  ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
    Ancestor n C (n + t') (n + t) → val C (pairInput u v) (n + t') = false

theorem ancestor_or_trace {n : ℕ} {C : Circuit} (hC : Monotone2 C)
    {root : ℕ} {x y z : Fin n → Bool}
    (hsource : ∀ i, x i = true → y i = true ∨ z i = true)
    (hdead : ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
      Ancestor n C (n + t) root → val C x (n + t) = false) :
    ∀ w, Ancestor n C w root → val C x w = true →
      val C y w = true ∨ val C z w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hanc hx
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      simpa only [← val_input C x i, ← val_input C y i, ← val_input C z i] using
        hsource i (by simpa only [← val_input C x i] using hx)
    by_cases hgt : n + C.gates.length ≤ w
    · rw [val_beyond C x hgt] at hx
      contradiction
    obtain ⟨p, hp, rfl⟩ : ∃ p, p < C.gates.length ∧ w = n + p :=
      ⟨w - n, by omega, by omega⟩
    let g := C.gates[p]
    have hg : C.gates[p]? = some g := List.getElem?_eq_some_iff.2 ⟨hp, rfl⟩
    have hop := (hC g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with hand | hor
    · have hh := hdead p g hg hand hanc
      rw [hx] at hh
      contradiction
    · rw [val_gate C x hg] at hx
      simp only [hor, GateOp.eval, List.any_map, Function.comp_apply, id,
        List.any_eq_true] at hx
      obtain ⟨a, ha, hax⟩ := hx
      have halt : a < n + p := by
        by_contra hge
        simp [operand, hge] at hax
      have haanc : Ancestor n C a root :=
        (Relation.TransGen.single ⟨halt, p, g, rfl, hg, ha⟩).trans hanc
      have hva : val C x a = true := by simpa [operand, halt] using hax
      have hor_true (q : Fin n → Bool) (hq : val C q a = true) :
          val C q (n + p) = true := by
        rw [val_gate C q hg]
        simp only [hor, GateOp.eval, List.any_map, Function.comp_apply, id,
          List.any_eq_true]
        exact ⟨a, ha, by simp [operand, halt, hq]⟩
      rcases ih a halt haanc hva with hy | hz
      · exact Or.inl (hor_true y hy)
      · exact Or.inr (hor_true z hz)

theorem owned_operand_singleton {n : ℕ} {C : Circuit} (hC : Monotone2 C)
    {t a : ℕ} {g : Gate} (hg : C.gates[t]? = some g) (hand : g.op = GateOp.and)
    (ha : a ∈ g.inputs) {u v : Fin n} (hown : OwnsPair C t u v) :
    a < n + t ∧
      (val C (singletonInput u) a = true ∨ val C (singletonInput v) a = true) := by
  have hax := hown.1
  rw [val_gate C (pairInput u v) hg] at hax
  simp only [hand, GateOp.eval, List.all_map, Function.comp_apply, id,
    List.all_eq_true] at hax
  have hh := hax a ha
  have halt : a < n + t := by
    by_contra hge
    simp [operand, hge] at hh
  refine ⟨halt, ?_⟩
  apply ancestor_or_trace hC (x := pairInput u v) ?_ hown.2 a
    (Relation.TransGen.single ⟨halt, t, g, rfl, hg, ha⟩)
    (by simpa [operand, halt] using hh)
  intro i hi
  simpa only [pairInput, singletonInput, decide_eq_true_eq] using hi

def SafeAt {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val C x w = true →
    ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true

theorem safe_zero_false {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {w : ℕ}
    (hsafe : SafeAt G C w) : val C (fun _ : Fin n => false) w = false := by
  cases h : val C (fun _ : Fin n => false) w with
  | false => rfl
  | true =>
    obtain ⟨i, j, _, hi, _⟩ := hsafe (fun _ => false) h
    cases hi

theorem safe_singleton_false {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit} {w : ℕ}
    (hsafe : SafeAt G C w) (c : Fin n) : val C (singletonInput c) w = false := by
  cases h : val C (singletonInput c) w with
  | false => rfl
  | true =>
    obtain ⟨i, j, hij, hi, hj⟩ := hsafe (singletonInput c) h
    simp only [singletonInput, decide_eq_true_eq] at hi hj
    subst i
    subst j
    exact False.elim (G.loopless.irrefl c hij)

theorem edge_on_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n}
    (h : ∃ i j : Fin n, G.Adj i j ∧ pairInput u v i = true ∧ pairInput u v j = true) :
    G.Adj u v := by
  obtain ⟨i, j, hij, hi, hj⟩ := h
  simp only [pairInput, decide_eq_true_eq] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact False.elim (G.loopless.irrefl _ hij)
  · exact hij
  · exact hij.symm
  · exact False.elim (G.loopless.irrefl _ hij)

theorem safe_and_support_cross {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) {t a b : ℕ} {g : Gate}
    (hg : C.gates[t]? = some g) (hand : g.op = GateOp.and)
    (hins : g.inputs = [a, b]) (ha : a < n + t) (hb : b < n + t)
    (hsafe : SafeAt G C (n + t)) {u v : Fin n}
    (hu : val C (singletonInput u) a = true)
    (hv : val C (singletonInput v) b = true) : G.Adj u v := by
  have hau : val C (pairInput u v) a = true := by
    apply acts_mono hC (x := singletonInput u) (y := pairInput u v) ?_ a hu
    intro i hi
    simp only [singletonInput, decide_eq_true_eq] at hi
    simp [pairInput, hi]
  have hbv : val C (pairInput u v) b = true := by
    apply acts_mono hC (x := singletonInput v) (y := pairInput u v) ?_ b hv
    intro i hi
    simp only [singletonInput, decide_eq_true_eq] at hi
    simp [pairInput, hi]
  apply edge_on_pair (hsafe (pairInput u v) ?_)
  rw [val_gate C (pairInput u v) hg, hand, hins]
  simp [GateOp.eval, operand, ha, hb, hau, hbv]

theorem biclique_one_side_singleton {α : Type} (G : SimpleGraph α)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (A B : α → Prop) (hA : ∃ a, A a) (hB : ∃ b, B b)
    (hcross : ∀ a b, A a → B b → G.Adj a b) :
    (∃ a, ∀ u, A u → u = a) ∨ (∃ b, ∀ v, B v → v = b) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  by_cases hsingle : ∀ u, A u → u = a
  · exact Or.inl ⟨a, hsingle⟩
  push_neg at hsingle
  obtain ⟨u, hu, hua⟩ := hsingle
  refine Or.inr ⟨b, fun v hv => ?_⟩
  have hh := hfour a b u v (hcross a b ha hb) (hcross u b hu hb).symm
    (hcross u v hu hv) (hcross a v ha hv).symm
  exact (hh.resolve_left hua.symm).symm

theorem safe_binary_and_owned_star {n : ℕ} (G : SimpleGraph (Fin n))
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d) {C : Circuit} (hC : Monotone2 C) {t a b : ℕ} {g : Gate}
    (hg : C.gates[t]? = some g) (hand : g.op = GateOp.and) (hins : g.inputs = [a, b])
    (hsafe : SafeAt G C (n + t))
    (hnonempty : ∃ u v : Fin n, G.Adj u v ∧ OwnsPair C t u v) :
    ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → OwnsPair C t u v → u = c ∨ v = c := by
  obtain ⟨u0, v0, _, hown0⟩ := hnonempty
  have hao := owned_operand_singleton hC hg hand (a := a) (by simp [hins]) hown0
  have hbo := owned_operand_singleton hC hg hand (a := b) (by simp [hins]) hown0
  let A := fun u : Fin n => val C (singletonInput u) a = true
  let B := fun u : Fin n => val C (singletonInput u) b = true
  have hA : ∃ u, A u := by rcases hao.2 with h | h; exact ⟨u0, h⟩; exact ⟨v0, h⟩
  have hB : ∃ v, B v := by rcases hbo.2 with h | h; exact ⟨u0, h⟩; exact ⟨v0, h⟩
  have cross : ∀ u v, A u → B v → G.Adj u v := fun u v hu hv =>
    safe_and_support_cross hC hg hand hins hao.1 hbo.1 hsafe hu hv
  rcases biclique_one_side_singleton G hfour A B hA hB cross with
    ⟨c, hc⟩ | ⟨c, hc⟩
  · refine ⟨c, fun u v _ hown => ?_⟩
    have hh := (owned_operand_singleton hC hg hand (a := a) (by simp [hins]) hown).2
    rcases hh with hu | hv
    · exact Or.inl (hc u hu)
    · exact Or.inr (hc v hv)
  · refine ⟨c, fun u v _ hown => ?_⟩
    have hh := (owned_operand_singleton hC hg hand (a := b) (by simp [hins]) hown).2
    rcases hh with hu | hv
    · exact Or.inl (hc u hu)
    · exact Or.inr (hc v hv)

theorem safe_and_owned_star {n : ℕ} (G : SimpleGraph (Fin n))
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d) {C : Circuit} (hC : Monotone2 C) {t : ℕ} {g : Gate}
    (hg : C.gates[t]? = some g) (hand : g.op = GateOp.and)
    (hsafe : SafeAt G C (n + t))
    (hnonempty : ∃ u v : Fin n, G.Adj u v ∧ OwnsPair C t u v) :
    ∃ c : Fin n, ∀ u v : Fin n, G.Adj u v → OwnsPair C t u v → u = c ∨ v = c := by
  have hlen := (hC g (List.mem_of_getElem? hg)).2
  cases hins : g.inputs with
  | nil =>
    have htrue : val C (fun _ : Fin n => false) (n + t) = true := by
      rw [val_gate C (fun _ => false) hg, hand, hins]
      rfl
    have hh := safe_zero_false hsafe
    rw [htrue] at hh
    contradiction
  | cons a rest =>
    cases rest with
    | nil =>
      obtain ⟨u, v, _, hown⟩ := hnonempty
      have hao := owned_operand_singleton hC hg hand (a := a) (by simp [hins]) hown
      obtain ⟨c, hc⟩ : ∃ c : Fin n, val C (singletonInput c) a = true := by
        rcases hao.2 with hu | hv
        · exact ⟨u, hu⟩
        · exact ⟨v, hv⟩
      have htrue : val C (singletonInput c) (n + t) = true := by
        rw [val_gate C (singletonInput c) hg, hand, hins]
        simp [GateOp.eval, operand, hao.1, hc]
      have hh := safe_singleton_false hsafe c
      rw [htrue] at hh
      contradiction
    | cons b tail =>
      have htail : tail.length = 0 := by simpa [hins] using hlen
      have hnil : tail = [] := by simpa using htail
      subst tail
      exact safe_binary_and_owned_star G hfour hC hg hand hins hsafe hnonempty

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

theorem rdel_get_lt (n p a : ℕ) (C : Circuit) (hp : p < C.gates.length)
    (j : ℕ) (hj : j < p) : (rdel n p a C).gates[j]? = C.gates[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]

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

theorem safe_forward_normal_ancestor {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (hN : SafeForwardNormal F C) {a b : ℕ} (hab : Ancestor n C a b) :
    WireSafe F C a → WireSafe F C b := by
  induction hab with
  | single h =>
    intro hs
    obtain ⟨hqb, p, g, rfl, hg, hmem⟩ := h
    exact (hN _ p g hg hmem hqb hs).2
  | tail _ h ih =>
    intro hs
    obtain ⟨hqb, p, g, rfl, hg, hmem⟩ := h
    exact (hN _ p g hg hmem hqb (ih hs)).2

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

noncomputable def graphFn {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

theorem graphFn_true {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :
    graphFn G x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  simp [graphFn]

theorem graphFn_pair {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n} (huv : G.Adj u v) :
    graphFn G (pairInput u v) = true := by
  apply (graphFn_true G _).2
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

def patchGate (C : Circuit) (p : ℕ) (h : Gate) : Circuit :=
  ⟨(C.gates.take p ++ [h]) ++ C.gates.drop (p + 1), C.output⟩

theorem patchGate_length (C : Circuit) (p : ℕ) (h : Gate) (hp : p < C.gates.length) :
    (patchGate C p h).gates.length = C.gates.length := by
  simp [patchGate]
  omega

theorem patchGate_get (C : Circuit) (p : ℕ) (h : Gate) (hp : p < C.gates.length) (j : ℕ) :
    (patchGate C p h).gates[j]? = if j = p then some h else C.gates[j]? := by
  by_cases hjp : j < p
  · simp only [patchGate]
    rw [List.getElem?_append_left (by simp; omega),
      List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hjp]
    simp [show j ≠ p by omega]
  by_cases hje : j = p
  · subst j
    simp [patchGate, List.getElem?_append, Nat.min_eq_left hp.le]
  · simp only [patchGate]
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_take, List.length_singleton,
      Nat.min_eq_left hp.le, List.getElem?_drop]
    have he : p + 1 + (j - (p + 1)) = j := by omega
    rw [he]
    simp [hje]

theorem patchGate_monotone {C : Circuit} (hC : Monotone2 C) (p : ℕ) (h : Gate)
    (hop : h.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : h.inputs.length ≤ 2) :
    Monotone2 (patchGate C p h) := by
  intro g hg
  change g ∈ (C.gates.take p ++ [h]) ++ C.gates.drop (p + 1) at hg
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · exact hC g (List.mem_of_mem_take hg)
    · simp only [List.mem_singleton] at hg
      subst g
      exact ⟨hop, hlen⟩
  · exact hC g (List.mem_of_mem_drop hg)

theorem compare_one_gate {n : ℕ} {C D : Circuit} (hC : Monotone2 C) (p : ℕ)
    (hlen : D.gates.length = C.gates.length)
    (hget : ∀ j, j ≠ p → D.gates[j]? = C.gates[j]?)
    (x : Fin n → Bool)
    (hpval : val D x (n + p) = true → val C x (n + p) = true) :
    ∀ w, val D x w = true → val C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · let i : Fin n := ⟨w, hin⟩
      have hi : val D x i.val = true := hw
      rw [val_input D x i] at hi
      change val C x i.val = true
      rw [val_input C x i]
      exact hi
    by_cases hgt : n + C.gates.length ≤ w
    · rw [val_beyond D x (by omega)] at hw
      contradiction
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < C.gates.length ∧ w = n + j :=
      ⟨w - n, by omega, by omega⟩
    by_cases hjp : j = p
    · subst j
      exact hpval hw
    let g := C.gates[j]
    have hg : C.gates[j]? = some g := List.getElem?_eq_some_iff.2 ⟨hj, rfl⟩
    have hgD : D.gates[j]? = some g := (hget j hjp).trans hg
    have hop := (hC g (List.mem_of_getElem? hg)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    have hm (a : ℕ) : operand D x (n + j) a = true → operand C x (n + j) a = true := by
      by_cases ha : a < n + j
      · simp only [operand, ite_eq_left ha]
        exact ih a ha
      · simp [operand, ha]
    rw [val_gate D x hgD] at hw
    rw [val_gate C x hg]
    rcases hop with hand | hor
    · simp only [hand, GateOp.eval, List.all_map, Function.comp_apply, id, List.all_eq_true] at hw ⊢
      exact fun a ha => hm a (hw a ha)
    · simp only [hor, GateOp.eval, List.any_map, Function.comp_apply, id, List.any_eq_true] at hw ⊢
      obtain ⟨a, ha, hva⟩ := hw
      exact ⟨a, ha, hm a hva⟩

theorem agree_one_gate {n : ℕ} {C D : Circuit} (hC : Monotone2 C) (hD : Monotone2 D) (p : ℕ)
    (hlen : D.gates.length = C.gates.length)
    (hget : ∀ j, j ≠ p → D.gates[j]? = C.gates[j]?)
    (x : Fin n → Bool) (hpval : val D x (n + p) = val C x (n + p)) :
    ∀ w, val D x w = val C x w := by
  have hDC := compare_one_gate hC p hlen hget x (fun ht => hpval.symm.trans ht)
  have hCD := compare_one_gate hD p hlen.symm (fun j hj => (hget j hj).symm) x
    (fun ht => hpval.trans ht)
  intro w
  have h1 := hDC w
  have h2 := hCD w
  cases hDval : val D x w <;> cases hCval : val C x w <;> simp_all

def forceFalse (C : Circuit) (p : ℕ) : Circuit := patchGate C p ⟨GateOp.or, []⟩

theorem forceFalse_monotone {C : Circuit} (hC : Monotone2 C) (p : ℕ) :
    Monotone2 (forceFalse C p) := patchGate_monotone hC p _ (by simp) (by simp)

theorem forceFalse_at {n : ℕ} (C : Circuit) (p : ℕ) (hp : p < C.gates.length)
    (x : Fin n → Bool) : val (forceFalse C p) x (n + p) = false := by
  have hg : (forceFalse C p).gates[p]? = some ⟨GateOp.or, []⟩ := by
    simpa [forceFalse] using patchGate_get C p ⟨GateOp.or, []⟩ hp p
  rw [val_gate (forceFalse C p) x hg]
  rfl

def CriticalEdge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (p : ℕ)
    (u v : Fin n) : Prop :=
  G.Adj u v ∧ (forceFalse C p).eval (List.ofFn (pairInput u v)) = false

theorem critical_edge_fires {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFn G x)
    {p : ℕ} (hp : p < C.gates.length) {u v : Fin n} (hc : CriticalEdge G C p u v) :
    val C (pairInput u v) (n + p) = true := by
  cases hv : val C (pairInput u v) (n + p) with
  | true => rfl
  | false =>
    have hagree := agree_one_gate hC (forceFalse_monotone hC p) p
      (patchGate_length C p _ hp)
      (fun j hj => by simpa [forceFalse, hj] using patchGate_get C p ⟨GateOp.or, []⟩ hp j)
      (pairInput u v) ((forceFalse_at C p hp _).trans hv.symm) C.output
    have hout : (forceFalse C p).eval (List.ofFn (pairInput u v)) =
        C.eval (List.ofFn (pairInput u v)) := hagree
    rw [hc.2, he, graphFn_pair G hc.1] at hout
    contradiction

theorem critical_edge_replacement {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hC : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFn G x)
    {p : ℕ} (hp : p < C.gates.length) (h : Gate)
    (hop : h.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hfanin : h.inputs.length ≤ 2)
    (hdown : ∀ x : Fin n → Bool, val (patchGate C p h) x (n + p) = true →
      val C x (n + p) = true)
    (hkeep : ∀ u v : Fin n, CriticalEdge G C p u v →
      val (patchGate C p h) (pairInput u v) (n + p) = true) :
    ∀ x : Fin n → Bool, (patchGate C p h).eval (List.ofFn x) = graphFn G x := by
  let D := patchGate C p h
  have hD : Monotone2 D := patchGate_monotone hC p h hop hfanin
  have hlen : D.gates.length = C.gates.length := patchGate_length C p h hp
  have hget : ∀ j, j ≠ p → D.gates[j]? = C.gates[j]? := by
    intro j hj
    simpa [D, hj] using patchGate_get C p h hp j
  have hle (x : Fin n → Bool) := compare_one_gate hC p hlen hget x (hdown x)
  have hedge (u v : Fin n) (huv : G.Adj u v) : D.eval (List.ofFn (pairInput u v)) = true := by
    cases hcut : (forceFalse C p).eval (List.ofFn (pairInput u v)) with
    | false =>
      have ht := hkeep u v ⟨huv, hcut⟩
      have hc := hdown (pairInput u v) ht
      have hagree := agree_one_gate hC hD p hlen hget (pairInput u v) (ht.trans hc.symm) C.output
      change D.eval (List.ofFn (pairInput u v)) = C.eval (List.ofFn (pairInput u v)) at hagree
      exact hagree.trans ((he _).trans (graphFn_pair G huv))
    | true =>
      have hcD : (forceFalse C p).gates.length = D.gates.length :=
        (patchGate_length C p _ hp).trans hlen.symm
      have hcGet : ∀ j, j ≠ p → (forceFalse C p).gates[j]? = D.gates[j]? := by
        intro j hj
        rw [hget j hj]
        simpa [forceFalse, hj] using patchGate_get C p ⟨GateOp.or, []⟩ hp j
      have hcLe := compare_one_gate hD p hcD hcGet (pairInput u v) (by
        rw [forceFalse_at C p hp]
        intro hf
        contradiction) C.output hcut
      exact hcLe
  intro x
  cases hx : graphFn G x with
  | false =>
    cases hval : D.eval (List.ofFn x) with
    | false => rfl
    | true =>
      have hh := hle x C.output hval
      change C.eval (List.ofFn x) = true at hh
      rw [he, hx] at hh
      contradiction
  | true =>
    obtain ⟨u, v, huv, hu, hv⟩ := (graphFn_true G x).1 hx
    have hh := acts_mono hD (x := pairInput u v) (y := x) (by
      intro i hi
      simp only [pairInput, decide_eq_true_eq] at hi
      rcases hi with rfl | rfl
      · exact hu
      · exact hv) D.output (hedge u v huv)
    exact hh

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

theorem minimum_of_same_eval_size {n : ℕ} {C D : Circuit}
    (hmin : IsMinimalMonoCircuit n C) (hD : Monotone2 D) (hsize : D.size = C.size)
    (he : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) :
    IsMinimalMonoCircuit n D := by
  refine ⟨hD, ?_⟩
  intro E hE hfun
  rw [hsize]
  apply hmin.2 E hE
  exact hfun.trans (funext he)

theorem graph_circuit_nonconstant {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFn G x)
    (hedge : ∃ u v, G.Adj u v) : CircuitNonconstant n C := by
  obtain ⟨u, v, huv⟩ := hedge
  refine ⟨pairInput u v, fun _ => false, ?_⟩
  rw [he, he]
  have ht : graphFn G (pairInput u v) = true := graphFn_pair G huv
  rw [ht]
  simp [graphFn]

theorem minimal_gate_has_critical_edge {n : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmin : IsMinimalMonoCircuit n C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFn G x)
    (hedge : ∃ u v, G.Adj u v) {p : ℕ} (hp : p < C.gates.length) :
    ∃ u v, CriticalEdge G C p u v := by
  classical
  by_contra hnone
  push_neg at hnone
  let h : Gate := ⟨GateOp.or, []⟩
  have hdown (x : Fin n → Bool) : val (patchGate C p h) x (n + p) = true →
      val C x (n + p) = true := by
    intro ht
    change val (forceFalse C p) x (n + p) = true at ht
    rw [forceFalse_at C p hp] at ht
    contradiction
  have hkeep : ∀ u v, CriticalEdge G C p u v →
      val (patchGate C p h) (pairInput u v) (n + p) = true := by
    intro u v hc
    exact False.elim (hnone u v hc)
  have hcomp := critical_edge_replacement hmin.1 he hp h (by simp [h]) (by simp [h]) hdown hkeep
  have hD : Monotone2 (patchGate C p h) := patchGate_monotone hmin.1 p h (by simp [h]) (by simp [h])
  have hsize : (patchGate C p h).size = C.size := patchGate_length C p h hp
  have hminD := minimum_of_same_eval_size hmin hD hsize (fun x => (hcomp x).trans (he x).symm)
  obtain ⟨u, v, huv⟩ := hedge
  have hn : 0 < n := by have := u.isLt; omega
  have hnc := graph_circuit_nonconstant hcomp ⟨u, v, huv⟩
  have hpD : p < (patchGate C p h).gates.length := by rw [patchGate_length C p h hp]; exact hp
  apply minimal_no_constant_gate hn hminD hnc hpD
  exact ⟨false, fun x => forceFalse_at C p hp x⟩

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem rdel_gate_op {n p a j : ℕ} {C : Circuit} (hp : p < C.gates.length)
    (hj : j ≠ p) :
    ((rdel n p a C).gates[shiftGate p j]?).map (fun g => g.op) =
      (C.gates[j]?).map (fun g => g.op) := by
  by_cases hjp : j < p
  · rw [show shiftGate p j = j by simp [shiftGate, hjp], rdel_get_lt n p a C hp j hjp]
  · have hpj : p < j := by omega
    have heq : j - 1 + 1 = j := by omega
    rw [show shiftGate p j = j - 1 by simp [shiftGate, hjp],
      rdel_get_ge n p a C hp (j - 1) (by omega), heq]
    cases C.gates[j]? <;> rfl

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.CountedBuilder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


def AllAndSafe {n : ℕ} (B : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ p g, C.gates[p]? = some g → g.op = GateOp.and → WireSafe B C (n + p)

end PEqualNP.Outside.L_meta_1031_aux.CountedBuilder

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def unsafeAndCount {n : ℕ} (F : (Fin n → Bool) → Bool)
    (C : Circuit) : ℕ :=
  Nat.card {j : Fin C.gates.length //
    (C.gates.get j).op = GateOp.and ∧ ¬ WireSafe F C (n + j.val)}

def MinUnsafeAndCount {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ D : Circuit, Monotone2 D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) → D.size = C.size →
    unsafeAndCount F C ≤ unsafeAndCount F D

def MaxSafeAtMinUnsafeAnd {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ D : Circuit, Monotone2 D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) → D.size = C.size →
    unsafeAndCount F D = unsafeAndCount F C → safeGateCount F D ≤ safeGateCount F C

theorem exists_minimum_junk_safe {n : ℕ} (F : (Fin n → Bool) → Bool)
    (C0 : Circuit) (hM0 : Monotone2 C0)
    (he0 : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = F x) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x) ∧ C.size ≤ C0.size ∧
      MinUnsafeAndCount F C ∧ MaxSafeAtMinUnsafeAnd F C := by
  classical
  obtain ⟨B, hminB, heB, hsB, _, _⟩ :=
    exists_minimum_safe_forward_normal F C0 hM0 he0
  have hex : ∃ j, ∃ D : Circuit, Monotone2 D ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) ∧
      D.size = B.size ∧ unsafeAndCount F D = j :=
    ⟨unsafeAndCount F B, B, hminB.1, heB, rfl, rfl⟩
  obtain ⟨J, hMJ, heJ, hsJ, hjJ⟩ := Nat.find_spec hex
  have hJmin (D : Circuit) (hD : Monotone2 D)
      (heD : ∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x)
      (hsD : D.size = B.size) : unsafeAndCount F J ≤ unsafeAndCount F D := by
    rw [hjJ]
    exact Nat.find_min' hex ⟨D, hD, heD, hsD, rfl⟩
  let P := fun s : ℕ => ∃ D : Circuit, Monotone2 D ∧
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = F x) ∧
    D.size = B.size ∧ unsafeAndCount F D = unsafeAndCount F J ∧
    safeGateCount F D = s
  have hP : P (safeGateCount F J) := ⟨J, hMJ, heJ, hsJ, rfl, rfl⟩
  have hbound : safeGateCount F J ≤ B.size := by
    have hh := safeGateCount_le F J
    omega
  obtain ⟨C, hMC, heC, hsC, hjC, hsafeC⟩ :=
    Nat.findGreatest_spec hbound hP
  have hminC : IsMinimalMonoCircuit n C := by
    refine ⟨hMC, fun D hMD hfun => ?_⟩
    rw [hsC]
    apply hminB.2 D hMD
    funext x
    exact ((congrFun hfun x).trans (heC x)).trans (heB x).symm
  have hminJC : MinUnsafeAndCount F C := by
    intro D hD heD hsD
    rw [hjC]
    exact hJmin D hD heD (hsD.trans hsC)
  have hmaxSC : MaxSafeAtMinUnsafeAnd F C := by
    intro D hD heD hsD hjD
    rw [hsafeC]
    apply Nat.le_findGreatest
    · have hh := safeGateCount_le F D
      omega
    · exact ⟨D, hD, heD, hsD.trans hsC, hjD.trans hjC, rfl⟩
  refine ⟨C, hminC, heC, ?_, hminJC, hmaxSC⟩
  omega

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev AndPosition (C : Circuit) := {j : Fin C.gates.length // (C.gates.get j).op = GateOp.and}

theorem option_op_iff (C : Circuit) (j : Fin C.gates.length) (op : GateOp) :
    (C.gates[j.val]?).map (fun g => g.op) = some op ↔ (C.gates.get j).op = op := by
  have hg : C.gates[j.val]? = some (C.gates.get j) := List.getElem?_eq_some_iff.mpr ⟨j.isLt, rfl⟩
  rw [hg]
  simp

theorem wireSafe_iff_of_negative_agreement {n : ℕ} {F : (Fin n → Bool) → Bool}
    {C D : Circuit} {u v : ℕ}
    (heq : ∀ x : Fin n → Bool, F x = false → val D x v = val C x u) :
    WireSafe F C u ↔ WireSafe F D v := by
  constructor
  · intro h x hx
    cases hF : F x with
    | true => rfl
    | false => simpa [hF] using h x ((heq x hF) ▸ hx)
  · intro h x hx
    cases hF : F x with
    | true => rfl
    | false => simpa [hF] using h x ((heq x hF).trans hx)

theorem unsafeAndCount_eq_of_negative_and_equiv {n : ℕ} {F : (Fin n → Bool) → Bool}
    {C D : Circuit} (e : AndPosition C ≃ AndPosition D)
    (heq : ∀ j, ∀ x : Fin n → Bool, F x = false →
      val D x (n + (e j).val.val) = val C x (n + j.val.val)) :
    unsafeAndCount F C = unsafeAndCount F D := by
  have hi (j : AndPosition C) :
      (¬ WireSafe F C (n + j.val.val)) ↔ ¬ WireSafe F D (n + (e j).val.val) :=
    not_congr (wireSafe_iff_of_negative_agreement (heq j))
  let eC := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun j : Fin C.gates.length => (C.gates.get j).op = GateOp.and)
    (fun j : Fin C.gates.length => ¬ WireSafe F C (n + j.val))
  let eD := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun j : Fin D.gates.length => (D.gates.get j).op = GateOp.and)
    (fun j : Fin D.gates.length => ¬ WireSafe F D (n + j.val))
  let eJ := e.subtypeEquiv
    (p := fun j : AndPosition C => ¬ WireSafe F C (n + j.val.val))
    (q := fun j : AndPosition D => ¬ WireSafe F D (n + j.val.val)) hi
  exact Nat.card_congr (eC.symm.trans (eJ.trans eD))

theorem safeOrLift_and_equiv {n p a q : ℕ} {C : Circuit} {g : Gate}
    (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or) :
    ∃ e : AndPosition C ≃ AndPosition (safeOrLift n p a q C),
      ∀ j, (e j).val.val = shiftGate p j.val.val := by
  classical
  let B := rdel n p a C
  let D := safeOrLift n p a q C
  have hp := (List.getElem?_eq_some_iff.mp hg).1
  have hlenB : B.gates.length + 1 = C.gates.length := rdel_length n p a C hp
  have hlenD : D.gates.length = C.gates.length := safeOrLift_size hp
  have hneq (j : AndPosition C) : j.val.val ≠ p := by
    intro heq
    have hj := (option_op_iff C j.val GateOp.and).mpr j.property
    rw [heq, hg] at hj
    simp [hor] at hj
  have hop (j : ℕ) (hj : j < C.gates.length) (hjp : j ≠ p) :
      (D.gates[shiftGate p j]?).map (fun g => g.op) = (C.gates[j]?).map (fun g => g.op) := by
    have hshift : shiftGate p j < B.gates.length := by
      have hh := shiftGate_lt hp hj hjp
      omega
    have hget : D.gates[shiftGate p j]? = B.gates[shiftGate p j]? :=
      List.getElem?_append_left hshift
    rw [hget]
    exact rdel_gate_op hp hjp
  let f : AndPosition C → AndPosition D := fun j =>
    ⟨⟨shiftGate p j.val.val, by
      rw [hlenD]
      have hh := shiftGate_lt hp j.val.isLt (hneq j)
      omega⟩, by
      apply (option_op_iff D _ GateOp.and).mp
      rw [hop j.val.val j.val.isLt (hneq j)]
      exact (option_op_iff C j.val GateOp.and).mpr j.property⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have hv := congrArg (fun z : AndPosition D => z.val.val) hij
    apply Subtype.ext
    apply Fin.ext
    exact shiftGate_injective (hneq i) (hneq j) hv
  have hsurj : Function.Surjective f := by
    intro k
    have hklen : k.val.val < B.gates.length := by
      have hk : k.val.val < C.gates.length := by rw [← hlenD]; exact k.val.isLt
      by_contra hnot
      have hlast : k.val.val = B.gates.length := by omega
      have hkop := (option_op_iff D k.val GateOp.and).mpr k.property
      rw [hlast] at hkop
      simp [D, safeOrLift, appendOutputOr, B] at hkop
    let j := if k.val.val < p then k.val.val else k.val.val + 1
    have hj : j < C.gates.length := by unfold j; split_ifs <;> omega
    have hjp : j ≠ p := by unfold j; split_ifs <;> omega
    have hshift : shiftGate p j = k.val.val := by unfold j shiftGate; split_ifs <;> omega
    have hand : (C.gates.get ⟨j, hj⟩).op = GateOp.and := by
      apply (option_op_iff C ⟨j, hj⟩ GateOp.and).mp
      rw [← hop j hj hjp, hshift]
      exact (option_op_iff D k.val GateOp.and).mpr k.property
    refine ⟨⟨⟨j, hj⟩, hand⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    exact hshift
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun _ => rfl⟩

theorem safeOrLift_unsafeAndCount {n p a q : ℕ} {F : (Fin n → Bool) → Bool}
    {C : Circuit} {g : Gate} (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (hsafe : WireSafe F C q) :
    unsafeAndCount F (safeOrLift n p a q C) = unsafeAndCount F C := by
  obtain ⟨e, he⟩ := safeOrLift_and_equiv (n := n) (a := a) (q := q) hg hor
  apply (unsafeAndCount_eq_of_negative_and_equiv e ?_).symm
  intro j x hneg
  have hjp : j.val.val ≠ p := by
    intro heq
    have hj := (option_op_iff C j.val GateOp.and).mpr j.property
    rw [heq, hg] at hj
    simp [hor] at hj
  rw [he j, ← rd_gate_eq (n := n) (a := a) hjp]
  exact safeOrLift_negative_agreement hg hor hins ha hq hsafe x hneg (n + j.val.val)
    (by have := j.val.isLt; omega) (by omega)

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem junk_max_safe_or_is_safe {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (hC : Monotone2 C) (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hmax : MaxSafeAtMinUnsafeAnd F C) {p a q : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hor : g.op = GateOp.or)
    (hins : g.inputs = [q, a] ∨ g.inputs = [a, q])
    (ha : a < n + p) (hq : q < n + p) (hsafe : WireSafe F C q) :
    WireSafe F C (n + p) := by
  by_contra hbad
  have hlt := safeOrLift_safe_count he hg hor hins ha hq hsafe hbad
  have hle := hmax (safeOrLift n p a q C) (safeOrLift_monotone hC)
    (safeOrLift_eval he hg hor hins ha hq hsafe)
    (safeOrLift_size (List.getElem?_eq_some_iff.1 hg).1)
    (safeOrLift_unsafeAndCount hg hor hins ha hq hsafe)
  omega

theorem junk_max_safe_reader_is_safe_or {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (hmin : IsMinimalMonoCircuit n C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hmax : MaxSafeAtMinUnsafeAnd F C) {p q : ℕ} {g : Gate}
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
        · exact junk_max_safe_or_is_safe hmin.1 he hmax hg hor (Or.inl hins) hb hq hsafe
        · intro x hx
          rw [val_gate C x hg] at hx
          simp [hor, hins, GateOp.eval, operand, hb, hq] at hx
          exact hsafe x hx
      · subst b
        by_cases ha : a < n + p
        · exact junk_max_safe_or_is_safe hmin.1 he hmax hg hor (Or.inr hins) ha hq hsafe
        · intro x hx
          rw [val_gate C x hg] at hx
          simp [hor, hins, GateOp.eval, operand, ha, hq] at hx
          exact hsafe x hx

theorem exists_minimum_junk_safe_forward {n : ℕ} (F : (Fin n → Bool) → Bool)
    (C0 : Circuit) (hM0 : Monotone2 C0)
    (he0 : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = F x) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x) ∧ C.size ≤ C0.size ∧
      MinUnsafeAndCount F C ∧ MaxSafeAtMinUnsafeAnd F C ∧ SafeForwardNormal F C := by
  obtain ⟨C, hmin, he, hsize, hminJ, hmaxS⟩ := exists_minimum_junk_safe F C0 hM0 he0
  exact ⟨C, hmin, he, hsize, hminJ, hmaxS, fun _ _ _ hg hm hq hs =>
    junk_max_safe_reader_is_safe_or hmin he hmaxS hg hm hq hs⟩

abbrev JunkPosition {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) :=
  {j : Fin C.gates.length // (C.gates.get j).op = GateOp.and ∧ ¬ WireSafe F C (n + j.val)}

theorem allAndSafe_unsafeAndCount_zero {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (h : CountedBuilder.AllAndSafe F C) : unsafeAndCount F C = 0 := by
  haveI : IsEmpty (JunkPosition F C) := ⟨fun j => j.property.2
    (h j.val.val (C.gates.get j.val)
      (List.getElem?_eq_some_iff.mpr ⟨j.val.isLt, rfl⟩) j.property.1)⟩
  exact Nat.card_of_isEmpty

end PEqualNP.Outside.L_meta_1031_aux

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

structure Geometry (G : SimpleGraph α) (c : Fin k → α)
    (L : Fin k → Finset α) : Prop where
  centers_injective : Function.Injective c
  leaves_nonempty : ∀ i, (L i).Nonempty
  centers_outside : ∀ i j, c i ∉ L j
  leaves_disjoint : ∀ i j, i ≠ j → Disjoint (L i) (L j)
  star_edges : ∀ i v, v ∈ L i → G.Adj (c i) v
  induced : ∀ u ∈ support c L, ∀ v ∈ support c L, G.Adj u v →
    ∃ i, (u = c i ∧ v ∈ L i) ∨ (v = c i ∧ u ∈ L i)

end PEqualNP.Outside.L_meta_1031_aux.InducedStarChoices

namespace PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

structure AdjacentCentersGeometry (G H : SimpleGraph α) (a b : α)
    (A B : Finset α) : Prop where
  center_edge : G.Adj a b
  left_nonempty : A.Nonempty
  right_nonempty : B.Nonempty
  left_away : b ∉ A
  right_away : a ∉ B
  left_edges : ∀ u ∈ A, H.Adj a u
  right_edges : ∀ v ∈ B, H.Adj b v
  envelope : ∀ u v, H.Adj u v →
    (u = a ∧ v ∈ insert b A) ∨ (v = a ∧ u ∈ insert b A) ∨
    (u = b ∧ v ∈ B) ∨ (v = b ∧ u ∈ B)

theorem independent_of_common_neighbor {G : SimpleGraph α}
    (h3 : RelativeClause.TriangleFree G) {S : Finset α} {c : α}
    (hS : ∀ u ∈ S, G.Adj c u) : G.IsIndepSet (S : Set α) := by
  intro u hu v hv _ huv
  exact h3 c u v (hS u hu) huv (hS v hv).symm

end PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

namespace PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem independent_insert_of_not_adj {G : SimpleGraph α} {c : α} {S : Finset α}
    (hS : G.IsIndepSet (S : Set α)) (hc : ∀ u ∈ S, ¬ G.Adj c u) :
    G.IsIndepSet ((insert c S : Finset α) : Set α) := by
  intro u hu v hv huv hG
  rcases Finset.mem_insert.mp hu with huc | hu
  · subst u
    rcases Finset.mem_insert.mp hv with hvc | hv
    · subst v
      exact huv rfl
    · exact hc v hv hG
  · rcases Finset.mem_insert.mp hv with hvc | hv
    · subst v
      exact hc u hu hG.symm
    · exact hS hu hv huv hG

structure CommonLeafGeometry (H : SimpleGraph α) (a b c : α)
    (A B : Finset α) : Prop where
  centers_distinct : a ≠ b
  common_left : H.Adj a c
  common_right : H.Adj b c
  left_nonempty : A.Nonempty
  right_nonempty : B.Nonempty
  common_left_away : c ∉ A
  common_right_away : c ∉ B
  left_edges : ∀ u ∈ A, H.Adj a u
  right_edges : ∀ v ∈ B, H.Adj b v
  envelope : ∀ u v, H.Adj u v →
    (u = a ∧ v ∈ insert c A) ∨ (v = a ∧ u ∈ insert c A) ∨
    (u = b ∧ v ∈ insert c B) ∨ (v = b ∧ u ∈ insert c B)

end PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

namespace PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

structure DisjointStarsGeometry (H : SimpleGraph α) (a b : α)
    (A B : Finset α) : Prop where
  centers_distinct : a ≠ b
  left_nonempty : A.Nonempty
  right_nonempty : B.Nonempty
  left_away : b ∉ A
  right_away : a ∉ B
  disjoint : Disjoint A B
  left_edges : ∀ u ∈ A, H.Adj a u
  right_edges : ∀ v ∈ B, H.Adj b v
  envelope : ∀ u v, H.Adj u v →
    (u = a ∧ v ∈ A) ∨ (v = a ∧ u ∈ A) ∨
    (u = b ∧ v ∈ B) ∨ (v = b ∧ u ∈ B)

end PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

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

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem safe_ancestor_last_or {n : ℕ} {F : (Fin n → Bool) → Bool} {C : Circuit}
    (hN : SafeForwardNormal F C) {a b : ℕ} (hab : Ancestor n C a b)
    (hs : WireSafe F C a) :
    ∃ p g, b = n + p ∧ C.gates[p]? = some g ∧ g.op = GateOp.or := by
  cases hab with
  | single h =>
    obtain ⟨hlt, p, g, rfl, hg, hm⟩ := h
    exact ⟨p, g, rfl, hg, (hN _ p g hg hm hlt hs).1⟩
  | tail hprev h =>
    obtain ⟨hlt, p, g, rfl, hg, hm⟩ := h
    exact ⟨p, g, rfl, hg,
      (hN _ p g hg hm hlt (safe_forward_normal_ancestor hN hprev hs)).1⟩

theorem safe_and_has_no_and_ancestor {n : ℕ} {F : (Fin n → Bool) → Bool}
    {C : Circuit} (hN : SafeForwardNormal F C)
    (hAll : ∀ p g, C.gates[p]? = some g → g.op = GateOp.and →
      WireSafe F C (n + p))
    {t t' : ℕ} {g g' : Gate} (hg : C.gates[t]? = some g)
    (hand : g.op = GateOp.and) (hg' : C.gates[t']? = some g')
    (hand' : g'.op = GateOp.and) : ¬ Ancestor n C (n + t') (n + t) := by
  intro hanc
  obtain ⟨p, h, hw, hh, hor⟩ := safe_ancestor_last_or hN hanc (hAll t' g' hg' hand')
  have hp : p = t := by omega
  subst p
  have heq : h = g := Option.some.inj (hh.symm.trans hg)
  subst h
  rw [hand] at hor
  contradiction

theorem minimum_all_safe_and_nonempty_stars {n : ℕ} (G : SimpleGraph (Fin n))
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d) {C : Circuit} (hmin : IsMinimalMonoCircuit n C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFn G x)
    (hedge : ∃ u v, G.Adj u v) (hN : SafeForwardNormal (graphFn G) C)
    (hAll : ∀ p g, C.gates[p]? = some g → g.op = GateOp.and →
      WireSafe (graphFn G) C (n + p)) :
    ∀ t g, C.gates[t]? = some g → g.op = GateOp.and →
      ∃ c : Fin n, (∃ u v, G.Adj u v ∧ OwnsPair C t u v) ∧
        ∀ u v, G.Adj u v → OwnsPair C t u v → u = c ∨ v = c := by
  intro t g hg hand
  have ht : t < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  obtain ⟨u, v, hc⟩ := minimal_gate_has_critical_edge hmin he hedge ht
  have hnonempty : ∃ u v, G.Adj u v ∧ OwnsPair C t u v := by
    refine ⟨u, v, hc.1, critical_edge_fires hmin.1 he ht hc, ?_⟩
    intro t' g' hg' hand' hanc
    exact False.elim (safe_and_has_no_and_ancestor hN hAll hg hand hg' hand' hanc)
  have hsafe : SafeAt G C (n + t) := by
    intro x hx
    exact (graphFn_true G x).mp (hAll t g hg hand x hx)
  obtain ⟨c, hc⟩ := safe_and_owned_star G hfour hmin.1 hg hand hsafe hnonempty
  exact ⟨c, hnonempty, hc⟩

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.ConnectedDoubleStar

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

structure Geometry (G H : SimpleGraph α) (a b : α) (A B : Finset α) : Prop
    extends SeparatedWitness.AdjacentCentersGeometry G H a b A B where
  critical_centers : H.Adj a b

def vertices (a b : α) (A B : Finset α) : Finset α := insert a (insert b (A ∪ B))

theorem Geometry.left_self {G H : SimpleGraph α} {a b : α} {A B : Finset α}
    (h : Geometry G H a b A B) : a ∉ A := by
  intro ha
  exact H.loopless.irrefl a (h.left_edges a ha)

theorem Geometry.right_self {G H : SimpleGraph α} {a b : α} {A B : Finset α}
    (h : Geometry G H a b A B) : b ∉ B := by
  intro hb
  exact H.loopless.irrefl b (h.right_edges b hb)

theorem Geometry.leaves_disjoint {G H : SimpleGraph α} {a b : α} {A B : Finset α}
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G)
    (h : Geometry G H a b A B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro u huA huB
  exact h3 a b u h.center_edge (hHG (h.right_edges u huB))
    (hHG (h.left_edges u huA)).symm

theorem Geometry.left_negative {G H : SimpleGraph α} {a b : α} {A B : Finset α}
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G)
    (h : Geometry G H a b A B) :
    G.IsIndepSet ((insert a B : Finset α) : Set α) := by
  apply SeparatedWitness.independent_of_common_neighbor h3 (c := b)
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact h.center_edge.symm
  · exact hHG (h.right_edges u hu)

theorem Geometry.right_negative {G H : SimpleGraph α} {a b : α} {A B : Finset α}
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G)
    (h : Geometry G H a b A B) :
    G.IsIndepSet ((insert b A : Finset α) : Set α) := by
  apply SeparatedWitness.independent_of_common_neighbor h3 (c := a)
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu
  · exact h.center_edge
  · exact hHG (h.left_edges u hu)

theorem Geometry.leaf_negative {G H : SimpleGraph α} {a b : α} {A B : Finset α}
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G)
    (h4 : RelativeClause.FourCycleFree G) (h : Geometry G H a b A B) :
    G.IsIndepSet ((A ∪ B : Finset α) : Set α) := by
  apply RelativeClause.indep_subset
    (RelativeClause.edge_open_neighborhoods_indep h3 h4 h.center_edge)
  intro u hu
  rcases Finset.mem_union.mp hu with hu | hu
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
      ⟨fun hub => h.left_away (hub ▸ hu),
        RelativeClause.mem_neighbors.mpr (hHG (h.left_edges u hu))⟩)
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
      ⟨fun hua => h.right_away (hua ▸ hu),
        RelativeClause.mem_neighbors.mpr (hHG (h.right_edges u hu))⟩)

theorem Geometry.induced {G H : SimpleGraph α} {a b : α} {A B : Finset α}
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G)
    (h4 : RelativeClause.FourCycleFree G) (h : Geometry G H a b A B) :
    ∀ u ∈ vertices a b A B, ∀ v ∈ vertices a b A B, G.Adj u v → H.Adj u v := by
  have hI0 := h.left_negative hHG h3
  have hI1 := h.right_negative hHG h3
  have hI2 := h.leaf_negative hHG h3 h4
  intro u hu v hv huv
  have hu' : u = a ∨ u = b ∨ u ∈ A ∨ u ∈ B := by simpa [vertices] using hu
  have hv' : v = a ∨ v = b ∨ v ∈ A ∨ v ∈ B := by simpa [vertices] using hv
  rcases hu' with hua | hub | huA | huB
  · subst u
    rcases hv' with hva | hvb | hvA | hvB
    · subst v; exact (huv.ne rfl).elim
    · subst v; exact h.critical_centers
    · exact h.left_edges v hvA
    · exact (RelativeClause.indep_not_adj hI0 (by simp) (by simp [hvB]) huv).elim
  · subst u
    rcases hv' with hva | hvb | hvA | hvB
    · subst v; exact h.critical_centers.symm
    · subst v; exact (huv.ne rfl).elim
    · exact (RelativeClause.indep_not_adj hI1 (by simp) (by simp [hvA]) huv).elim
    · exact h.right_edges v hvB
  · rcases hv' with hva | hvb | hvA | hvB
    · subst v; exact (h.left_edges u huA).symm
    · subst v; exact (RelativeClause.indep_not_adj hI1 (by simp [huA]) (by simp) huv).elim
    · exact (RelativeClause.indep_not_adj hI2 (by simp [huA]) (by simp [hvA]) huv).elim
    · exact (RelativeClause.indep_not_adj hI2 (by simp [huA]) (by simp [hvB]) huv).elim
  · rcases hv' with hva | hvb | hvA | hvB
    · subst v; exact (RelativeClause.indep_not_adj hI0 (by simp [huB]) (by simp) huv).elim
    · subst v; exact (h.right_edges u huB).symm
    · exact (RelativeClause.indep_not_adj hI2 (by simp [huB]) (by simp [hvA]) huv).elim
    · exact (RelativeClause.indep_not_adj hI2 (by simp [huB]) (by simp [hvB]) huv).elim

end PEqualNP.Outside.L_meta_1031_aux.ConnectedDoubleStar

namespace PEqualNP.Outside.L_meta_1031_aux.CommonLeafBoundarySelection

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def active (a b c : α) (A B : Finset α) : Finset α :=
  ({a, b, c} ∪ A) ∪ B

structure Selection (a b c : α) (A B : Finset α)
    (L : β → Finset α) (f : α → β) : Prop where
  arms_disjoint : Disjoint A B
  left_apart : Disjoint A {a, b, c}
  right_apart : Disjoint B {a, b, c}
  pure_a : L (f a) = {a}
  pure_b : L (f b) = {b}
  pure_c : L (f c) = {c}
  left : ∀ u ∈ A, u ∈ L (f u) ∧ L (f u) ⊆ {u, b}
  right : ∀ v ∈ B, v ∈ L (f v) ∧ L (f v) ⊆ {v, a}

variable {a b c : α} {A B : Finset α} {L : β → Finset α} {f : α → β}

theorem active_cases {u : α} (hu : u ∈ active a b c A B) :
    u ∈ ({a, b, c} : Finset α) ∨ u ∈ A ∨ u ∈ B := by
  simpa [active, or_assoc] using hu

theorem Selection.core_pure (h : Selection a b c A B L f) {u : α}
    (hu : u ∈ ({a, b, c} : Finset α)) : L (f u) = {u} := by
  rcases (show u = a ∨ u = b ∨ u = c by simpa using hu) with hua | hub | huc
  · subst u; exact h.pure_a
  · subst u; exact h.pure_b
  · subst u; exact h.pure_c

theorem Selection.contains (h : Selection a b c A B L f) {u : α}
    (hu : u ∈ active a b c A B) : u ∈ L (f u) := by
  rcases active_cases hu with hcore | hleft | hright
  · rw [h.core_pure hcore]
    simp
  · exact (h.left u hleft).1
  · exact (h.right u hright).1

theorem Selection.left_label_unique (h : Selection a b c A B L f)
    {u v : α} (hu : u ∈ A) (hv : v ∈ active a b c A B)
    (huv : u ∈ L (f v)) : v = u := by
  have hucore : u ∉ ({a, b, c} : Finset α) :=
    fun hm => Finset.disjoint_left.mp h.left_apart hu hm
  rcases active_cases hv with hvcore | hvA | hvB
  · rw [h.core_pure hvcore] at huv
    have huv' : u = v := Finset.mem_singleton.mp huv
    exact (hucore (huv'.symm ▸ hvcore)).elim
  · have hsub := (h.left v hvA).2 huv
    rcases (show u = v ∨ u = b by simpa using hsub) with huv' | hub
    · exact huv'.symm
    · exact (hucore (by simp [hub])).elim
  · have hsub := (h.right v hvB).2 huv
    rcases (show u = v ∨ u = a by simpa using hsub) with huv' | hua
    · exact (Finset.disjoint_left.mp h.arms_disjoint hu (huv'.symm ▸ hvB)).elim
    · exact (hucore (by simp [hua])).elim

theorem Selection.right_label_unique (h : Selection a b c A B L f)
    {u v : α} (hu : u ∈ B) (hv : v ∈ active a b c A B)
    (huv : u ∈ L (f v)) : v = u := by
  have hucore : u ∉ ({a, b, c} : Finset α) :=
    fun hm => Finset.disjoint_left.mp h.right_apart hu hm
  rcases active_cases hv with hvcore | hvA | hvB
  · rw [h.core_pure hvcore] at huv
    have huv' : u = v := Finset.mem_singleton.mp huv
    exact (hucore (huv'.symm ▸ hvcore)).elim
  · have hsub := (h.left v hvA).2 huv
    rcases (show u = v ∨ u = b by simpa using hsub) with huv' | hub
    · exact (Finset.disjoint_left.mp h.arms_disjoint (huv'.symm ▸ hvA) hu).elim
    · exact (hucore (by simp [hub])).elim
  · have hsub := (h.right v hvB).2 huv
    rcases (show u = v ∨ u = a by simpa using hsub) with huv' | hua
    · exact huv'.symm
    · exact (hucore (by simp [hua])).elim

theorem Selection.injective (h : Selection a b c A B L f) :
    Set.InjOn f (active a b c A B : Set α) := by
  intro u hu v hv hfv
  have huv : u ∈ L (f v) := by
    rw [← hfv]
    exact h.contains hu
  have hvu : v ∈ L (f u) := by
    rw [hfv]
    exact h.contains hv
  rcases active_cases hu with hucore | huA | huB
  · rcases active_cases hv with hvcore | hvA | hvB
    · rw [h.core_pure hvcore] at huv
      exact Finset.mem_singleton.mp huv
    · exact h.left_label_unique hvA hu hvu
    · exact h.right_label_unique hvB hu hvu
  · exact (h.left_label_unique huA hv huv).symm
  · exact (h.right_label_unique huB hv huv).symm

end PEqualNP.Outside.L_meta_1031_aux.CommonLeafBoundarySelection

namespace PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

open Finset CommonLeafBoundarySelection

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {G H : SimpleGraph α} {a b c : α} {A B : Finset α}

theorem CommonLeafGeometry.left_self (h : CommonLeafGeometry H a b c A B) :
    a ∉ A := by
  intro ha
  exact H.loopless.irrefl a (h.left_edges a ha)

theorem CommonLeafGeometry.right_self (h : CommonLeafGeometry H a b c A B) :
    b ∉ B := by
  intro hb
  exact H.loopless.irrefl b (h.right_edges b hb)

theorem CommonLeafGeometry.not_centers_adj (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G) : ¬ G.Adj a b := by
  intro hab
  exact h3 a b c hab (hHG h.common_right) (hHG h.common_left).symm

theorem CommonLeafGeometry.left_other (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G) : b ∉ A := by
  intro hb
  exact h.not_centers_adj hHG h3 (hHG (h.left_edges b hb))

theorem CommonLeafGeometry.right_other (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G) : a ∉ B := by
  intro ha
  exact h.not_centers_adj hHG h3 (hHG (h.right_edges a ha)).symm

theorem CommonLeafGeometry.arms_disjoint (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h4 : RelativeClause.FourCycleFree G) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro u huA huB
  have hcu : c ≠ u := fun hcu => h.common_left_away (hcu.symm ▸ huA)
  exact h4 a c b u h.centers_distinct hcu
    (hHG h.common_left) (hHG h.common_right).symm
    (hHG (h.right_edges u huB)) (hHG (h.left_edges u huA)).symm

theorem CommonLeafGeometry.left_apart (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G) :
    Disjoint A ({a,b,c} : Finset α) := by
  apply Finset.disjoint_left.mpr
  intro u hu hcore
  rcases (show u = a ∨ u = b ∨ u = c by simpa using hcore) with hua | hub | huc
  · exact h.left_self (hua ▸ hu)
  · exact h.left_other hHG h3 (hub ▸ hu)
  · exact h.common_left_away (huc ▸ hu)

theorem CommonLeafGeometry.right_apart (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G) :
    Disjoint B ({a,b,c} : Finset α) := by
  apply Finset.disjoint_left.mpr
  intro u hu hcore
  rcases (show u = a ∨ u = b ∨ u = c by simpa using hcore) with hua | hub | huc
  · exact h.right_other hHG h3 (hua ▸ hu)
  · exact h.right_self (hub ▸ hu)
  · exact h.common_right_away (huc ▸ hu)

theorem CommonLeafGeometry.not_left_to_right_arm (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h4 : RelativeClause.FourCycleFree G) :
    ∀ v ∈ B, ¬ G.Adj a v := by
  intro v hv hav
  have hcv : c ≠ v := fun hcv => h.common_right_away (hcv.symm ▸ hv)
  exact h4 a c b v h.centers_distinct hcv
    (hHG h.common_left) (hHG h.common_right).symm
    (hHG (h.right_edges v hv)) hav.symm

theorem CommonLeafGeometry.not_right_to_left_arm (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h4 : RelativeClause.FourCycleFree G) :
    ∀ u ∈ A, ¬ G.Adj b u := by
  intro u hu hbu
  have hcu : c ≠ u := fun hcu => h.common_left_away (hcu.symm ▸ hu)
  exact h4 b c a u h.centers_distinct.symm hcu
    (hHG h.common_right) (hHG h.common_left).symm
    (hHG (h.left_edges u hu)) hbu.symm

theorem CommonLeafGeometry.left_negative (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G)
    (h4 : RelativeClause.FourCycleFree G) :
    G.IsIndepSet ((insert a B : Finset α) : Set α) := by
  exact independent_insert_of_not_adj
    (independent_of_common_neighbor h3 (fun v hv => hHG (h.right_edges v hv)))
    (h.not_left_to_right_arm hHG h4)

theorem CommonLeafGeometry.right_negative (h : CommonLeafGeometry H a b c A B)
    (hHG : H ≤ G) (h3 : RelativeClause.TriangleFree G)
    (h4 : RelativeClause.FourCycleFree G) :
    G.IsIndepSet ((insert b A : Finset α) : Set α) := by
  exact independent_insert_of_not_adj
    (independent_of_common_neighbor h3 (fun u hu => hHG (h.left_edges u hu)))
    (h.not_right_to_left_arm hHG h4)

end PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

namespace PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

variable {G H : SimpleGraph α} {a b : α} {A B : Finset α}

theorem DisjointStarsGeometry.left_self (h : DisjointStarsGeometry H a b A B) :
    a ∉ A := by
  intro ha
  exact H.loopless.irrefl a (h.left_edges a ha)

theorem DisjointStarsGeometry.right_self (h : DisjointStarsGeometry H a b A B) :
    b ∉ B := by
  intro hb
  exact H.loopless.irrefl b (h.right_edges b hb)

end PEqualNP.Outside.L_meta_1031_aux.SeparatedWitness

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open Finset

theorem minimum_graph_gate_has_edge {n p : ℕ} {G : SimpleGraph (Fin n)} {C : Circuit}
    (hmin : IsMinimalMonoCircuit n C)
    (he : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFn G x)
    (hp : p < C.gates.length) : ∃ u v, G.Adj u v := by
  classical
  by_contra hnone
  have hzero : ∀ x : Fin n → Bool, graphFn G x = false := by
    intro x
    cases ht : graphFn G x with
    | false => rfl
    | true =>
      obtain ⟨u,v,huv,_,_⟩ := (graphFn_true G x).mp ht
      exact (hnone ⟨u,v,huv⟩).elim
  let D : Circuit := ⟨[],n⟩
  have hD : Monotone2 D := by
    intro g hg
    simp [D] at hg
  have hDe : circuitFun n D = circuitFun n C := by
    funext x
    change D.eval (List.ofFn x) = C.eval (List.ofFn x)
    rw [he,hzero]
    change val D x n = false
    exact val_beyond D x (by simp [D])
  have hbound := hmin.2 D hD hDe
  change C.gates.length ≤ 0 at hbound
  omega

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.DisjointStarFamily

open Finset

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

def support (c : ι → α) (L : ι → Finset α) : Finset α :=
  Finset.univ.biUnion fun i => insert (c i) (L i)

structure Geometry (H : SimpleGraph α) (c : ι → α) (L : ι → Finset α) : Prop where
  leaves_nonempty : ∀ i, (L i).Nonempty
  star_edges : ∀ i u, u ∈ L i → H.Adj (c i) u
  envelope : ∀ u v, H.Adj u v → ∃ i,
    (u = c i ∧ v ∈ L i) ∨ (v = c i ∧ u ∈ L i)
  closed_disjoint : ∀ i j, i ≠ j → Disjoint (insert (c i) (L i)) (insert (c j) (L j))

end PEqualNP.Outside.L_meta_1031_aux.DisjointStarFamily

namespace PEqualNP.Outside.L_meta_1031_aux

open Finset

variable {ι : Type*} [DecidableEq ι]

def FeatureSupported (f : Finset ι → Bool) (S : Finset ι) : Prop :=
  ∀ A, f A = f (A ∩ S)

theorem FeatureSupported.mono {f : Finset ι → Bool} {S T : Finset ι}
    (hs : FeatureSupported f S) (hst : S ⊆ T) : FeatureSupported f T := by
  intro A
  have he : (A ∩ T) ∩ S = A ∩ S := by
    ext i
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,hst h.2⟩,h.2⟩⟩
  rw [hs A,hs (A ∩ T),he]

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

def forestFun0 {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∨ ∃ u v : Fin n, K.Adj u v ∧ x u = true ∧ x v = true)

lemma forestFun0_false {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (A : Finset (Fin n)) :
    forestFun0 K A (fun _ => false) = false := by
  simp [forestFun0]

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

end PEqualNP.Outside.L_meta_1031_aux.RelativeForestCore

namespace PEqualNP.Outside.L_meta_1031_aux

open Finset

variable {ι : Type*} [DecidableEq ι]

theorem feature_supported_singleton_outside {f : Finset ι → Bool} {S : Finset ι}
    (hs : FeatureSupported f S) {u : ι} (hu : u ∉ S) : f {u} = f ∅ := by
  have hempty : ({u} : Finset ι) ∩ S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hxu,hxS⟩ := Finset.mem_inter.mp hx
    exact hu ((Finset.mem_singleton.mp hxu) ▸ hxS)
  rw [hs {u},hempty]

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

theorem Expr.eval_supported (e : Expr ι) : FeatureSupported e.eval e.support := by
  induction e with
  | zero => intro A; rfl
  | input i => intro A; simp [Expr.eval,Expr.support]
  | conj p q hp hq => exact feature_supported_and hp hq
  | disj p q hp hq => exact feature_supported_or hp hq

theorem Expr.eval_empty (e : Expr ι) : e.eval ∅ = false := by
  induction e <;> simp_all [Expr.eval]

def Expr.erase (z : ι) : Expr ι → Expr ι
  | .zero => .zero
  | .input i => if i = z then .zero else .input i
  | .conj p q => .conj (p.erase z) (q.erase z)
  | .disj p q => .disj (p.erase z) (q.erase z)

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

open Finset SimpleGraph

variable {ι : Type*} [DecidableEq ι]

def Expr.pairGraph (e : Expr ι) : SimpleGraph ι where
  Adj u v := u ≠ v ∧ e.eval {u,v} = true
  symm := by
    constructor
    intro u v h
    exact ⟨Ne.symm h.1,by simpa only [Finset.pair_comm] using h.2⟩
  loopless := by constructor; intro u h; exact h.1 rfl

@[simp] theorem Expr.pairGraph_adj (e : Expr ι) (u v : ι) :
    e.pairGraph.Adj u v ↔ u ≠ v ∧ e.eval {u,v} = true := Iff.rfl

theorem Expr.singleton_mem_support (e : Expr ι) {u : ι}
    (hu : e.eval {u} = true) : u ∈ e.support := by
  by_contra hn
  rw [feature_supported_singleton_outside e.eval_supported hn,e.eval_empty] at hu
  contradiction

def Expr.privateSingletons (e : Expr ι) (z : ι) : Finset ι :=
  (e.support.erase z).filter (fun a => e.eval {a} = true)

@[simp] theorem Expr.mem_privateSingletons (e : Expr ι) (z a : ι) :
    a ∈ e.privateSingletons z ↔ a ≠ z ∧ e.eval {a} = true := by
  constructor
  · intro ha
    obtain ⟨haS,ha⟩ := mem_filter.mp ha
    exact ⟨(mem_erase.mp haS).1,ha⟩
  · rintro ⟨haz,ha⟩
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨haz,e.singleton_mem_support ha⟩,ha⟩

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

open Finset SimpleGraph

variable {ι : Type*} [DecidableEq ι]

def Expr.singletonSupport (e : Expr ι) : Finset ι :=
  e.support.filter (fun i => e.eval {i} = true)

@[simp] theorem Expr.mem_singletonSupport (e : Expr ι) (i : ι) :
    i ∈ e.singletonSupport ↔ e.eval {i} = true := by
  constructor
  · exact fun hi => (mem_filter.mp hi).2
  · exact fun hi => mem_filter.mpr ⟨e.singleton_mem_support hi,hi⟩

end PEqualNP.Outside.L_meta_1031_aux.QuadraticExpr

namespace PEqualNP.Outside.L_meta_1031_aux.SelectedGateExtraction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def wire (n m : ℕ) (C : Circuit) (A : Finset ℕ)
    (β : ℕ → Option (Fin m)) (w : ℕ) : ℕ := by
  classical
  exact if w ∈ A.image (fun j => n + j) then m + (w - n)
    else (β w).elim (m + C.gates.length) Fin.val

noncomputable def gate (n m : ℕ) (C : Circuit) (A : Finset ℕ)
    (β : ℕ → Option (Fin m)) (j : Fin C.gates.length) : Gate := by
  classical
  exact if j.val ∈ A then
    ⟨(C.gates.get j).op, (C.gates.get j).inputs.map (wire n m C A β)⟩
    else ⟨GateOp.or, []⟩

noncomputable def stage (n m : ℕ) (C : Circuit) (A : Finset ℕ)
    (β : ℕ → Option (Fin m)) (p : ℕ) : Circuit :=
  ⟨List.ofFn (gate n m C A β), m + p⟩

@[simp] theorem stage_length (n m : ℕ) (C : Circuit) (A : Finset ℕ)
    (β : ℕ → Option (Fin m)) (p : ℕ) :
    (stage n m C A β p).gates.length = C.gates.length := by simp [stage]

end PEqualNP.Outside.L_meta_1031_aux.SelectedGateExtraction

namespace PEqualNP.Outside.L_meta_1031_aux.PureBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open RelativeForestCore

noncomputable def liftInput {m n : ℕ} (e : Fin m ↪ Fin n)
    (x : Fin m → Bool) : Fin n → Bool := by
  classical
  exact fun v => decide (∃ u : Fin m, e u = v ∧ x u = true)

@[simp] theorem liftInput_true {m n : ℕ} (e : Fin m ↪ Fin n)
    (x : Fin m → Bool) (v : Fin n) :
    liftInput e x v = true ↔ ∃ u : Fin m, e u = v ∧ x u = true := by
  classical
  simp [liftInput]

@[simp] theorem liftInput_apply {m n : ℕ} (e : Fin m ↪ Fin n)
    (x : Fin m → Bool) (u : Fin m) : liftInput e x (e u) = x u := by
  classical
  rw [Bool.eq_iff_iff, liftInput_true]
  constructor
  · rintro ⟨v,hv,hx⟩
    exact e.injective hv ▸ hx
  · intro hx
    exact ⟨u,rfl,hx⟩

end PEqualNP.Outside.L_meta_1031_aux.PureBoundary

namespace PEqualNP.Outside.L_meta_1031_aux.QuadraticGraph

open SimpleGraph

variable {V : Type*}

noncomputable def collapseVertex (w z v : V) : V := by
  classical
  exact if v=w then z else v

@[simp] theorem collapseVertex_self (w z : V) : collapseVertex w z w=z := by
  classical
  simp [collapseVertex]

end PEqualNP.Outside.L_meta_1031_aux.QuadraticGraph

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem unsafeAndCount_zero_all_safe {n : ℕ} {F : (Fin n → Bool) → Bool}
    {C : Circuit} (hzero : unsafeAndCount F C = 0) :
    CountedBuilder.AllAndSafe F C := by
  classical
  intro p g hg hand
  by_contra hbad
  have hp : p < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hget : C.gates.get ⟨p,hp⟩ = g := by
    have ht : C.gates[p]? = some (C.gates.get ⟨p,hp⟩) :=
      List.getElem?_eq_some_iff.mpr ⟨hp,rfl⟩
    exact Option.some.inj (ht.symm.trans hg)
  have hex : Nonempty (JunkPosition F C) :=
    ⟨⟨⟨p,hp⟩,by simpa only [hget] using hand,hbad⟩⟩
  have hpos : 0 < unsafeAndCount F C := by
    simpa only [unsafeAndCount,Nat.card_eq_fintype_card] using
      Fintype.card_pos_iff.mpr hex
  omega

theorem safe_minimum_can_have_nonempty_star_owners {n : ℕ}
    (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (C0 : Circuit) (hmin0 : IsMinimalMonoCircuit n C0)
    (he0 : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = graphFn G x)
    (hAll0 : CountedBuilder.AllAndSafe (graphFn G) C0) :
    ∃ C : Circuit, IsMinimalMonoCircuit n C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFn G x) ∧
      C.size = C0.size ∧ CountedBuilder.AllAndSafe (graphFn G) C ∧
      ∀ t g, C.gates[t]? = some g → g.op = GateOp.and →
        ∃ c : Fin n, (∃ u v, G.Adj u v ∧ OwnsPair C t u v) ∧
          ∀ u v, G.Adj u v → OwnsPair C t u v → u = c ∨ v = c := by
  classical
  obtain ⟨C,hmin,he,hsize,hjunk,_,hN⟩ :=
    exists_minimum_junk_safe_forward (graphFn G) C0 hmin0.1 he0
  have hback : C0.size ≤ C.size := by
    apply hmin0.2 C hmin.1
    funext x
    exact (he x).trans (he0 x).symm
  have heq : C.size = C0.size := Nat.le_antisymm hsize hback
  have hcount : unsafeAndCount (graphFn G) C = 0 := by
    have hle := hjunk C0 hmin0.1 he0 heq.symm
    rw [allAndSafe_unsafeAndCount_zero hAll0] at hle
    omega
  have hAll := unsafeAndCount_zero_all_safe hcount
  refine ⟨C,hmin,he,heq,hAll,?_⟩
  intro t g hg hand
  have ht : t < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have hedge := minimum_graph_gate_has_edge hmin he ht
  exact minimum_all_safe_and_nonempty_stars G h4 hmin he hedge hN hAll t g hg hand

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem safe_least_suffices_for_full_star_ownership
    (hSoundLeast : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∃ C : Circuit, Monotone2 C ∧
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        (∀ D : Circuit, Monotone2 D →
          (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
            decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
          C.size ≤ D.size) ∧
        ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = true →
            ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  intro n G _ h3 h4
  obtain ⟨C0,hM0,he0,hsize0,hAll0⟩ := hSoundLeast n G h3 h4
  have hmin0 : IsMinimalMonoCircuit n C0 := by
    refine ⟨hM0,?_⟩
    intro D hD hfun
    apply hsize0 D hD
    intro x
    exact (congrFun hfun x).trans (he0 x)
  have hgraph : ∀x:Fin n→Bool,graphFn G x =
      decide (∃i j:Fin n,G.Adj i j ∧ x i=true ∧ x j=true) := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using graphFn_true G x
  have he0' : ∀ x : Fin n → Bool, C0.eval (List.ofFn x) = graphFn G x :=
    fun x => (he0 x).trans (hgraph x).symm
  have hAll0' : CountedBuilder.AllAndSafe (graphFn G) C0 := by
    intro t g hg hand x hx
    exact (graphFn_true G x).mpr (hAll0 t g hg hand x hx)
  obtain ⟨C,hmin,he,_,_,howns⟩ :=
    safe_minimum_can_have_nonempty_star_owners G h4 C0 hmin0 he0' hAll0'
  refine ⟨C,hmin.1,(fun x => (he x).trans (hgraph x)),?_,howns⟩
  intro D hD heD
  apply hmin.2 D hD
  funext x
  exact ((heD x).trans (hgraph x).symm).trans (he x).symm

end PEqualNP.Outside.L_meta_1031_aux

