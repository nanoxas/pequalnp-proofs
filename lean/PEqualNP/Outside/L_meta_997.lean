import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import PEqualNP.Defs.CircuitLowerBounds

-- Restricted two-window lower bound for Boolean sums.
-- The final theorems give the desk inequality for at most twenty-one inputs,
-- and whenever the witness has at most two points or n ≤ 7 times its size plus one and n+3 ≤ 8 times its size.
-- At 22 inputs the unrestricted inequality can miss by at most one gate.
-- The original inequality holds there when the refund count exceeds the number
-- of disjoint rows of size at least |y|+2 that lack a full private gate count.
-- At 22 inputs a single spare private gate for a row touching y also suffices.
-- Such a gate exists for a proper touching row longer than |y| with non-AND output.
-- At 22 inputs a violation also forces exactly two exceptional gates besides
-- the switch. They precede it, are false on every singleton, and are true on y.
-- Before the switch, no wire responds on two singleton inputs from an underpaid disjoint row.
-- The rigidity theorem specifies the two possible roles for each remaining gate.
-- The unrestricted L-meta-997 statement remains open.
-- This file builds on Apache-2.0 code by contributors to brilliant-hq/pequalnp-proofs.
-- L_meta_270.lean, restored by ilyasudakov in PR 805, supplies the small-cut counting argument.
-- L_meta_988.lean, RepoTactics in PR 2015, supplies the sound-wire count on a fixed window.
-- L_meta_1377.lean, psosnin in PR 2757, supplies circuit semantics and the constant-gate replacement.
-- These arguments are adapted here to handle both values of the constrained wire.
-- Source commits are 5c4c77a55bcf447311a2eb7e7a4c05c303856342,
-- 48a1a46a56b8b906a7e15b4f98bbceb16b50e5d2 and 98648e41435898c7dc1fe68d052bc233217cbe7a respectively.

namespace PEqualNP.Outside.L_meta_997.Light
-- Wire and replacement lemmas are adapted from L-meta-1377. The small-cut argument is from L-meta-270/988.
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def frozen (b : Bool) (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨if b then GateOp.and else GateOp.or, []⟩, 0⟩

lemma fixed_size (b : Bool) (gates : List Gate) (i0 : ℕ) : (frozen b gates i0).size = gates.length := by
  simp [frozen, Circuit.size]

lemma fixed_gates (b : Bool) (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (frozen b gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [frozen] using hk
  by_cases hki : i0.val = k
  · cases b <;> simp [frozen, hki]
  · have e : (frozen b gates i0.val).gates[k] = gates[k] := by
      simp [frozen, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma fixed_value {n : ℕ} (b : Bool) (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    value (frozen b gates i0.val) x (n + i0.val) = b := by
  have h := gate_value (frozen b gates i0.val) x (n + i0.val) (by omega)
    (by rw [fixed_size]; omega)
  simp only at h
  rw [h]
  cases b <;> simp [frozen, GateOp.eval]

lemma fixed_other {n : ℕ} (b : Bool) (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (frozen b gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (frozen b gates i0) x r else false) := by
  have h := gate_value (frozen b gates i0) x w hn (by rw [fixed_size]; exact hw)
  simp only at h
  rw [h]
  have e : (frozen b gates i0).gates[w - n]'(by simp [frozen]; omega) = gates[w - n]'(by omega) := by
    simp only [frozen, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma fixed_eq {n : ℕ} (b : Bool) (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = b) (w : ℕ) :
    value (frozen b gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (frozen b gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact fixed_value b gates i0 x
      · rw [orig_value gates o x w (by omega) hw, fixed_other b gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (frozen b gates i0.val) x w (by rw [fixed_size]; omega)]

lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def assigned {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C w ⊆ T ∧ 2 ≤ (support (n := n) C w).card

-- A small cut leaves some point of T uncovered by its clean wires.
-- Each other wire can be made true by a single point outside T.
lemma card_assigned {n k c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ T)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ T.card) : c ≤ (assigned C T).card := by
  classical
  let G := assigned C T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) := if support C w ⊆ T then support C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support C w ⊆ T
    · change (if support C w ⊆ T then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let D := B.filter (fun w => ¬ support C w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support C w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card ≤ k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ k := hb.trans hk
  have hyfalse : value C y o = false := by
    apply hsparse y
    · have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [y, hnot]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) ((ho p).mpr hp)
    intro w hw hx
    by_cases hs : support C w ⊆ T
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) y _ w ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [y, hm]
  simp [hyfalse] at hytrue

/-- On all inputs of weight strictly below `k`, the distinguished wire is true.
For a row OR, its clean singleton-support wires pay for `min k T.card - 1`. -/
theorem card_light {n k : ℕ} (T : Finset (Fin n)) (C : Circuit) (o t : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true) : min k T.card ≤ (assigned C T).card + 1 := by
  classical
  by_cases hk : 2 ≤ k
  swap
  · omega
  by_cases hT : 2 ≤ T.card
  swap
  · omega
  cases C with
  | mk gates o' =>
    let C : Circuit := ⟨gates,o'⟩
    have hvalid : t < gates.length := by
      by_contra! h
      have hf := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gates.length ≤ n+t; omega)
      have ht := hlight (fun _ : Fin n => false) (by simpa using (show 0 < k by omega))
      exact Bool.noConfusion (hf.symm.trans ht)
    let j : Fin gates.length := ⟨t,hvalid⟩
    let D := frozen true gates t
    have hd : good D := fixed_gates true gates j hg fun i hi => Fin.ext (hu i hi)
    have eq_light (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p : Fin n => x p = true)).card < k)
        (w : ℕ) : value D x w = value C x w := fixed_eq true gates j o' x (hlight x hx) w
    have es (p : Fin n) (w : ℕ) : value D (fun r => decide (r=p)) w = value C (fun r => decide (r=p)) w := by
      apply eq_light
      have hf : Finset.univ.filter (fun r : Fin n => decide (r=p) = true) = {p} := by ext a; simp
      rw [hf, Finset.card_singleton]
      omega
    have s_eq (w : ℕ) : support (n:=n) D w = support C w := by
      ext v
      rw [mem_support, mem_support, es]
    have assigned_eq : assigned D T = assigned C T := by
      ext w
      simp only [assigned, Finset.mem_filter, s_eq]
      rw [show D.size = C.size from fixed_size true gates t]
    have count := card_assigned (n:=n) (k:=k-1) (c:=min k T.card-1) D T o hd (by
      intro p
      rw [es, hout]
      simp) (by
      intro x hx hzero
      rw [eq_light x (by omega), hout]
      apply decide_eq_false
      rintro ⟨v,hv,ht⟩
      exact Bool.noConfusion ((hzero v hv).symm.trans ht)) (by omega) (by omega)
    rw [assigned_eq] at count
    change min k T.card ≤ (assigned C T).card + 1
    omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

/-- Count only the rows chosen for the light window. Their private gate sets are disjoint. -/
theorem sum_light {n m k : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true) : (∑ i ∈ I, min k (S i).card) ≤ (I.biUnion (fun i => assigned C (S i))).card + I.card := by
  classical
  let G := fun i => assigned C (S i)
  have hd : (↑I : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro w wi wj
    have ⟨hi,hs⟩ := (Finset.mem_filter.mp wi).2
    have hj := (Finset.mem_filter.mp wj).2.1
    have hsub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi hp,hj hp⟩
    have := hs.trans ((Finset.card_le_card hsub).trans (hpair i j hij))
    omega
  have per := Finset.sum_le_sum (s:=I) (fun i _ => card_light (k:=k) (S i) C (o i) t hg hu (hout i) hlight)
  change _ ≤ (I.biUnion G).card + I.card
  rw [Finset.card_biUnion hd]
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one, G] using per

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

noncomputable def refunds {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (y : Finset (Fin n)) :
    Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun g =>
    (∃ i, ∀ p : Fin n, value C (fun v => decide (v = p)) (n+g.val) = true ↔ p ∈ S i) ∧
    (∃ i, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
      (value C (fun v => decide (v ∈ y ∨ v = p)) (n+g.val) = true ↔ p ∈ S i))

/-- Each disjoint row of size at least two contributes its own output wire to the refund. -/
theorem disjoint_outputs_refunded {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (y : Finset (Fin n)) (D : Finset (Fin m))
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hD : ∀ i ∈ D, Disjoint (S i) y ∧ 2 ≤ (S i).card) : D.card ≤ (refunds S C y).card := by
  classical
  have hs (i : Fin m) : support C (o i) = S i := by
    ext p
    rw [mem_support, hout]
    simp
  have ho (u : {i // i ∈ D}) : n ≤ o u.val ∧ o u.val < n+C.size :=
    support_gate C _ (by simpa only [hs] using (hD u.val u.property).2)
  let f (u : {i // i ∈ D}) : Fin C.gates.length := ⟨o u.val - n, by
    have lo := (ho u).1
    have h := (ho u).2
    change o u.val < n+C.gates.length at h
    omega⟩
  have hw (u : {i // i ∈ D}) : n+(f u).val = o u.val := by have h := (ho u).1; dsimp [f]; omega
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    by_contra h
    have hw' : o a.val = o b.val := (hw a).symm.trans ((congrArg (fun g : Fin C.gates.length => n+g.val) he).trans (hw b))
    have hS : S a.val = S b.val := by rw [← hs a.val, ← hs b.val, hw']
    have step := hpair a.val b.val h
    rw [← hS, Finset.inter_self] at step
    have := (hD a.val a.property).2
    omega
  calc
    D.card = D.attach.card := Finset.card_attach.symm
    _ = (D.attach.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ (refunds S C y).card := Finset.card_le_card (by
      intro g hg
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hg
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ⟨a.val,?_⟩,a.val,(hD a.val a.property).1,?_⟩
      · intro p
        rw [hw,← mem_support,hs]
      · intro p _
        rw [hw,hout,decide_eq_true_eq]
        constructor
        · rintro ⟨v,hv,ht⟩
          rcases of_decide_eq_true ht with hy | h
          · exact False.elim (Finset.disjoint_left.mp (hD a.val a.property).1 hv hy)
          · simpa [← h] using hv
        · exact fun hp => ⟨p,hp,by simp⟩)

theorem window_bound_one_extra {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hOne : ∀ i : Fin m, Disjoint (S i) y → (S i).card ≤ y.card+1) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length+(refunds S C y).card+m := by
  classical
  by_cases hy : y.card = 0
  · have hh := Finset.sum_le_sum (s:= (Finset.univ : Finset (Fin m))) (fun i _ =>
        (show (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ 1 by
          split <;> rename_i h
          · simpa [hy] using hOne i h
          · simp [hy]))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] at hh
    omega
  let D := Finset.univ.filter fun i => Disjoint (S i) y ∧ y.card < (S i).card
  have hD (i) (hi : i ∈ D) : Disjoint (S i) y ∧ 2 ≤ (S i).card := by
    obtain ⟨hd, hlt⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨hd,by omega⟩
  have hrefund := disjoint_outputs_refunded S C o y D hpair hout hD
  have hper (i : Fin m) : (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      min y.card (S i).card + (if i ∈ D then 1 else 0) := by
    by_cases hd : Disjoint (S i) y
    · have h := hOne i hd
      by_cases hs : y.card < (S i).card <;> simp [D,hd,hs] <;> omega
    · simp [D,hd]
  have hadd := Finset.sum_le_sum (s:= (Finset.univ : Finset (Fin m))) (fun i _ => hper i)
  rw [Finset.sum_add_distrib] at hadd
  have hbool : (∑ i : Fin m, if i ∈ D then 1 else 0) = D.card := by simp
  rw [hbool] at hadd
  have hsum := sum_light S Finset.univ C o t hpair hg hu hout hlight
  have hgate : (Finset.univ.biUnion (fun i => assigned C (S i))).card ≤ C.gates.length := by
    calc
      _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card (by
        intro w hw
        obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
        exact (Finset.mem_filter.mp hi).1)
      _ = C.gates.length := by simp [Circuit.size]
  simp only [Finset.card_univ, Fintype.card_fin] at hsum
  omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

def dormant {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n+C.size)).filter fun w => value C (fun _ : Fin n => false) w = false ∧ 2 ≤ (support C w ∩ T).card

lemma dormant_count {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hg : good C)
    (ho : ∀ p ∈ T, value C (fun v => decide (v=p)) o = true)
    (hz : value C (fun _ : Fin n => false) o = false) :
    T.card ≤ (dormant C T).card+1 := by
  classical
  let G := dormant C T
  have hG (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size :=
    Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B,hd,hcap,transfer⟩ := cut C hg G hG (n+C.size) {o}
      (fun w _ hw => (hG w hw).2)
  let f := fun w => if value C (fun _ : Fin n => false) w = false then support C w ∩ T else ∅
  have hone (w : ℕ) (hw : w ∈ B) : (f w).card ≤ 1 := by
    by_contra! h
    by_cases hb : value C (fun _ : Fin n => false) w = false
    · have hbnd : 1 < (support C w ∩ T).card := by simpa [f,hb] using h
      have hl : 2 ≤ (support C w ∩ T).card := by omega
      have h2 : 2 ≤ (support (n:=n) C w).card := hl.trans (Finset.card_le_card Finset.inter_subset_left)
      have hin : w ∈ G := Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w h2),hb,hl⟩
      exact Finset.disjoint_left.mp hd hw hin
    · simp [f,hb] at h
  have sub : T ⊆ B.biUnion f := by
    intro p hp
    by_contra hno
    have hgo := transfer (fun v => decide (v=p)) (fun _ => false) (by
      intro w hw hsw
      by_cases hb : value C (fun _ : Fin n => false) w = false
      · apply False.elim (hno (Finset.mem_biUnion.mpr ⟨w,hw,?_⟩))
        simpa [f,hb] using Finset.mem_inter.mpr ⟨(mem_support C w p).mpr hsw,hp⟩
      · simpa using hb) o (by simp) (ho p hp)
    simp [hz] at hgo
  have h1 := Finset.card_le_card sub
  have h2 := Finset.card_biUnion_le_card_mul B f 1 hone
  have h3 := Finset.card_filter_le G (fun w => w < n+C.size)
  change T.card ≤ G.card+1
  simp only [Finset.card_singleton] at hcap
  simp only [Nat.mul_one] at h2
  omega

lemma low_dormant_count {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true) : T.card ≤ (dormant C T).card+1 := by
  classical
  cases C with
  | mk gates o' =>
    let C : Circuit := ⟨gates,o'⟩
    have hvalid : t < gates.length := by
      by_contra! h
      have hf := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gates.length ≤ n+t; omega)
      have ht := hlight (fun _ : Fin n => false) (by simpa using (show 0 < k by omega))
      exact Bool.noConfusion (hf.symm.trans ht)
    let j : Fin gates.length := ⟨t,hvalid⟩
    let D := frozen true gates t
    have hd : good D := fixed_gates true gates j hg fun i hi => Fin.ext (hu i hi)
    have eq_light (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p = true)).card < k)
        (w : ℕ) : value D x w = value C x w := fixed_eq true gates j o' x (hlight x hx) w
    have es (p : Fin n) (w : ℕ) : value D (fun r => decide (r=p)) w = value C (fun r => decide (r=p)) w := by
      apply eq_light
      have hf : Finset.univ.filter (fun r : Fin n => decide (r=p) = true) = {p} := by ext a; simp
      rw [hf,Finset.card_singleton]
      omega
    have sp (w : ℕ) : support (n:=n) D w = support C w := by
      ext p
      rw [mem_support, mem_support, es]
    have hsame : dormant D T = dormant C T := by
      ext w
      have ez := eq_light (fun _ => false) (by simpa using (show 0 < k by omega)) w
      simp only [dormant,Finset.mem_filter,sp,ez]
      rw [show D.size = C.size from fixed_size true gates t]
    have hr := dormant_count D T o hd (by
      intro p hp
      rw [es,hout]
      simpa using hp) (by
      rw [eq_light _ (by simpa using (show 0 < k by omega)),hout]
      simp)
    rwa [hsame] at hr

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma prefix_value_eq {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + j.val) :
    value ⟨gates,0⟩ x w = value ⟨gates.take j.val,0⟩ x w := by
  change (run gates (List.ofFn x)).getD w false = (run (gates.take j.val) (List.ofFn x)).getD w false
  rw [run_split gates (List.ofFn x) j.val]
  exact run_getD _ _ _ (by simpa [run_length, Nat.min_eq_left j.isLt.le] using hw)

lemma pre_basis (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ k : Fin gates.length, (gates.get k).op = .not → k = j) :
    ∀ g ∈ gates.take j.val, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hgin
  obtain ⟨a, ha, hag⟩ := List.mem_iff_getElem.mp hgin
  have haj : a < j.val := by simpa [List.length_take, Nat.min_eq_left j.isLt.le] using ha
  let k : Fin gates.length := ⟨a, lt_trans haj j.isLt⟩
  have hkg : gates.get k = g := by simpa [k] using hag
  obtain ⟨hop, hw⟩ := hg g (List.mem_of_mem_take hgin)
  refine ⟨?_, hw⟩
  rcases hop with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have heq := huniq k (by simpa only [hkg] using h)
    have := congrArg Fin.val heq
    change a = j.val at this
    omega

lemma not_value_prefix {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hj : (gates.get j).op = .not) (x : Fin n → Bool) :
    value ⟨gates, 0⟩ x (n + j.val) =
      !(value ⟨gates.take j.val, 0⟩ x ((gates.get j).inputs.headD (n + j.val))) := by
  let z := n + j.val
  have gone : z - n = j.val := by dsimp [z]; omega
  have hg := gate_value (⟨gates, 0⟩ : Circuit) x z (by dsimp [z]; omega)
    (by change z < n + gates.length; dsimp [z]; omega)
  change value ⟨gates, 0⟩ x z = _
  have hidx : z - n < gates.length := by rw [gone]; exact j.isLt
  have hget : gates[z - n] = gates.get j := by simp [gone]
  change value ⟨gates, 0⟩ x z = GateOp.eval (gates[z - n]).op
    ((gates[z - n]).inputs.map fun r => if r < z then value ⟨gates, 0⟩ x r else false) at hg
  rw [hg, hget, hj]
  have hmiss (r : ℕ) (hr : z ≤ r) : value ⟨gates.take j.val, 0⟩ x r = false := by
    apply missing_value
    simpa [Circuit.size, List.length_take, Nat.min_eq_left j.isLt.le, z] using hr
  have hr (r : ℕ) :
      (if r < z then value ⟨gates, 0⟩ x r else false) = value ⟨gates.take j.val, 0⟩ x r := by
    by_cases h : r < z
    · rw [ite_eq_left h, prefix_value_eq gates j x r h]
    · rw [ite_eq_right h, hmiss r (by omega)]
  cases hi : (gates.get j).inputs with
  | nil =>
    change true = !(value ⟨gates.take j.val, 0⟩ x z)
    rw [hmiss z (Nat.le_refl _)]
    rfl
  | cons r rs =>
    change (!(if r < z then value ⟨gates, 0⟩ x r else false)) = !(value ⟨gates.take j.val, 0⟩ x r)
    rw [hr]

def emptyGates {n : ℕ} (C : Circuit) : Finset ℕ :=
  (Finset.Ico n (n+C.size)).filter fun w => support (n:=n) C w = ∅

lemma mintrue_empty_count {n k : ℕ} (C : Circuit) (hg : good C) (w : ℕ) (y : Fin n → Bool)
    (hy : value C y w = true)
    (hsmall : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x w = false) : k ≤ (emptyGates (n:=n) C).card + 1 := by
  classical
  let G := emptyGates (n:=n) C
  have hG (a) (ha : a ∈ G) : n ≤ a ∧ a < n+C.size := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
  obtain ⟨B,hd,hcap,transfer⟩ := cut C hg G hG (n+C.size) {w} (fun a _ ha => (hG a ha).2)
  let U := B.filter fun a => value C y a = true
  have hex (a : {a // a ∈ U}) : ∃ p : Fin n, p ∈ support C a.val := by
    have hdata := Finset.mem_filter.mp a.property
    by_cases hhi : a.val < n+C.size
    · by_cases hin : a.val < n
      · let p : Fin n := ⟨a.val,hin⟩
        refine ⟨p,(mem_support C a.val p).mpr ?_⟩
        exact (input_value C (fun v => decide (v=p)) p).trans (by simp)
      · by_contra! hemp
        have he : support (n:=n) C a.val = ∅ := Finset.eq_empty_iff_forall_notMem.mpr hemp
        exact Finset.disjoint_left.mp hd hdata.1
          (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,hhi⟩,he⟩)
    · have hf := missing_value C y a.val (by omega)
      exact False.elim (Bool.noConfusion (hf.symm.trans hdata.2))
  choose pt hpt using hex
  let X := U.attach.image pt
  let x := fun p : Fin n => decide (p ∈ X)
  have hxx : Finset.univ.filter (fun p => x p = true) = X := by ext p; simp [x]
  have hp (a) (ha : a ∈ B) (ht : value C y a = true) : value C x a = true := by
    let a' : {a // a ∈ U} := ⟨a,Finset.mem_filter.mpr ⟨ha,ht⟩⟩
    have hmem : pt a' ∈ X := Finset.mem_image.mpr ⟨a',Finset.mem_attach _ _,rfl⟩
    apply value_mono C hg (fun v => decide (v=pt a')) x _ a ((mem_support C a (pt a')).mp (hpt a'))
    intro v hv
    have he : v = pt a' := of_decide_eq_true hv
    simpa [x,he] using hmem
  have ht := transfer y x hp w (by simp) hy
  have hlow : k ≤ X.card := by
    by_contra! h
    have hf := hsmall x (by rwa [hxx])
    exact Bool.noConfusion (hf.symm.trans ht)
  have hU : X.card ≤ B.card := calc
    _ ≤ U.attach.card := Finset.card_image_le
    _ = U.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
  have h3 := Finset.card_filter_le G (fun w => w < n+C.size)
  change k ≤ G.card+1
  simp only [Finset.card_singleton] at hcap
  omega

lemma guard_empty_gates {n k : ℕ} (C : Circuit) (t : ℕ) (y : Finset (Fin n)) (hk : 0 < k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false) :
    ∃ A : Finset ℕ, k ≤ A.card+1 ∧ A ⊆ Finset.Ico n (n+t) ∧
      ∀ w ∈ A, support (n:=n) C w = ∅ := by
  classical
  cases C with
  | mk gates out =>
    let C : Circuit := ⟨gates,out⟩
    have h0 := hl (fun _ => false) (by simpa using hk)
    have hvalid : t < gates.length := by
      by_contra! h
      have hf := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gates.length ≤ n+t; omega)
      exact Bool.noConfusion (hf.symm.trans h0)
    let j : Fin gates.length := ⟨t,hvalid⟩
    have hj : (gates.get j).op = .not := by
      by_contra hn
      have hm : good C := by
        intro g hgin
        obtain ⟨hops,hlen⟩ := hg g hgin
        refine ⟨?_,hlen⟩
        rcases hops with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp hgin
          have hop : (gates.get (⟨a,ha⟩ : Fin gates.length)).op = .not := (congrArg Gate.op he).trans h
          have hidx := hu ⟨a,ha⟩ hop
          have ej : (⟨a,ha⟩ : Fin gates.length) = j := Fin.ext hidx
          exact False.elim (hn (ej ▸ hop))
      have hh := value_mono C hm (fun _ => false) (fun p => decide (p ∈ y)) (by simp) (n+t) h0
      exact Bool.noConfusion (hy.symm.trans hh)
    let P : Circuit := ⟨gates.take t,0⟩
    let w := (gates.get j).inputs.headD (n+t)
    have hnot (x : Fin n → Bool) : value C x (n+t) = !(value P x w) := not_value_prefix gates j hj x
    have hw : value P (fun p => decide (p ∈ y)) w = true := by
      change value C _ (n+t) = false at hy
      rw [hnot] at hy
      simpa using hy
    have hsmall (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p = true)).card < k) :
        value P x w = false := by
      have h := hl x hx
      change value C x (n+t) = true at h
      rw [hnot] at h
      simpa using h
    have hgood : good P := pre_basis gates j hg (fun a ha => Fin.ext (hu a ha))
    refine ⟨emptyGates (n:=n) P,mintrue_empty_count P hgood w _ hw hsmall,?_,?_⟩
    · intro v hv
      have h := (Finset.mem_filter.mp hv).1
      simpa [P,Circuit.size,List.length_take,Nat.min_eq_left hvalid.le] using h
    · intro v hv
      have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp hv).1
      have vlt : v < n+t := by simpa [P,Circuit.size,List.length_take,Nat.min_eq_left hvalid.le] using hi.2
      have es : support (n:=n) C v = support P v := by
        ext p
        rw [mem_support,mem_support]
        rw [show value C (fun a => decide (a=p)) v = value P _ v from prefix_value_eq gates j _ _ vlt]
      exact es.trans (Finset.mem_filter.mp hv).2

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma exceptional_count_reserve {n m k : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ k) (hD : 2 ≤ (S d).card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false) :
    (S d).card + (∑ i ∈ Finset.univ.erase d, min k (S i).card) + k ≤ C.gates.length + m := by
  classical
  let I := Finset.univ.erase d
  let U := I.biUnion (fun i => assigned C (S i))
  let G := dormant C (S d)
  have dis : Disjoint U G := by
    apply Finset.disjoint_left.mpr
    intro w hu hg'
    obtain ⟨i,hi,hwi⟩ := Finset.mem_biUnion.mp hu
    have ha := (Finset.mem_filter.mp hwi).2.1
    have hc := (Finset.mem_filter.mp hg').2.2
    have hs : support C w ∩ S d ⊆ S i ∩ S d := fun v hv =>
      Finset.mem_inter.mpr ⟨ha (Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩
    have hd := hpair i d (Finset.mem_erase.mp hi).1
    have hsmall := (Finset.card_le_card hs).trans hd
    omega
  let z := n+t
  have htz := hlight (fun _ => false) (by simpa using (show 0 < k by omega))
  have hzrange : z ∈ Finset.Ico n (n+C.size) := by
    apply Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _,?_⟩
    by_contra! hn
    have hf := missing_value C (fun _ : Fin n => false) z hn
    exact Bool.noConfusion (hf.symm.trans htz)
  have hzs : ∀ p : Fin n, p ∈ support C z := by
    intro p
    apply (mem_support C z p).mpr
    apply hlight
    have h : Finset.univ.filter (fun v : Fin n => decide (v=p) = true) = {p} := by ext v; simp
    rw [h,Finset.card_singleton]
    omega
  have hnotin : z ∉ U ∪ G := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i,hi,hw⟩ := Finset.mem_biUnion.mp h
      have ha := (Finset.mem_filter.mp hw).2.1
      have ts : S d ⊆ S i ∩ S d := fun p hp => Finset.mem_inter.mpr ⟨ha (hzs p),hp⟩
      have small := (Finset.card_le_card ts).trans (hpair i d (Finset.mem_erase.mp hi).1)
      omega
    · have hz := (Finset.mem_filter.mp h).2.1
      exact Bool.noConfusion (hz.symm.trans htz)
  obtain ⟨A,hkA,hAi,hAs⟩ := guard_empty_gates C t y (by omega : 0 < k) hg hu hlight hy
  let W := insert z (U ∪ G)
  have disA : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro w wa ww
    rcases Finset.mem_insert.mp ww with hz | h
    · have hi := (Finset.mem_Ico.mp (hAi wa)).2
      change w < z at hi
      omega
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i,_,hw⟩ := Finset.mem_biUnion.mp h
        have hc := (Finset.mem_filter.mp hw).2.2
        rw [hAs w wa] at hc
        simp at hc
      · have hc := (Finset.mem_filter.mp h).2.2
        rw [hAs w wa] at hc
        simp at hc
  have hgate : A.card + (U.card + G.card + 1) ≤ C.gates.length := by
    calc
      _ = (A ∪ W).card := by
        rw [Finset.card_union_of_disjoint disA]
        simp only [W,Finset.card_insert_of_notMem hnotin,Finset.card_union_of_disjoint dis]
      _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card (by
        intro w hw
        rcases Finset.mem_union.mp hw with ha | hw
        · obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp (hAi ha)
          exact Finset.mem_Ico.mpr ⟨lo,hi.trans (Finset.mem_Ico.mp hzrange).2⟩
        · rcases Finset.mem_insert.mp hw with h | hw
          · exact h ▸ hzrange
          · rcases Finset.mem_union.mp hw with hw | hw
            · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
              exact (Finset.mem_filter.mp hi).1
            · exact (Finset.mem_filter.mp hw).1)
      _ = C.gates.length := by simp [Circuit.size]
  have hcard := Finset.card_erase_add_one (Finset.mem_univ d)
  change I.card + 1 = _ at hcard
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  have hgeneral := sum_light S I C o t hpair hg hu hout hlight
  change (∑ i ∈ I, min k (S i).card) ≤ U.card + I.card at hgeneral
  have hspecial := low_dormant_count C (S d) (o d) t hk hg hu (hout d) hlight
  change (S d).card ≤ G.card + 1 at hspecial
  change (S d).card + (∑ i ∈ I, min k (S i).card) + k ≤ _
  omega

lemma window_bound_reserve {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card) (hD : 2 ≤ (S d).card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (he : (∑ i, if Disjoint (S i) y then (S i).card-y.card else 0) ≤
      ((S d).card-y.card) + (refunds S C y).card + y.card) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  let f := fun i : Fin m => min y.card (S i).card
  let e := fun i : Fin m => if Disjoint (S i) y then (S i).card-y.card else 0
  have per (i : Fin m) : (if Disjoint (S i) y then (S i).card else min y.card (S i).card) =
      f i + e i := by
    by_cases h : Disjoint (S i) y
    · simp [f,e,h]; omega
    · simp [f,e,h]
  have hsum := Finset.sum_congr (s₁:=(Finset.univ : Finset (Fin m))) rfl (fun i _ => per i)
  rw [Finset.sum_add_distrib] at hsum
  have hall := exceptional_count_reserve S d C o t y hk hD hpair hg hu hout hlight hy
  change (S d).card + (∑ i ∈ Finset.univ.erase d, f i) + y.card ≤ _ at hall
  change (∑ i, e i) ≤ _ at he
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) f (Finset.mem_univ d)
  have hd : (S d).card = f d + ((S d).card-y.card) := by dsimp [f]; omega
  omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997_aux.Heavy
open PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

def sound {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, value C x w = true → ∃ p ∈ T, x p = true

def supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun v => decide (v ∈ Y ∨ v = p)) w = true)

lemma mem_supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ supp C Y w ↔ value C (fun v => decide (v ∈ Y ∨ v = p)) w = true := by
  simp [supp]

noncomputable def asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (fun w => sound C T w ∧ 2 ≤ (supp C Y w).card)

lemma mem_asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) :
    w ∈ asg C Y T ↔ (n ≤ w ∧ w < n + C.size) ∧ sound C T w ∧ 2 ≤ (supp C Y w).card := by
  classical
  unfold asg
  rw [Finset.mem_filter, Finset.mem_Ico]

lemma supp_gate {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) (hYT : Disjoint Y T)
    (hs : sound C T w) (h2 : 2 ≤ (supp C Y w).card) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p0 : Fin n := ⟨w, hw⟩
    have hY : p0 ∉ Y := by
      intro hp0
      have hv : value C (fun v => decide (v ∈ Y)) w = true := by
        change value C (fun v => decide (v ∈ Y)) p0 = true
        rw [input_value]
        simpa using hp0
      obtain ⟨q, hqT, hqY⟩ := hs _ hv
      exact Finset.disjoint_left.mp hYT (by simpa using hqY) hqT
    have hsub : supp C Y w ⊆ {p0} := by
      intro q hq
      have hv := (mem_supp C Y w q).mp hq
      change value C (fun v => decide (v ∈ Y ∨ v = q)) p0 = true at hv
      rw [input_value] at hv
      simp only [decide_eq_true_eq] at hv
      rcases hv with hv | hv
      · exact absurd hv hY
      · simp [hv]
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_contra! hw
    have hs0 : supp (n := n) C Y w = ∅ := by
      ext q
      simp [mem_supp, missing_value C _ w hw]
    simp [hs0] at h2

lemma card_le {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (o : ℕ) (hYT : Disjoint Y T) (hso : sound C T o)
    (hfire : ∀ p ∈ T, value C (fun v => decide (v ∈ Y ∨ v = p)) o = true) :
    T.card ≤ (asg C Y T).card + 1 := by
  classical
  let G := asg C Y T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw => ((mem_asg C Y T w).mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean (w : ℕ) : Finset (Fin n) := if sound C T w then supp C Y w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : sound C T w
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      have hg := supp_gate C Y T w hYT hs (by omega)
      exact Finset.disjoint_left.mp hd hw ((mem_asg C Y T w).mpr ⟨hg, hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    have hG' : G.card + 1 < T.card := hsmall
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dn := B.filter (fun w => ¬ sound C T w)
  have hout (w : {w // w ∈ Dn}) :
      ∃ x : Fin n → Bool, value C x w.val = true ∧ ∀ q ∈ T, x q = false := by
    have hns := (Finset.mem_filter.mp w.property).2
    unfold sound at hns
    push Not at hns
    obtain ⟨x, hx, hxT⟩ := hns
    exact ⟨x, hx, fun q hq => by simpa using hxT q hq⟩
  choose xs hxs using hout
  let z : Fin n → Bool := fun v => decide (v ∈ Y ∨ ∃ d : {w // w ∈ Dn}, xs d v = true)
  have hzfalse : value C z o = false := by
    by_contra hne
    have ht : value C z o = true := by simpa using hne
    obtain ⟨q, hqT, hzq⟩ := hso z ht
    simp only [z, decide_eq_true_eq] at hzq
    rcases hzq with hqY | ⟨d, hd'⟩
    · exact Finset.disjoint_left.mp hYT hqY hqT
    · rw [(hxs d).2 q hqT] at hd'
      exact Bool.false_ne_true hd'
  have hztrue : value C z o = true := by
    apply hcut (fun v => decide (v ∈ Y ∨ v = p)) z _ o (Finset.mem_singleton_self o) (hfire p hp)
    intro w hw hx
    by_cases hs : sound C T w
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_supp C Y w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (xs d) z _ w (hxs d).1
      intro v hv
      simp only [z, decide_eq_true_eq]
      exact Or.inr ⟨d, hv⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

noncomputable def heavyG {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (fun w =>
    supp C Y w ⊆ T ∧ 2 ≤ (supp C Y w).card ∧ value C (fun q : Fin n => decide (q ∈ Y)) w = false)

lemma heavy_per {n : ℕ} (C D : Circuit) (Y T : Finset (Fin n)) (o : ℕ)
    (hlen : D.size = C.size)
    (hG : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hagree : ∀ (x : Fin n → Bool), (∀ v ∈ Y, x v = true) → ∀ w, value D x w = value C x w)
    (hd : Disjoint Y T)
    (houtput : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true)) :
    T.card ≤ (heavyG C Y T).card + 1 := by
  classical
  have hs : sound D T o := by
    intro x hx
    let z (p : Fin n) := x p || decide (p ∈ Y)
    have h := value_mono D hG x z (fun p hxp => by simp [z,hxp]) o hx
    rw [hagree z (fun p hp => by simp [z,hp]), houtput] at h
    obtain ⟨p,hp,ht⟩ := of_decide_eq_true h
    refine ⟨p,hp,?_⟩
    have hn : p ∉ Y := fun hY => Finset.disjoint_left.mp hd hY hp
    simpa [z,hn] using ht
  have htest (p : Fin n) (w : ℕ) :
      value D (fun v => decide (v ∈ Y ∨ v = p)) w =
      value C (fun v => decide (v ∈ Y ∨ v = p)) w :=
    hagree _ (fun q hq => by simp [hq]) w
  have hfire (p : Fin n) (hp : p ∈ T) :
      value D (fun v => decide (v ∈ Y ∨ v = p)) o = true := by
    rw [htest, houtput]
    exact decide_eq_true ⟨p,hp,by simp⟩
  apply (card_le D hG Y T o hd hs hfire).trans
  apply Nat.add_le_add_right
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hr, hsw, hk⟩ := (mem_asg D Y T w).mp hw
  have heq : supp D Y w = supp C Y w := by
    ext p
    rw [mem_supp,mem_supp,htest]
  have hbase : value C (fun q : Fin n => decide (q ∈ Y)) w = false := by
    apply Bool.eq_false_iff.mpr
    intro hon
    rw [← hagree _ (fun q hq => by simpa using hq) w] at hon
    obtain ⟨p,hp,hpY⟩ := hsw _ hon
    exact Finset.disjoint_left.mp hd (of_decide_eq_true hpY) hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hr.1, by simpa only [hlen] using hr.2⟩,?_,by simpa only [← heq] using hk,hbase⟩
  intro p hp
  have ht := (mem_supp D Y w p).mp (heq.symm ▸ hp)
  obtain ⟨q,hq,hon⟩ := hsw _ ht
  rcases of_decide_eq_true hon with hq' | rfl
  · exact False.elim (Finset.disjoint_left.mp hd hq' hq)
  · exact hq

lemma heavy_disjoint {n : ℕ} (C : Circuit) (Y T U : Finset (Fin n))
    (h : (T ∩ U).card ≤ 1) : Disjoint (heavyG C Y T) (heavyG C Y U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hw hv
  obtain ⟨_, hs, hk, _⟩ := Finset.mem_filter.mp hw
  obtain ⟨_, hu, _⟩ := Finset.mem_filter.mp hv
  have hsub : supp C Y w ⊆ T ∩ U := fun x hx => Finset.mem_inter.mpr ⟨hs hx,hu hx⟩
  have := (Finset.card_le_card hsub).trans h
  omega

lemma heavy_window {n m : ℕ} (C D : Circuit) (Y : Finset (Fin n))
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hlen : D.size = C.size)
    (hG : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hagree : ∀ (x : Fin n → Bool), (∀ v ∈ Y, x v = true) → ∀ w, value D x w = value C x w)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (houtput : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    let H := Finset.univ.filter (fun i => Disjoint Y (S i))
    (∑ i ∈ H, ((S i).card - 1)) ≤ (H.biUnion (fun i => heavyG C Y (S i))).card := by
  classical
  let H := Finset.univ.filter (fun i => Disjoint Y (S i))
  change (∑ i ∈ H, ((S i).card - 1)) ≤ (H.biUnion (fun i => heavyG C Y (S i))).card
  have hpair : (H : Set (Fin m)).PairwiseDisjoint (fun i => heavyG C Y (S i)) := by
    intro i _ j _ hij
    exact heavy_disjoint C Y (S i) (S j) (hlin i j hij)
  rw [Finset.card_biUnion hpair]
  apply Finset.sum_le_sum
  intro i hi
  have h := heavy_per C D Y (S i) (o i) hlen hG hagree (Finset.mem_filter.mp hi).2 (houtput i)
  omega

lemma heavy_model {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false) :
    ∃ D : Circuit, D.size = C.size ∧
      (∀ g ∈ D.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ∀ (x : Fin n → Bool), (∀ v ∈ Y, x v = true) → ∀ w, value D x w = value C x w := by
  classical
  cases C with
  | mk gates out =>
    by_cases hnot : ∃ i : Fin gates.length, (gates.get i).op = .not
    · obtain ⟨j,hj⟩ := hnot
      have ht := hu j hj
      subst t
      have hu' : ∀ i : Fin gates.length, (gates.get i).op = .not → i = j :=
        fun i hi => Fin.ext (hu i hi)
      refine ⟨frozen false gates j.val, fixed_size false gates j.val, fixed_gates false gates j hg hu', ?_⟩
      intro x hx w
      apply fixed_eq false gates j out x _ w
      change value ⟨gates,0⟩ x (n + j.val) = false
      change value ⟨gates,0⟩ (fun p : Fin n => decide (p ∈ Y)) (n + j.val) = false at hy
      rw [not_value_prefix gates j hj] at hy ⊢
      have hbase : value ⟨gates.take j.val,0⟩ (fun p : Fin n => decide (p ∈ Y))
          ((gates.get j).inputs.headD (n+j.val)) = true := by simpa using hy
      have hhigh := value_mono ⟨gates.take j.val,0⟩ (pre_basis gates j hg hu')
        (fun p : Fin n => decide (p ∈ Y)) x (fun p hp => hx p (of_decide_eq_true hp)) _ hbase
      rw [hhigh]
      rfl
    · refine ⟨⟨gates,out⟩,rfl,?_,fun _ _ _ => rfl⟩
      intro g hmem
      obtain ⟨hop, hlen⟩ := hg g hmem
      refine ⟨?_,hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hmem
        exact False.elim (hnot ⟨⟨i,hi⟩, by simpa only [List.get_eq_getElem, he] using h⟩)

lemma heavy_original {n m : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (houtput : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    let H := Finset.univ.filter (fun i => Disjoint Y (S i))
    (∑ i ∈ H, ((S i).card - 1)) ≤ (H.biUnion (fun i => heavyG C Y (S i))).card := by
  obtain ⟨D,hlen,hgood,hagree⟩ := heavy_model C Y t hg hu hy
  exact heavy_window C D Y S o hlen hgood hagree hlin houtput

theorem heavy_charge_set {n m : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (houtput : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    ∃ U : Finset (Fin C.gates.length),
      (∀ g ∈ U, (C.wires (List.ofFn (fun p : Fin n => decide (p ∈ Y)))).getD (n + g.val) false = false) ∧
      (∑ i ∈ Finset.univ.filter (fun i => Disjoint (S i) Y), ((S i).card-1)) ≤ U.card := by
  classical
  let U := Finset.univ.filter (fun g : Fin C.gates.length => value C (fun p : Fin n => decide (p ∈ Y)) (n + g.val) = false)
  refine ⟨U,fun g hg => (Finset.mem_filter.mp hg).2,?_⟩
  have hb := heavy_original C Y t S o hg hu hy hlin houtput
  let H := Finset.univ.filter (fun i => Disjoint Y (S i))
  change (∑ i ∈ H, ((S i).card-1)) ≤ (H.biUnion (fun i => heavyG C Y (S i))).card at hb
  have hc : H.biUnion (fun i => heavyG C Y (S i)) ⊆ U.image (fun g => n + g.val) := by
    intro w hw
    obtain ⟨i,_, hi⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hr,_,_,hv⟩ := Finset.mem_filter.mp hi
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hr
    change w < n + C.gates.length at hhi
    let g : Fin C.gates.length := ⟨w-n,by omega⟩
    have he : n + g.val = w := by dsimp [g]; omega
    exact Finset.mem_image.mpr ⟨g,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he ▸ hv⟩,he⟩
  have ht := hb.trans ((Finset.card_le_card hc).trans Finset.card_image_le)
  simpa only [H, disjoint_comm] using ht

end PEqualNP.Outside.L_meta_997_aux.Heavy

namespace PEqualNP.Outside.L_meta_997_refund
open PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma output_singleton {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (p : Fin n) : value C (fun v => decide (v = p)) (o i) = true ↔ p ∈ S i := by
  rw [out]; simp

lemma output_gate_of_card_two {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (hc : 2 ≤ (S i).card) : n ≤ o i ∧ o i < n + C.gates.length := by
  constructor
  · by_contra! h
    let q : Fin n := ⟨o i,h⟩
    have sub : S i ⊆ {q} := by
      intro p hp
      have on := (output_singleton S C o out i p).2 hp
      change value C (fun v : Fin n => decide (v = p)) q.val = true at on
      rw [input_value] at on
      exact Finset.mem_singleton.mpr (of_decide_eq_true on).symm
    have hle := Finset.card_le_card sub
    simp only [Finset.card_singleton] at hle
    omega
  · by_contra! h
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (S i).card by omega)
    have on := (output_singleton S C o out i p).2 hp
    rw [missing_value C _ _ h] at on
    contradiction

lemma output_ne_of_nontrivial {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hcross : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i j : Fin m) (hc : 2 ≤ (S i).card) (hne : i ≠ j) : o i ≠ o j := by
  intro oe
  have sub : S i ⊆ S i ∩ S j := by
    intro p hp
    have on := (output_singleton S C o out i p).2 hp
    rw [oe] at on
    exact Finset.mem_inter.mpr ⟨hp,(output_singleton S C o out j p).1 on⟩
  have := (Finset.card_le_card sub).trans (hcross i j hne)
  omega

end PEqualNP.Outside.L_meta_997_refund

namespace PEqualNP.Outside.L_meta_997_aux

lemma two_window_credit_count {m s k credit : ℕ}
    (size : Fin m → ℕ) (heavy : Fin m → Prop) [DecidablePred heavy]
    (cold : Finset (Fin s))
    (hz : (∑ i : Fin m, if heavy i then 0 else min k (size i) - 2) ≤ credit)
    (hc : (∑ i : Fin m, if heavy i then size i - 1 else 0) ≤ cold.card)
    (hh : (Finset.univ.filter (fun i => ¬heavy i ∧ 2 ≤ size i)).card ≤
      (Finset.univ \ cold).card) :
    (∑ i : Fin m, if heavy i then size i else min k (size i)) ≤ s + credit + m := by
  classical
  let mark (i : Fin m) : ℕ := if ¬heavy i ∧ 2 ≤ size i then 1 else 0
  have hmark : (∑ i : Fin m, mark i) = (Finset.univ.filter (fun i => ¬heavy i ∧ 2 ≤ size i)).card := by
    simp only [mark, ← Finset.sum_filter]
    simp
  let extra (i : Fin m) : ℕ := if heavy i then 0 else min k (size i) - 2
  have hp (i : Fin m) :
      (if heavy i then size i else min k (size i)) ≤
      (if heavy i then size i - 1 else 0) + mark i + extra i + 1 := by
    by_cases hi : heavy i
    · simp [hi, mark, extra]; omega
    · by_cases hs : 2 ≤ size i
      · simp [hi, hs, mark, extra]; omega
      · simp [hi, hs, mark, extra]; omega
  calc
    _ ≤ ∑ i : Fin m, ((if heavy i then size i - 1 else 0) + mark i + extra i + 1) :=
      Finset.sum_le_sum fun i _ => hp i
    _ = (∑ i : Fin m, if heavy i then size i - 1 else 0) +
        (Finset.univ.filter (fun i => ¬heavy i ∧ 2 ≤ size i)).card + (∑ i : Fin m, extra i) + m := by
          simp [Finset.sum_add_distrib, hmark]
    _ ≤ s + credit + m := by
      change (∑ i : Fin m, extra i) ≤ credit at hz
      have hpart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ cold)
      simp only [Finset.card_univ, Fintype.card_fin] at hpart
      omega

end PEqualNP.Outside.L_meta_997_aux

namespace PEqualNP.Outside.L_meta_997_aux

open PEqualNP.CircuitLowerBounds

lemma touching_outputs_hot {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (o : Fin m → ℕ) (y : Finset (Fin n)) (cold : Finset (Fin C.gates.length))
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false =
      decide (∃ p ∈ S i, x p = true))
    (valid : ∀ i, 2 ≤ (S i).card → n ≤ o i ∧ o i < n + C.gates.length)
    (distinct : ∀ i j, i ≠ j → 2 ≤ (S i).card → 2 ≤ (S j).card → o i ≠ o j)
    (isCold : ∀ g ∈ cold, (C.wires (List.ofFn (fun p => decide (p ∈ y)))).getD (n + g.val) false = false) :
    (Finset.univ.filter (fun i => ¬Disjoint (S i) y ∧ 2 ≤ (S i).card)).card ≤
       (Finset.univ \ cold).card := by
  classical
  let A := Finset.univ.filter (fun i => ¬Disjoint (S i) y ∧ 2 ≤ (S i).card)
  have ha (i : A) : ¬Disjoint (S i.val) y ∧ 2 ≤ (S i.val).card := (Finset.mem_filter.mp i.property).2
  let f (i : A) : Fin C.gates.length :=
    ⟨o i.val - n, by have h := valid i.val (ha i).2; omega⟩
  have wire (i : A) : n + (f i).val = o i.val := by
    have h := (valid i.val (ha i).2).1
    dsimp [f]
    omega
  have hot (i : A) : f i ∉ cold := by
    intro hc
    have hf := isCold (f i) hc
    rw [wire i, hout] at hf
    obtain ⟨p, hpS, hpy⟩ := Finset.not_disjoint_iff.mp (ha i).1
    exact (of_decide_eq_false hf) ⟨p, hpS, decide_eq_true hpy⟩
  have inj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra h
    exact distinct i.val j.val h (ha i).2 (ha j).2 ((wire i).symm.trans ((congrArg (fun g : Fin C.gates.length => n + g.val) hij).trans (wire j)))
  have hcount := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset A))
    (t := Finset.univ \ cold) f
    (fun i _ => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hot i⟩) inj.injOn
  simpa [A] using hcount

end PEqualNP.Outside.L_meta_997_aux
namespace PEqualNP.Outside.L_meta_997_aux
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997_refund PEqualNP.Outside.L_meta_997.Light

lemma two_window_with_credits {n m : ℕ} (C : Circuit) (y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hy : (C.wires (List.ofFn (fun p => decide (p ∈ y)))).getD (n+t) false = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true))
    (hroom : (∑ i : Fin m, if Disjoint (S i) y then 0 else min y.card (S i).card - 2) ≤ (refunds S C y).card) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  obtain ⟨cold, hgate, hcount⟩ := Heavy.heavy_charge_set C y t S o hg hu hy hlin ho
  apply two_window_credit_count (fun i => (S i).card) (fun i => Disjoint (S i) y) cold hroom
  · simpa only [Finset.sum_filter] using hcount
  · apply touching_outputs_hot C S o y cold ho
    · exact output_gate_of_card_two S C o ho
    · exact fun i j hij hi _ => output_ne_of_nontrivial S C o ho hlin i j hi hij
    · exact hgate

lemma two_window_of_card_le_two {n m : ℕ} (C : Circuit) (y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hy : (C.wires (List.ofFn (fun p => decide (p ∈ y)))).getD (n+t) false = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true))
    (hsmall : y.card ≤ 2) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  apply two_window_with_credits C y t S o hg hu hy hlin ho
  have hzero (i : Fin m) : min y.card (S i).card - 2 = 0 := by omega
  simp [hzero]

end PEqualNP.Outside.L_meta_997_aux

namespace PEqualNP.Outside.L_meta_997.Small

lemma card_disjoint_cap {n : ℕ} (Y A : Finset (Fin n)) (h : Disjoint A Y) :
    A.card + Y.card ≤ n := by
  rw [← Finset.card_union_of_disjoint h]
  simpa using Finset.card_le_univ (A ∪ Y)

lemma line_union {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (I : Finset (Fin m)) :
    (∑ i ∈ I, (S i).card) ≤ (I.biUnion S).card + I.card.choose 2 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hb' := Finset.card_biUnion_le_card_mul I (fun j => S i ∩ S j) 1
      (fun j hj => hlin i j (fun h => hi (h ▸ hj)))
    have hb : (S i ∩ I.biUnion S).card ≤ I.card := by
      simpa only [Finset.inter_biUnion, mul_one] using hb'
    have hc := Finset.card_union_add_card_inter (S i) (I.biUnion S)
    rw [Finset.sum_insert hi, Finset.biUnion_insert, Finset.card_insert_of_notMem hi,
      Nat.choose_succ_succ, Nat.choose_one_right]
    change (S i).card + (∑ j ∈ I, (S j).card) ≤ (S i ∪ I.biUnion S).card + (I.card + I.card.choose 2)
    omega

lemma price_cap {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (I : Finset (Fin m))
    (hd : ∀ i ∈ I, Disjoint (S i) Y) :
    Y.card + (∑ i ∈ I, (S i).card) ≤ n + I.card.choose 2 := by
  classical
  have hdu : Disjoint (I.biUnion S) Y := by
    apply Finset.disjoint_left.mpr
    intro p hp hpY
    obtain ⟨i,hi,hp'⟩ := Finset.mem_biUnion.mp hp
    exact Finset.disjoint_left.mp (hd i hi) hp' hpY
  have h := card_disjoint_cap Y (I.biUnion S) hdu
  have h' := line_union S hlin I
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Light

/-- Bound the number of covered labels by the number of starting wires plus
the charged binary branches. All other nontrivial wires pass their covered
labels to at most one predecessor. -/
lemma branching_cover {α : Type*} [DecidableEq α] (labels : ℕ → Finset α) (cost : Finset ℕ)
    (step : ∀ w, 2 ≤ (labels w).card → ∃ P : Finset ℕ, (∀ r ∈ P, r < w) ∧
      P.card ≤ (if w ∈ cost then 2 else 1) ∧ labels w ⊆ P.biUnion labels)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, 2 ≤ (labels w).card → w < t) :
    (F.biUnion labels).card ≤ F.card + (cost.filter (· < t)).card := by
  classical
  induction t generalizing F with
  | zero =>
    have hl (w) (hw : w ∈ F) : (labels w).card ≤ 1 := by
      by_contra! h
      exact Nat.not_lt_zero _ (hF w hw h)
    have hc := Finset.card_biUnion_le_card_mul F labels 1 hl
    simp only [Nat.mul_one] at hc
    omega
  | succ t ih =>
    by_cases expand : t ∈ F ∧ 2 ≤ (labels t).card
    · obtain ⟨P,hbelow,hcard,hcover⟩ := step t expand.2
      let F' := F.erase t ∪ P
      have hF' (w) (hw : w ∈ F') (hwbig : 2 ≤ (labels w).card) : w < t := by
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨hne,hmem⟩ := Finset.mem_erase.mp h
          have hh := hF w hmem hwbig
          omega
        · exact hbelow w h
      have hsub : F.biUnion labels ⊆ F'.biUnion labels := by
        intro a ha
        obtain ⟨w,hw,ha⟩ := Finset.mem_biUnion.mp ha
        by_cases heq : w = t
        · subst w
          obtain ⟨r,hr,har⟩ := Finset.mem_biUnion.mp (hcover ha)
          exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_union_right _ hr,har⟩
        · exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨heq,hw⟩),ha⟩
      have hc := Finset.card_le_card hsub
      have hi := ih F' hF'
      have hfsize : F'.card ≤ (F.erase t).card+P.card := Finset.card_union_le _ _
      have herase := Finset.card_erase_add_one expand.1
      by_cases htc : t ∈ cost
      · have heq : cost.filter (· < t+1) = insert t (cost.filter (· < t)) := by
          ext w
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hmem,hl⟩
            by_cases he : w=t
            · exact Or.inl he
            · exact Or.inr ⟨hmem,by omega⟩
          · rintro (rfl | ⟨hmem,hl⟩)
            · exact ⟨htc,by omega⟩
            · exact ⟨hmem,by omega⟩
        rw [heq,Finset.card_insert_of_notMem (by simp)]
        simp only [ite_eq_left htc] at hcard
        omega
      · simp only [ite_eq_right htc] at hcard
        have hmono := Finset.card_le_card (show cost.filter (· < t) ⊆ cost.filter (· < t+1) from
          fun w hw => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2.trans (by omega)⟩)
        omega
    · have ht (w) (hw : w ∈ F) (hb : 2 ≤ (labels w).card) : w < t := by
        have hne : w ≠ t := fun h => expand ⟨h ▸ hw,h ▸ hb⟩
        have hlt := hF w hw hb
        omega
      have hh := ih F ht
      have hmono := Finset.card_le_card (show cost.filter (· < t) ⊆ cost.filter (· < t+1) from
        fun w hw => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2.trans (by omega)⟩)
      omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

def unionWire {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w ∧ value C (fun _ : Fin n => false) r = false) ∧
    support (n:=n) C w = P.biUnion (support (n:=n) C)

lemma union_or_unary {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ)
    (hz : value C (fun _ : Fin n => false) w = false) (hs : 2 ≤ (support (n:=n) C w).card) :
    unionWire (n:=n) C w ∨ ∃ r, r < w ∧ value C (fun _ : Fin n => false) r = false ∧
      support (n:=n) C w ⊆ support C r := by
  classical
  obtain ⟨hn,hw⟩ := support_gate C w hs
  have hidx : w-n < C.gates.length := by change w<n+C.gates.length at hw; omega
  let g := C.gates[w-n]
  have hgs : g ∈ C.gates := List.getElem_mem _
  obtain ⟨hop,hlen⟩ := hg g hgs
  let read := fun (x : Fin n → Bool) (r : ℕ) => if r < w then value C x r else false
  have eqv (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w hn hw
  rcases hop with ha | ho
  · right
    have hall (x : Fin n → Bool) : value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
      rw [eqv x,ha]
      simp [GateOp.eval]
    have hneg : ¬ ∀ r ∈ g.inputs, read (fun _ => false) r = true := by
      intro h
      exact Bool.noConfusion (hz.symm.trans ((hall _).mpr h))
    push Not at hneg
    obtain ⟨r,hr,hrf⟩ := hneg
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (support (n:=n) C w).card by omega)
    have hyes := (hall _).mp ((mem_support C w p).mp hp) r hr
    have hrw : r < w := by
      by_contra h
      simp [read,h] at hyes
    refine ⟨r,hrw,?_,?_⟩
    · simpa [read,hrw] using hrf
    · intro a ha
      apply (mem_support C r a).mpr
      simpa [read,hrw] using ((hall _).mp ((mem_support C w a).mp ha) r hr)
  · left
    have hany (x : Fin n → Bool) : value C x w = true ↔ ∃ r ∈ g.inputs, read x r = true := by
      rw [eqv x,ho]
      simp [GateOp.eval]
    let P := g.inputs.toFinset.filter (· < w)
    refine ⟨P,(Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen),?_,?_⟩
    · intro r hr
      obtain ⟨hrg,hrw⟩ := Finset.mem_filter.mp hr
      refine ⟨hrw,?_⟩
      cases he : value C (fun _ : Fin n => false) r with
      | false => rfl
      | true =>
        have h := (hany _).mpr ⟨r,List.mem_toFinset.mp hrg,by simpa [read,hrw] using he⟩
        exact Bool.noConfusion (hz.symm.trans h)
    · ext p
      rw [mem_support,Finset.mem_biUnion,hany]
      constructor
      · rintro ⟨r,hr,hx⟩
        have hrw : r < w := by by_contra h; simp [read,h] at hx
        exact ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hrw⟩,
          (mem_support C r p).mpr (by simpa [read,hrw] using hx)⟩
      · rintro ⟨r,hr,hp⟩
        obtain ⟨hrg,hrw⟩ := Finset.mem_filter.mp hr
        exact ⟨r,List.mem_toFinset.mp hrg,by simpa [read,hrw] using (mem_support C r p).mp hp⟩

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

noncomputable def traceCost {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (clean : Bool) : Finset ℕ := by
  classical
  exact (dormant C T).filter fun w => unionWire (n:=n) C w ∧ (clean = true → support C w ⊆ T)

lemma trace_count {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ) (hg : good C)
    (hz : value C (fun _ : Fin n => false) o = false) (hsup : support C o = T)
    (clean : Bool) (hall : clean = true → ∀ w ∈ dormant C T, unionWire (n:=n) C w) :
    T.card ≤ (traceCost C T clean).card + 1 := by
  classical
  let Q (w : ℕ) := value C (fun _ : Fin n => false) w = false ∧ (clean = true → support C w ⊆ T)
  let L := fun w => if Q w then support C w ∩ T else ∅
  have goodL {w : ℕ} (hbig : 2 ≤ (L w).card) : Q w ∧ 2 ≤ (support C w ∩ T).card := by
    by_cases hq : Q w
    · exact ⟨hq,by simpa [L,hq] using hbig⟩
    · simp [L,hq] at hbig
  have biggate {w : ℕ} (hbig : 2 ≤ (L w).card) : w ∈ dormant C T := by
    obtain ⟨hq,htrace⟩ := goodL hbig
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (htrace.trans
      (Finset.card_le_card Finset.inter_subset_left))),hq.1,htrace⟩
  have hstep (w : ℕ) (hbig : 2 ≤ (L w).card) : ∃ P : Finset ℕ, (∀ r ∈ P, r < w) ∧
      P.card ≤ (if w ∈ traceCost C T clean then 2 else 1) ∧ L w ⊆ P.biUnion L := by
    have hmem := biggate hbig
    obtain ⟨hq,htrace⟩ := goodL hbig
    have hl : L w = support C w ∩ T := by simp [L,hq]
    by_cases hu : unionWire (n:=n) C w
    · have hc : w ∈ traceCost C T clean := Finset.mem_filter.mpr ⟨hmem,hu,hq.2⟩
      obtain ⟨P,hpc,hdata,heq⟩ := hu
      refine ⟨P,fun r hr => (hdata r hr).1,by simpa [hc] using hpc,?_⟩
      intro a ha
      obtain ⟨has,hat⟩ := Finset.mem_inter.mp (hl ▸ ha)
      obtain ⟨r,hr,har⟩ := Finset.mem_biUnion.mp (heq ▸ has)
      have hqr : Q r := by
        refine ⟨(hdata r hr).2,fun hcl p hp => hq.2 hcl ?_⟩
        rw [heq]
        exact Finset.mem_biUnion.mpr ⟨r,hr,hp⟩
      exact Finset.mem_biUnion.mpr ⟨r,hr,by simpa [L,hqr] using Finset.mem_inter.mpr ⟨har,hat⟩⟩
    · obtain ⟨r,hr,hrz,hsub⟩ := (union_or_unary C hg w hq.1
        (htrace.trans (Finset.card_le_card Finset.inter_subset_left))).resolve_left hu
      have hnc : clean ≠ true := fun hcl => hu (hall hcl w hmem)
      have hqr : Q r := ⟨hrz,fun hc => (hnc hc).elim⟩
      refine ⟨{r},by simpa using hr,?_,?_⟩
      · simp only [Finset.card_singleton]; split <;> decide
      · simp only [Finset.singleton_biUnion]
        rw [hl]
        intro a ha
        simpa [L,hqr] using Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
  have hcut := branching_cover L (traceCost C T clean) hstep (n+C.size) {o} (by
    intro w _ hb
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp (biggate hb)).1).2)
  have hqo : Q o := ⟨hz,fun _ => hsup.le⟩
  have hlo : L o = T := by simp [L,hqo,hsup]
  simp only [Finset.singleton_biUnion,hlo,Finset.card_singleton] at hcut
  have hmono := Finset.card_filter_le (traceCost C T clean) (· < n+C.size)
  omega

/-- Either the pure gates pay the entire row privately, or its dormant
projection contains at least one extra gate. -/
lemma private_or_extra {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hg : good C) (hz : value C (fun _ : Fin n => false) o = false) (hsup : support C o = T) :
    T.card ≤ (assigned C T).card + 1 ∨ T.card ≤ (dormant C T).card := by
  classical
  by_cases hall : ∀ w ∈ dormant C T, unionWire (n:=n) C w
  · left
    have hc := trace_count C T o hg hz hsup true (fun _ => hall)
    have hsub : traceCost C T true ⊆ assigned C T := by
      intro w hw
      obtain ⟨hw,_,hclean⟩ := Finset.mem_filter.mp hw
      obtain ⟨hr,_,hcard⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hr,hclean rfl,hcard.trans (Finset.card_le_card Finset.inter_subset_left)⟩
    exact hc.trans (Nat.add_le_add_right (Finset.card_le_card hsub) _)
  · right
    push Not at hall
    obtain ⟨r,hr,hn⟩ := hall
    have hne : r ∉ traceCost C T false := fun hh => hn (Finset.mem_filter.mp hh).2.1
    have hsub : traceCost C T false ⊆ (dormant C T).erase r := by
      intro w hw
      exact Finset.mem_erase.mpr ⟨fun he => hne (he ▸ hw),(Finset.mem_filter.mp hw).1⟩
    have hc := trace_count C T o hg hz hsup false (by simp)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_erase_add_one hr
    omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma low_private_or_extra {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true) : T.card ≤ (assigned C T).card+1 ∨ T.card ≤ (dormant C T).card := by
  classical
  cases C with
  | mk gates o' =>
    let C : Circuit := ⟨gates,o'⟩
    have hvalid : t < gates.length := by
      by_contra! h
      have hf := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gates.length ≤ n+t; omega)
      have ht := hlight (fun _ : Fin n => false) (by simpa using (show 0 < k by omega))
      exact Bool.noConfusion (hf.symm.trans ht)
    let j : Fin gates.length := ⟨t,hvalid⟩
    let D := frozen true gates t
    have hd : good D := fixed_gates true gates j hg fun i hi => Fin.ext (hu i hi)
    have eq_light (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p = true)).card < k)
        (w : ℕ) : value D x w = value C x w := fixed_eq true gates j o' x (hlight x hx) w
    have es (p : Fin n) (w : ℕ) : value D (fun r => decide (r=p)) w = value C (fun r => decide (r=p)) w := by
      apply eq_light
      have hf : Finset.univ.filter (fun r : Fin n => decide (r=p) = true) = {p} := by ext a; simp
      rw [hf,Finset.card_singleton]
      omega
    have sp (w : ℕ) : support (n:=n) D w = support C w := by
      ext p
      rw [mem_support, mem_support, es]
    have hsame : dormant D T = dormant C T := by
      ext w
      have ez := eq_light (fun _ => false) (by simpa using (show 0 < k by omega)) w
      simp only [dormant,Finset.mem_filter,sp,ez]
      rw [show D.size = C.size from fixed_size true gates t]
    have hassigned : assigned D T = assigned C T := by
      ext w
      simp only [assigned,Finset.mem_filter,sp]
      rw [show D.size = C.size from fixed_size true gates t]
    have hz : value D (fun _ : Fin n => false) o = false := by
      rw [eq_light _ (by simpa using (show 0 < k by omega)),hout]
      simp
    have hsupport : support D o = T := by
      ext p
      rw [mem_support,es,hout]
      simp
    simpa only [hsame,hassigned] using private_or_extra D T o hd hz hsupport

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem sum_row_weights {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (C : Circuit) (f : Fin m → ℕ)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hweight : ∀ i ∈ I, f i ≤ (assigned C (S i)).card + 1) : (∑ i ∈ I, f i) ≤ (I.biUnion (fun i => assigned C (S i))).card + I.card := by
  classical
  let G := fun i => assigned C (S i)
  have hd : (↑I : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr ?_
    intro w wi wj
    have ⟨hi,hs⟩ := (Finset.mem_filter.mp wi).2
    have hj := (Finset.mem_filter.mp wj).2.1
    have hsub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hi hp,hj hp⟩
    have := hs.trans ((Finset.card_le_card hsub).trans (hpair i j hij))
    omega
  have per := Finset.sum_le_sum (s:=I) (fun i hi => hweight i hi)
  change _ ≤ (I.biUnion G).card + I.card
  rw [Finset.card_biUnion hd]
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one, G] using per

lemma weighted_exceptional_count {n m k : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ k) (hD : 2 ≤ (S d).card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true)
    (q : ℕ) (hdweight : q ≤ (dormant C (S d)).card+1)
    (f : Fin m → ℕ)
    (hweight : ∀ i, i ≠ d → f i ≤ (assigned C (S i)).card+1)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false) :
    q + (∑ i ∈ Finset.univ.erase d, f i) + k ≤ C.gates.length + m := by
  classical
  let I := Finset.univ.erase d
  let U := I.biUnion (fun i => assigned C (S i))
  let G := dormant C (S d)
  have dis : Disjoint U G := by
    apply Finset.disjoint_left.mpr
    intro w hu hg'
    obtain ⟨i,hi,hwi⟩ := Finset.mem_biUnion.mp hu
    have ha := (Finset.mem_filter.mp hwi).2.1
    have hc := (Finset.mem_filter.mp hg').2.2
    have hs : support C w ∩ S d ⊆ S i ∩ S d := fun v hv =>
      Finset.mem_inter.mpr ⟨ha (Finset.mem_inter.mp hv).1,(Finset.mem_inter.mp hv).2⟩
    have hd := hpair i d (Finset.mem_erase.mp hi).1
    have hsmall := (Finset.card_le_card hs).trans hd
    omega
  let z := n+t
  have htz := hlight (fun _ => false) (by simpa using (show 0 < k by omega))
  have hzrange : z ∈ Finset.Ico n (n+C.size) := by
    apply Finset.mem_Ico.mpr ⟨Nat.le_add_right _ _,?_⟩
    by_contra! hn
    have hf := missing_value C (fun _ : Fin n => false) z hn
    exact Bool.noConfusion (hf.symm.trans htz)
  have hzs : ∀ p : Fin n, p ∈ support C z := by
    intro p
    apply (mem_support C z p).mpr
    apply hlight
    have h : Finset.univ.filter (fun v : Fin n => decide (v=p) = true) = {p} := by ext v; simp
    rw [h,Finset.card_singleton]
    omega
  have hnotin : z ∉ U ∪ G := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i,hi,hw⟩ := Finset.mem_biUnion.mp h
      have ha := (Finset.mem_filter.mp hw).2.1
      have ts : S d ⊆ S i ∩ S d := fun p hp => Finset.mem_inter.mpr ⟨ha (hzs p),hp⟩
      have small := (Finset.card_le_card ts).trans (hpair i d (Finset.mem_erase.mp hi).1)
      omega
    · have hz := (Finset.mem_filter.mp h).2.1
      exact Bool.noConfusion (hz.symm.trans htz)
  obtain ⟨A,hkA,hAi,hAs⟩ := guard_empty_gates C t y (by omega : 0 < k) hg hu hlight hy
  let W := insert z (U ∪ G)
  have disA : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro w wa ww
    rcases Finset.mem_insert.mp ww with hz | h
    · have hi := (Finset.mem_Ico.mp (hAi wa)).2
      change w < z at hi
      omega
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i,_,hw⟩ := Finset.mem_biUnion.mp h
        have hc := (Finset.mem_filter.mp hw).2.2
        rw [hAs w wa] at hc
        simp at hc
      · have hc := (Finset.mem_filter.mp h).2.2
        rw [hAs w wa] at hc
        simp at hc
  have hgate : A.card + (U.card + G.card + 1) ≤ C.gates.length := by
    calc
      _ = (A ∪ W).card := by
        rw [Finset.card_union_of_disjoint disA]
        simp only [W,Finset.card_insert_of_notMem hnotin,Finset.card_union_of_disjoint dis]
      _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card (by
        intro w hw
        rcases Finset.mem_union.mp hw with ha | hw
        · obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp (hAi ha)
          exact Finset.mem_Ico.mpr ⟨lo,hi.trans (Finset.mem_Ico.mp hzrange).2⟩
        · rcases Finset.mem_insert.mp hw with h | hw
          · exact h ▸ hzrange
          · rcases Finset.mem_union.mp hw with hw | hw
            · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
              exact (Finset.mem_filter.mp hi).1
            · exact (Finset.mem_filter.mp hw).1)
      _ = C.gates.length := by simp [Circuit.size]
  have hcard := Finset.card_erase_add_one (Finset.mem_univ d)
  change I.card + 1 = _ at hcard
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  have hgeneral := sum_row_weights S I C f hpair (fun i hi => hweight i (Finset.mem_erase.mp hi).1)
  change (∑ i ∈ I, f i) ≤ U.card + I.card at hgeneral
  change q ≤ G.card + 1 at hdweight
  change q + (∑ i ∈ I, f i) + k ≤ _
  omega


end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma window_bound_bonus {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card) (hD : 2 ≤ (S d).card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (e : Fin m) (hed : e ≠ d) (hes : y.card < (S e).card)
    (he : (∑ i, if Disjoint (S i) y then (S i).card-y.card else 0) ≤
      ((S d).card-y.card) + (refunds S C y).card + y.card + 1) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  let f := fun i : Fin m => min y.card (S i).card
  let ex := fun i : Fin m => if Disjoint (S i) y then (S i).card-y.card else 0
  have per (i : Fin m) : (if Disjoint (S i) y then (S i).card else min y.card (S i).card) =
      f i + ex i := by
    by_cases h : Disjoint (S i) y
    · simp [f,ex,h]; omega
    · simp [f,ex,h]
  have hsum := Finset.sum_congr (s₁:=(Finset.univ : Finset (Fin m))) rfl (fun i _ => per i)
  rw [Finset.sum_add_distrib] at hsum
  change (∑ i, ex i) ≤ _ at he
  have hf (i : Fin m) : f i ≤ (assigned C (S i)).card+1 :=
    card_light (S i) C (o i) t hg hu (hout i) hlight
  have hfd : (S d).card = f d + ((S d).card-y.card) := by dsimp [f]; omega
  rcases low_private_or_extra C (S d) (o d) t hk hg hu (hout d) hlight with hstrong | hweak
  · let g := fun i : Fin m => f i + if i = d then ((S d).card-y.card) else 0
    have hg' (i) : g i ≤ (assigned C (S i)).card + 1 := by
      by_cases h : i = d
      · subst i; simpa [g,←hfd] using hstrong
      · simpa [g,h] using hf i
    have hq := low_dormant_count C (S e) (o e) t hk hg hu (hout e) hlight
    have hall := weighted_exceptional_count S e C t y hk (by omega) hpair hg hu hlight
      (S e).card hq g (fun i _ => hg' i) hy
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) f (Finset.mem_univ e)
    have hde : d ∈ (Finset.univ : Finset (Fin m)).erase e := Finset.mem_erase.mpr ⟨hed.symm,Finset.mem_univ _⟩
    have hval : (∑ i ∈ Finset.univ.erase e, g i) =
        (∑ i ∈ Finset.univ.erase e, f i) + ((S d).card-y.card) := by simp [g,Finset.sum_add_distrib,hde]
    rw [hval] at hall
    have hfe : f e = y.card := Nat.min_eq_left (by omega)
    omega
  · have hall := weighted_exceptional_count S d C t y hk hD hpair hg hu hlight
      ((S d).card+1) (by omega) f (fun i _ => hf i) hy
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) f (Finset.mem_univ d)
    omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Small

/-- Counting row pairs at each input bounds the total incidence in a linear family. -/
lemma pair_incidence {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (V : Finset (Fin n)) (hsub : ∀ i ∈ I, S i ⊆ V)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    2 * (∑ i ∈ I, (S i).card) ≤ 3 * V.card + I.card.choose 2 := by
  classical
  let N (p : Fin n) := I.filter fun i => p ∈ S i
  let P (p : Fin n) := (N p).powersetCard 2
  have hdis : (↑V : Set (Fin n)).PairwiseDisjoint P := by
    intro p _ q _ hpq
    refine Finset.disjoint_left.mpr ?_
    intro J jp jq
    obtain ⟨hjp,hcard⟩ := Finset.mem_powersetCard.mp jp
    obtain ⟨hjq,_⟩ := Finset.mem_powersetCard.mp jq
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (show 1 < J.card by omega)
    have contains (s) (hs : J ⊆ N s) : s ∈ S i ∩ S j :=
      Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp (hs hi)).2,(Finset.mem_filter.mp (hs hj)).2⟩
    have hmany := Finset.one_lt_card.mpr ⟨p,contains p hjp,q,contains q hjq,hpq⟩
    have hle := hlin i j hij
    omega
  have hbudget : (∑ p ∈ V, (N p).card.choose 2) ≤ I.card.choose 2 := by
    calc
      _ = (V.biUnion P).card := by
        rw [Finset.card_biUnion hdis]
        simp [P]
      _ ≤ (I.powersetCard 2).card := Finset.card_le_card (by
        intro J hJ
        obtain ⟨p,_, hp⟩ := Finset.mem_biUnion.mp hJ
        exact Finset.powersetCard_mono (Finset.filter_subset _ _) hp)
      _ = _ := Finset.card_powersetCard 2 I
  have incid : (∑ p ∈ V, (N p).card) = ∑ i ∈ I, (S i).card := by
    calc
      _ = ∑ p ∈ V, ∑ i ∈ I, (if p ∈ S i then 1 else 0) := by
        simp [N,Finset.sum_boole]
      _ = ∑ i ∈ I, ∑ p ∈ V, (if p ∈ S i then 1 else 0) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.inter_eq_right.mpr (hsub i hi)]
  have per (d : ℕ) : 2*d ≤ 3 + d.choose 2 := by
    induction d with
    | zero => decide
    | succ d ih =>
      rw [Nat.choose_succ_succ d 1,Nat.choose_one_right]
      cases d with
      | zero => decide
      | succ d =>
        cases d with
        | zero => decide
        | succ d => change 2*((d+1+1)+1) ≤ 3+((d+1+1) + (d+1+1).choose 2); omega
  have hsum := Finset.sum_le_sum (s:=V) (fun p _ => per (N p).card)
  rw [← Finset.mul_sum,incid,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hsum
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small

lemma geometry_bonus {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (hk : 3 ≤ Y.card) (hn : n ≤ 4*Y.card+7)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∀ i, Disjoint (S i) Y → (S i).card ≤ Y.card+1) ∨
    ∃ d, 2 ≤ (S d).card ∧ (∑ i, if Disjoint (S i) Y then (S i).card-Y.card else 0) ≤
      ((S d).card-Y.card) + (Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)).card + Y.card + 1 := by
  classical
  let k := Y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ k+2 ≤ (S i).card)
  let D := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)
  by_cases hne : B.Nonempty
  swap
  · refine Or.inl ?_
    intro i hi
    by_contra! hs
    exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,by dsimp [k]; omega⟩⟩
  obtain ⟨d,hd,hm⟩ := B.exists_max_image (fun i => (S i).card) hne
  have binfo {i} (hi : i ∈ B) : Disjoint (S i) Y ∧ k+2 ≤ (S i).card := (Finset.mem_filter.mp hi).2
  have hds := (binfo hd).2
  have hkk : 3 ≤ k := hk
  have h6 : B.card ≤ 6 := by
    by_contra! hlarge
    obtain ⟨I,hI,h7⟩ := Finset.exists_subset_card_eq (s:=B) (n:=7) (by omega)
    let V := Finset.univ \ Y
    have hin (i) (hi : i ∈ I) : S i ⊆ V := by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp (binfo (hI hi)).1 hp⟩
    have hinc := pair_incidence S I V hin hlin
    have hcard : V.card = n-k := by
      simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ Y),k]
    have hkN : k ≤ n := by simpa [k] using Finset.card_le_univ Y
    rw [hcard,h7] at hinc
    norm_num [Nat.choose] at hinc
    have hsum := Finset.sum_le_sum (s:=I) (fun i hi => (binfo (hI hi)).2)
    simp only [Finset.sum_const,h7,smul_eq_mul] at hsum
    change n ≤ 4*k+7 at hn
    omega
  have hp := price_cap S Y hlin B (fun i hi => (binfo hi).1)
  change k + _ ≤ _ at hp
  have hM := Finset.sum_le_sum (s:=B) (fun i hi => hm i hi)
  simp only [Finset.sum_const,smul_eq_mul] at hM
  have hpos : 0 < B.card := Finset.card_pos.mpr hne
  have key : (∑ i ∈ B, (S i).card) ≤ B.card * (k+1) + (S d).card + 1 := by
    generalize hr : B.card = r at *
    interval_cases r <;> norm_num [Nat.choose] at * <;> omega
  let b (i : Fin m) := (S i).card - (k+1)
  have splitB (i : Fin m) (hi : i ∈ B) : (S i).card = (k+1) + b i := by
    have h := (binfo hi).2
    dsimp [b]
    omega
  have heq := Finset.sum_congr (s₂:=B) rfl splitB
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at heq
  have hbudget : (∑ i ∈ B, b i) ≤ (S d).card + 1 := by omega
  have hper (i : Fin m) : (if Disjoint (S i) Y then (S i).card-k else 0) ≤
      (if i ∈ D then 1 else 0) + (if i ∈ B then b i else 0) := by
    by_cases hdY : Disjoint (S i) Y
    · by_cases hib : i ∈ B
      · have hs := (binfo hib).2
        have hid : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdY,by omega⟩
        simp [hdY, hib, hid, b]
        omega
      · have hs : (S i).card ≤ k+1 := by
          by_contra! h
          exact hib (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdY,by omega⟩)
        by_cases his : 2 ≤ (S i).card
        · have hid : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdY,his⟩
          simp [hdY, hib, hid]
          omega
        · simp [hdY, hib]
          omega
    · simp [hdY]
  have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hper i)
  rw [Finset.sum_add_distrib, Fintype.sum_ite_mem, Fintype.sum_ite_mem] at he
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at he
  refine Or.inr ⟨d,by omega,?_⟩
  change (∑ i, if Disjoint (S i) Y then (S i).card-k else 0) ≤ ((S d).card-k)+D.card+k+1
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997.Light

theorem size_window_bonus : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card ≤ 2 ∨ n ≤ 4*y.card+7) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by

  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy
  by_cases hk : y.card ≤ 2
  · exact PEqualNP.Outside.L_meta_997_aux.two_window_of_card_le_two C y t S o hg hu hy hlin ho hk
  rcases geometry_bonus S y (by omega) (hn.resolve_left hk) hlin with hr | ⟨d,hds,hb⟩
  · exact window_bound_one_extra S C o t y hlin hg hu ho hlight hr
  · let D := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
    have href := disjoint_outputs_refunded S C o y D hlin ho (fun i hi => (Finset.mem_filter.mp hi).2)
    by_cases he : ∃ e, e ≠ d ∧ Disjoint (S e) y ∧ y.card < (S e).card
    · obtain ⟨e,hed,_,hes⟩ := he
      apply window_bound_bonus S d C o t y (by omega) hds hlin hg hu ho hlight hy e hed hes
      change (∑ i, if Disjoint (S i) y then (S i).card - y.card else 0) ≤
        ((S d).card-y.card) + D.card + y.card + 1 at hb
      omega
    · apply window_bound_reserve S d C o t y (by omega) hds hlin hg hu ho hlight hy
      rw [Finset.sum_eq_single d]
      · split <;> omega
      · intro i _ hid
        by_cases hi : Disjoint (S i) y
        · have hs : (S i).card ≤ y.card := Nat.le_of_not_gt (fun h => he ⟨i,hid,hi,h⟩)
          simp [hi,Nat.sub_eq_zero_of_le hs]
        · simp [hi]
      · simp

theorem num_inputs_nineteen : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 19 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  intro n m S C o t y hn
  apply size_window_bonus n m S C o t y
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Light

/-- A fixed graph cut has a subordinate true-certificate cut for every
positive input. Unary certificate steps only grow the former cut. -/
lemma dual_cut {X : Type*} (v : X → ℕ → Prop) (G A : Finset ℕ) (_hAG : A ⊆ G)
    (step : ∀ w ∈ G, ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ x, v x w → ∃ Q : Finset ℕ, Q ⊆ P ∧ Q.card ≤ (if w ∈ A then 2 else 1) ∧
        (∀ r ∈ Q, v x r) ∧ ∀ y, (∀ r ∈ Q, v y r) → v y w)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x, ∀ E ⊆ F, (∀ w ∈ E, v x w) →
        ∃ R : Finset ℕ, R ⊆ B ∧ R.card ≤ E.card + (A.filter (· < t)).card ∧
          (∀ w ∈ R, v x w) ∧ ∀ y, (∀ r ∈ R, v y r) → ∀ w ∈ E, v y w := by
  classical
  have next (K : Finset ℕ) (t : ℕ) (hm : t ∈ K) :
      (K.filter (· < t+1)).card = (K.filter (· < t)).card+1 := by
    have heq : K.filter (· < t+1) = insert t (K.filter (· < t)) := by
      ext w
      simp only [Finset.mem_filter,Finset.mem_insert]
      constructor
      · rintro ⟨hw,hl⟩
        by_cases he : w=t
        · exact Or.inl he
        · exact Or.inr ⟨hw,by omega⟩
      · rintro (rfl | ⟨hw,hl⟩)
        · exact ⟨hm,by omega⟩
        · exact ⟨hw,by omega⟩
    rw [heq,Finset.card_insert_of_notMem (by simp)]
  have mono (K : Finset ℕ) (t : ℕ) : (K.filter (· < t)).card ≤ (K.filter (· < t+1)).card :=
    Finset.card_le_card fun w hw => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
      (Finset.mem_filter.mp hw).2.trans (by omega)⟩
  induction t generalizing F with
  | zero =>
    exact ⟨F,Finset.disjoint_left.mpr (fun w hw hm => Nat.not_lt_zero _ (hF w hw hm)),
      Nat.le_add_right ..,fun x E hE hx => ⟨E,hE,Nat.le_add_right ..,hx,fun _ h => h⟩⟩
  | succ t ih =>
    by_cases expand : t ∈ F ∧ t ∈ G
    · obtain ⟨P,hpc,hlo,hsel⟩ := step t expand.2
      let F' := F.erase t ∪ P
      have hF' (w) (hw : w ∈ F') (hg : w ∈ G) : w < t := by
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨hne,hw⟩ := Finset.mem_erase.mp h
          have h := hF w hw hg
          omega
        · exact hlo w h
      obtain ⟨B,hd,hb,subcut⟩ := ih F' hF'
      have hFc : F'.card ≤ (F.erase t).card + P.card := Finset.card_union_le _ _
      have hFe := Finset.card_erase_add_one expand.1
      refine ⟨B,hd,(by rw [next G t expand.2]; omega),?_⟩
      intro x E hE hpos
      by_cases htE : t ∈ E
      · obtain ⟨Q,hQP,hQcard,hQpos,hQsel⟩ := hsel x (hpos t htE)
        let E' := E.erase t ∪ Q
        have hE' : E' ⊆ F' := Finset.union_subset_union (Finset.erase_subset_erase t hE) hQP
        have hpos' (w) (hw : w ∈ E') : v x w := by
          rcases Finset.mem_union.mp hw with h | h
          · exact hpos w (Finset.mem_erase.mp h).2
          · exact hQpos w h
        obtain ⟨R,hR,hRc,hRx,hRy⟩ := subcut x E' hE' hpos'
        refine ⟨R,hR,?_,hRx,?_⟩
        · have hEc : E'.card ≤ (E.erase t).card + Q.card := Finset.card_union_le _ _
          have hEe := Finset.card_erase_add_one htE
          by_cases htA : t ∈ A
          · simp only [ite_eq_left htA] at hQcard
            rw [next A t htA]
            omega
          · simp only [ite_eq_right htA] at hQcard
            have h := mono A t
            omega
        · intro y hy w hw
          by_cases he : w = t
          · subst w
            exact hQsel y (fun r hr => hRy y hy r (Finset.mem_union_right _ hr))
          · exact hRy y hy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hw⟩))
      · have hEF : E ⊆ F' := by
          intro w hw
          exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => htE (h ▸ hw),hE hw⟩)
        obtain ⟨R,hR,hc,hx,hy⟩ := subcut x E hEF hpos
        refine ⟨R,hR,?_,hx,hy⟩
        have h := mono A t
        omega
    · have hFt (w) (hw : w ∈ F) (hg : w ∈ G) : w < t := by
        have hne : w ≠ t := fun h => expand ⟨h ▸ hw,h ▸ hg⟩
        have hh := hF w hw hg
        omega
      obtain ⟨B,hd,hc,hsub⟩ := ih F hFt
      refine ⟨B,hd,hc.trans (Nat.add_le_add_left (mono G t) _),?_⟩
      intro x E hE hx
      obtain ⟨R,hR,hr,hp,hy⟩ := hsub x E hE hx
      exact ⟨R,hR,hr.trans (Nat.add_le_add_left (mono A t) _),hp,hy⟩

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

abbrev andAt (C : Circuit) (n w : ℕ) : Prop :=
  (C.gates[w-n]?).map Gate.op = some .and

noncomputable instance (C : Circuit) (n w : ℕ) : Decidable (andAt C n w) := Classical.propDecidable _

lemma gate_operation_split {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ)
    (hz : value C (fun _ : Fin n => false) w = false) (hs : 2 ≤ (support (n:=n) C w).card) :
    (¬ andAt C n w ∧ unionWire (n:=n) C w) ∨ andAt C n w ∧ ∃ r, r < w ∧ value C (fun _ : Fin n => false) r = false ∧
      support (n:=n) C w ⊆ support C r := by
  classical
  obtain ⟨hn,hw⟩ := support_gate C w hs
  have hidx : w-n < C.gates.length := by change w<n+C.gates.length at hw; omega
  let g := C.gates[w-n]
  have hgs : g ∈ C.gates := List.getElem_mem _
  obtain ⟨hop,hlen⟩ := hg g hgs
  let read := fun (x : Fin n → Bool) (r : ℕ) => if r < w then value C x r else false
  have eqv (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w hn hw
  rcases hop with ha | ho
  · right
    refine ⟨?_,?_⟩
    · simpa [andAt,hidx,g] using ha
    have hall (x : Fin n → Bool) : value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
      rw [eqv x,ha]
      simp [GateOp.eval]
    have hneg : ¬ ∀ r ∈ g.inputs, read (fun _ => false) r = true := by
      intro h
      exact Bool.noConfusion (hz.symm.trans ((hall _).mpr h))
    push Not at hneg
    obtain ⟨r,hr,hrf⟩ := hneg
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (support (n:=n) C w).card by omega)
    have hyes := (hall _).mp ((mem_support C w p).mp hp) r hr
    have hrw : r < w := by
      by_contra h
      simp [read,h] at hyes
    refine ⟨r,hrw,?_,?_⟩
    · simpa [read,hrw] using hrf
    · intro a ha
      apply (mem_support C r a).mpr
      simpa [read,hrw] using ((hall _).mp ((mem_support C w a).mp ha) r hr)
  · left
    refine ⟨?_,?_⟩
    · simp [andAt,hidx,show C.gates[w-n].op = .or from ho]
    have hany (x : Fin n → Bool) : value C x w = true ↔ ∃ r ∈ g.inputs, read x r = true := by
      rw [eqv x,ho]
      simp [GateOp.eval]
    let P := g.inputs.toFinset.filter (· < w)
    refine ⟨P,(Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen),?_,?_⟩
    · intro r hr
      obtain ⟨hrg,hrw⟩ := Finset.mem_filter.mp hr
      refine ⟨hrw,?_⟩
      cases he : value C (fun _ : Fin n => false) r with
      | false => rfl
      | true =>
        have h := (hany _).mpr ⟨r,List.mem_toFinset.mp hrg,by simpa [read,hrw] using he⟩
        exact Bool.noConfusion (hz.symm.trans h)
    · ext p
      rw [mem_support,Finset.mem_biUnion,hany]
      constructor
      · rintro ⟨r,hr,hx⟩
        have hrw : r < w := by by_contra h; simp [read,h] at hx
        exact ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hrw⟩,
          (mem_support C r p).mpr (by simpa [read,hrw] using hx)⟩
      · rintro ⟨r,hr,hp⟩
        obtain ⟨hrg,hrw⟩ := Finset.mem_filter.mp hr
        exact ⟨r,List.mem_toFinset.mp hrg,by simpa [read,hrw] using (mem_support C r p).mp hp⟩

lemma certificate_inputs {n : ℕ} (C : Circuit) (hg : good C) (w : ℕ)
    (hn : n ≤ w) (hw : w < n+C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ x : Fin n → Bool, value C x w = true → ∃ Q : Finset ℕ, Q ⊆ P ∧
      Q.card ≤ (if andAt C n w then 2 else 1) ∧
      (∀ r ∈ Q, value C x r = true) ∧
      ∀ y : Fin n → Bool, (∀ r ∈ Q, value C y r = true) → value C y w = true := by
  classical
  have hidx : w-n < C.gates.length := by change w<n+C.gates.length at hw; omega
  let g := C.gates[w-n]
  have hgs : g ∈ C.gates := List.getElem_mem _
  obtain ⟨hop,hlen⟩ := hg g hgs
  let read := fun (x : Fin n → Bool) (r : ℕ) => if r < w then value C x r else false
  have eqv (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w hn hw
  let P := g.inputs.toFinset.filter (· < w)
  have hpc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen)
  refine ⟨P,hpc,fun w hw => (Finset.mem_filter.mp hw).2,?_⟩
  intro x hx
  rcases hop with ha | ho
  · have hall (x : Fin n → Bool) : value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
      rw [eqv x,ha]
      simp [GateOp.eval]
    have hA : andAt C n w := by simpa [andAt,hidx,g] using ha
    refine ⟨P,Finset.Subset.refl _,by rw [ite_eq_left hA]; exact hpc,?_,?_⟩
    · intro r hr
      obtain ⟨hm,hrw⟩ := Finset.mem_filter.mp hr
      simpa [read,hrw] using (hall x).mp hx r (List.mem_toFinset.mp hm)
    · intro y hy
      apply (hall y).mpr
      intro r hr
      have hrw : r < w := by
        by_contra h
        have hread := (hall x).mp hx r hr
        simp [read,h] at hread
      simpa [read,hrw] using hy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hrw⟩)
  · have hany (x : Fin n → Bool) : value C x w = true ↔ ∃ r ∈ g.inputs, read x r = true := by
      rw [eqv x,ho]
      simp [GateOp.eval]
    obtain ⟨r,hr,hrx⟩ := (hany x).mp hx
    have hrw : r < w := by by_contra h; simp [read,h] at hrx
    refine ⟨{r},Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hrw⟩),?_,?_,?_⟩
    · simp only [Finset.card_singleton]; split <;> decide
    · simpa [read,hrw] using hrx
    · intro y hy
      exact (hany y).mpr ⟨r,hr,by simpa [read,hrw] using hy r (Finset.mem_singleton_self _)⟩

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma many_private_ands {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hg : good C)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ T)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hunder : (assigned C T).card+1 < T.card) :
    k ≤ ((assigned C T).filter (andAt C n)).card+1 := by
  classical
  let G := assigned C T
  let A := G.filter (andAt C n)
  let v := fun (x : Fin n → Bool) (w : ℕ) => value C x w = true
  have gRange (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have hstep (w : ℕ) (hw : w ∈ G) : ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ x, v x w → ∃ Q : Finset ℕ, Q ⊆ P ∧ Q.card ≤ (if w ∈ A then 2 else 1) ∧
        (∀ r ∈ Q, v x r) ∧ ∀ y, (∀ r ∈ Q, v y r) → v y w := by
    have hm : w ∈ A ↔ andAt C n w := by simp [A,hw]
    simpa only [hm,v] using certificate_inputs C hg w (gRange _ hw).1 (gRange _ hw).2
  obtain ⟨B,hd,hBc,hcert⟩ := dual_cut v G A (Finset.filter_subset _ _) hstep (n+C.size) {o}
      (fun w _ hw => (gRange w hw).2)
  have hbound : B.card < T.card := by
    have h := Finset.card_filter_le G (· < n+C.size)
    simp only [Finset.card_singleton] at hBc
    change G.card+1 < _ at hunder
    omega
  let clean (w : ℕ) : Finset (Fin n) := if support C w ⊆ T then support C w else ∅
  have hclean (w) (hw : w ∈ B) : (clean w).card ≤ 1 := by
    by_cases hsub : support C w ⊆ T
    · rw [show clean w = support C w by simp [clean,hsub]]
      by_contra! h
      exact Finset.disjoint_left.mp hd hw (Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr (support_gate C w h),hsub,h⟩)
    · simp [clean,hsub]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p,hp,hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let x : Fin n → Bool := fun q => decide (q=p)
  have hpos : ∀ w ∈ ({o} : Finset ℕ), v x w := by simpa [v,x] using (ho p).mpr hp
  obtain ⟨R,hR,hRc,hRx,hRy⟩ := hcert x {o} (Finset.Subset.refl _) hpos
  have choose_out (w : {w // w ∈ R}) : ∃ q ∈ support C w.val, q ∉ T := by
    by_contra! hsub
    have hw := (mem_support C w p).mpr (hRx w w.property)
    have hst : support C w.val ⊆ T := hsub
    apply hpnot
    exact Finset.mem_biUnion.mpr ⟨w,hR w.property,by simpa only [clean,ite_eq_left hst] using hw⟩
  choose a ha using choose_out
  let Y := R.attach.image a
  let y : Fin n → Bool := fun q => decide (q ∈ Y)
  have hy (w : ℕ) (hw : w ∈ R) : v y w := by
    let w' : {w // w ∈ R} := ⟨w,hw⟩
    have hin : a w' ∈ Y := Finset.mem_image_of_mem a (Finset.mem_attach R w')
    apply value_mono C hg (fun q => decide (q=a w')) y _ w ((mem_support C w (a w')).mp (ha w').1)
    intro q hq
    simpa [y,of_decide_eq_true hq] using hin
  have hon := hRy y hy o (Finset.mem_singleton_self _)
  change value C y o = true at hon
  have hY : Y.card ≤ R.card := by
    have h := Finset.card_image_le (s:=R.attach) (f:=a)
    simpa [Y] using h
  have hkY : k ≤ Y.card := by
    by_contra! hsmall
    have hset : Finset.univ.filter (fun q => y q = true) = Y := by ext; simp [y]
    have hoff := hsparse y (by rwa [hset]) (by
      intro q hq
      have hnot : q ∉ Y := by
        rintro h
        obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp h
        exact (ha w).2 hq
      simp [y,hnot])
    exact Bool.noConfusion (hoff.symm.trans hon)
  have hA := Finset.card_filter_le A (· < n+C.size)
  simp only [Finset.card_singleton] at hRc
  change k ≤ A.card+1
  omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma projections_need_ors {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ) (hg : good C)
    (hz : value C (fun _ : Fin n => false) o = false) (hsup : support C o = T) :
    T.card ≤ ((dormant C T).filter (fun w => ¬ andAt C n w)).card+1 := by
  classical
  let Q (w : ℕ) := value C (fun _ : Fin n => false) w = false
  let L := fun w => if Q w then support C w ∩ T else ∅
  let G := (dormant C T).filter (fun w => ¬ andAt C n w)
  have big {w : ℕ} (hbig : 2 ≤ (L w).card) : Q w ∧ 2 ≤ (support C w ∩ T).card := by
    by_cases hq : Q w
    · exact ⟨hq,by simpa [L,hq] using hbig⟩
    · simp [L,hq] at hbig
  have range {w : ℕ} (hbig : 2 ≤ (L w).card) : w ∈ dormant C T := by
    obtain ⟨hq,htrace⟩ := big hbig
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (htrace.trans
      (Finset.card_le_card Finset.inter_subset_left))),hq,htrace⟩
  have step (w : ℕ) (hbig : 2 ≤ (L w).card) : ∃ P : Finset ℕ, (∀ r ∈ P, r < w) ∧
      P.card ≤ (if w ∈ G then 2 else 1) ∧ L w ⊆ P.biUnion L := by
    have hmem := range hbig
    obtain ⟨hq,htrace⟩ := big hbig
    have hl : L w = support C w ∩ T := by simp [L,hq]
    rcases gate_operation_split C hg w hq (htrace.trans (Finset.card_le_card Finset.inter_subset_left)) with
      ⟨hn,P,hpc,hdata,heq⟩ | ⟨_,r,hr,hrz,hsub⟩
    · have hc : w ∈ G := Finset.mem_filter.mpr ⟨hmem,hn⟩
      refine ⟨P,fun r hr => (hdata r hr).1,by simpa [hc] using hpc,?_⟩
      intro a ha
      obtain ⟨has,hat⟩ := Finset.mem_inter.mp (hl ▸ ha)
      obtain ⟨r,hr,har⟩ := Finset.mem_biUnion.mp (heq ▸ has)
      have hqr : Q r := (hdata r hr).2
      exact Finset.mem_biUnion.mpr ⟨r,hr,by simpa [L,hqr] using Finset.mem_inter.mpr ⟨har,hat⟩⟩
    · have hqr : Q r := hrz
      refine ⟨{r},by simpa using hr,?_,?_⟩
      · simp only [Finset.card_singleton]; split <;> decide
      · simp only [Finset.singleton_biUnion]
        rw [hl]
        intro a ha
        simpa [L,hqr] using Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
  have hcut := branching_cover L G step (n+C.size) {o} (by
    intro w _ hb
    exact (Finset.mem_Ico.mp (Finset.mem_filter.mp (range hb)).1).2)
  have hqo : Q o := hz
  have hlo : L o = T := by simp [L,hqo,hsup]
  simp only [Finset.singleton_biUnion,hlo,Finset.card_singleton] at hcut
  have hmono := Finset.card_filter_le G (· < n+C.size)
  change T.card ≤ G.card+1
  omega

lemma sharp_private_or_extra {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ) (hg : good C)
    (hz : value C (fun _ : Fin n => false) o = false) (hsup : support C o = T)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ T, x q = false) → value C x o = false) :
    T.card ≤ (assigned C T).card+1 ∨ T.card+k ≤ (dormant C T).card+2 := by
  classical
  by_cases hpaid : T.card ≤ (assigned C T).card+1
  · exact Or.inl hpaid
  right
  have hor := projections_need_ors C T o hg hz hsup
  have hpos (p : Fin n) : value C (fun q => decide (q=p)) o = true ↔ p ∈ T := by
    rw [←mem_support,hsup]
  have hand := many_private_ands C T o hg hpos hsparse (by omega)
  have hnotfull : T ≠ Finset.univ := by
    intro hall
    have hr := dormant_count C T o hg (fun p hp => (hpos p).mpr hp) hz
    have hsub : dormant C T ⊆ assigned C T := by
      intro w hw
      obtain ⟨hi,_,ht⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hi,hall ▸ Finset.subset_univ _,ht.trans (Finset.card_le_card Finset.inter_subset_left)⟩
    exact hpaid (hr.trans (Nat.add_le_add_right (Finset.card_le_card hsub) _))
  have hsub : (assigned C T).filter (andAt C n) ⊆ (dormant C T).filter (andAt C n) := by
    intro w hw
    obtain ⟨ha,hA⟩ := Finset.mem_filter.mp hw
    obtain ⟨hi,hst,hs⟩ := Finset.mem_filter.mp ha
    have hzero : value C (fun _ : Fin n => false) w = false := by
      cases h : value C (fun _ : Fin n => false) w with
      | false => rfl
      | true =>
        exfalso
        apply hnotfull
        apply Finset.eq_univ_of_forall
        intro p
        apply hst
        apply (mem_support C w p).mpr
        exact value_mono C hg _ _ (by simp) w h
    have hct : 2 ≤ (support C w ∩ T).card := by rwa [Finset.inter_eq_left.mpr hst]
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hi,hzero,hct⟩,hA⟩
  have hA := Finset.card_le_card hsub
  have hsplit := Finset.card_filter_add_card_filter_not (s:=dormant C T) (p:=andAt C n)
  omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma low_sharp_private_or_extra {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true) : T.card ≤ (assigned C T).card+1 ∨ T.card+k ≤ (dormant C T).card+2 := by
  classical
  cases C with
  | mk gates o' =>
    let C : Circuit := ⟨gates,o'⟩
    have hvalid : t < gates.length := by
      by_contra! h
      have hf := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gates.length ≤ n+t; omega)
      have ht := hlight (fun _ : Fin n => false) (by simpa using (show 0 < k by omega))
      exact Bool.noConfusion (hf.symm.trans ht)
    let j : Fin gates.length := ⟨t,hvalid⟩
    let D := frozen true gates t
    have hd : good D := fixed_gates true gates j hg fun i hi => Fin.ext (hu i hi)
    have eq_light (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p = true)).card < k)
        (w : ℕ) : value D x w = value C x w := fixed_eq true gates j o' x (hlight x hx) w
    have es (p : Fin n) (w : ℕ) : value D (fun r => decide (r=p)) w = value C (fun r => decide (r=p)) w := by
      apply eq_light
      have hf : Finset.univ.filter (fun r : Fin n => decide (r=p) = true) = {p} := by ext a; simp
      rw [hf,Finset.card_singleton]
      omega
    have sp (w : ℕ) : support (n:=n) D w = support C w := by
      ext p
      rw [mem_support, mem_support, es]
    have hsame : dormant D T = dormant C T := by
      ext w
      have ez := eq_light (fun _ => false) (by simpa using (show 0 < k by omega)) w
      simp only [dormant,Finset.mem_filter,sp,ez]
      rw [show D.size = C.size from fixed_size true gates t]
    have hassigned : assigned D T = assigned C T := by
      ext w
      simp only [assigned,Finset.mem_filter,sp]
      rw [show D.size = C.size from fixed_size true gates t]
    have hz : value D (fun _ : Fin n => false) o = false := by
      rw [eq_light _ (by simpa using (show 0 < k by omega)),hout]
      simp
    have hsupport : support D o = T := by
      ext p
      rw [mem_support,es,hout]
      simp
    have hsparse (x : Fin n → Bool) (hx : (Finset.univ.filter (fun q => x q = true)).card < k)
        (hn : ∀ q ∈ T, x q = false) : value D x o = false := by
      rw [eq_light x hx,hout]
      apply decide_eq_false
      rintro ⟨p,hp,ht⟩
      exact Bool.noConfusion ((hn p hp).symm.trans ht)
    simpa only [hsame,hassigned] using sharp_private_or_extra D T o hd hz hsupport hsparse

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma window_bound_from_row_alternative {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card) (hD : 2 ≤ (S d).card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (b : ℕ) (halt : ∀ i, (S i).card ≤ (assigned C (S i)).card+1 ∨
      (S i).card+b ≤ (dormant C (S i)).card+1)
    (he : (∑ i, if Disjoint (S i) y then (S i).card-y.card else 0) ≤
      ((S d).card-y.card) + (refunds S C y).card + y.card + b) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  let f := fun i : Fin m => min y.card (S i).card
  let ex := fun i : Fin m => if Disjoint (S i) y then (S i).card-y.card else 0
  have per (i : Fin m) : (if Disjoint (S i) y then (S i).card else min y.card (S i).card) =
      f i + ex i := by
    by_cases h : Disjoint (S i) y
    · simp [f,ex,h]; omega
    · simp [f,ex,h]
  have hsum := Finset.sum_congr (s₁:=(Finset.univ : Finset (Fin m))) rfl (fun i _ => per i)
  rw [Finset.sum_add_distrib] at hsum
  change (∑ i, ex i) ≤ _ at he
  have hf (i : Fin m) : f i ≤ (assigned C (S i)).card+1 :=
    card_light (S i) C (o i) t hg hu (hout i) hlight
  have hfd : (S d).card = f d + ((S d).card-y.card) := by dsimp [f]; omega
  by_cases hfull : ∀ i, (S i).card ≤ (assigned C (S i)).card+1
  · have hall := sum_row_weights S Finset.univ C (fun i => (S i).card) hpair (fun i _ => hfull i)
    have hgates : (Finset.univ.biUnion (fun i => assigned C (S i))).card ≤ C.gates.length := by
      calc
        _ ≤ (Finset.Ico n (n+C.size)).card := Finset.card_le_card (by
          intro w hw; obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw; exact (Finset.mem_filter.mp hi).1)
        _ = _ := by simp [Circuit.size]
    have hp (i : Fin m) : (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ (S i).card := by
      split <;> omega
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hp i)
    simp only [Finset.card_univ,Fintype.card_fin] at hall
    omega
  push Not at hfull
  obtain ⟨e,heweak⟩ := hfull
  have hes : y.card < (S e).card := by have hfe := hf e; dsimp [f] at hfe; omega
  rcases halt d with hstrong | hweak
  · let g := fun i : Fin m => f i + if i = d then ((S d).card-y.card) else 0
    have hg' (i) : g i ≤ (assigned C (S i)).card + 1 := by
      by_cases h : i = d
      · subst i; simpa [g,←hfd] using hstrong
      · simpa [g,h] using hf i
    have hq := (halt e).resolve_left (by omega)
    have hed : e ≠ d := by rintro rfl; omega
    have hall := weighted_exceptional_count S e C t y hk (by omega) hpair hg hu hlight
      ((S e).card+b) hq g (fun i _ => hg' i) hy
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) f (Finset.mem_univ e)
    have hde : d ∈ (Finset.univ : Finset (Fin m)).erase e := Finset.mem_erase.mpr ⟨hed.symm,Finset.mem_univ _⟩
    have hval : (∑ i ∈ Finset.univ.erase e, g i) =
        (∑ i ∈ Finset.univ.erase e, f i) + ((S d).card-y.card) := by simp [g,Finset.sum_add_distrib,hde]
    rw [hval] at hall
    have hfe : f e = y.card := Nat.min_eq_left (by omega)
    omega
  · have hall := weighted_exceptional_count S d C t y hk hD hpair hg hu hlight
      ((S d).card+b) hweak f (fun i _ => hf i) hy
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) f (Finset.mem_univ d)
    omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Small

lemma geometry_sharp {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (hk : 3 ≤ Y.card) (hn : n ≤ 7*Y.card+1 ∧ n+4 ≤ 8*Y.card)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∀ i, Disjoint (S i) Y → (S i).card ≤ Y.card+1) ∨
    ∃ d, 2 ≤ (S d).card ∧ (∑ i, if Disjoint (S i) Y then (S i).card-Y.card else 0) ≤
      ((S d).card-Y.card) + (Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)).card + Y.card + (Y.card-1) := by
  classical
  let k := Y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ k+2 ≤ (S i).card)
  let D := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)
  by_cases hne : B.Nonempty
  swap
  · refine Or.inl ?_
    intro i hi
    by_contra! hs
    exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,by dsimp [k]; omega⟩⟩
  obtain ⟨d,hd,hm⟩ := B.exists_max_image (fun i => (S i).card) hne
  have binfo {i} (hi : i ∈ B) : Disjoint (S i) Y ∧ k+2 ≤ (S i).card := (Finset.mem_filter.mp hi).2
  have hds := (binfo hd).2
  have hkk : 3 ≤ k := hk
  have h6 : B.card ≤ 9 := by
    by_contra! hlarge
    obtain ⟨I,hI,h10⟩ := Finset.exists_subset_card_eq (s:=B) (n:=10) (by omega)
    let V := Finset.univ \ Y
    have hin (i) (hi : i ∈ I) : S i ⊆ V := by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp (binfo (hI hi)).1 hp⟩
    have hinc := pair_incidence S I V hin hlin
    have hcard : V.card = n-k := by
      simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ Y),k]
    have hkN : k ≤ n := by simpa [k] using Finset.card_le_univ Y
    rw [hcard,h10] at hinc
    norm_num [Nat.choose] at hinc
    have hsum := Finset.sum_le_sum (s:=I) (fun i hi => (binfo (hI hi)).2)
    simp only [Finset.sum_const,h10,smul_eq_mul] at hsum
    change n ≤ 7*k+1 ∧ n+4 ≤ 8*k at hn
    omega
  let V := Finset.univ \ Y
  have hV : V.card = n-k := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ Y),k]
  have hkN : k ≤ n := by simpa [k] using Finset.card_le_univ Y
  have hinc := pair_incidence S B V (fun i hi p hp =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp (binfo hi).1 hp⟩) hlin
  rw [hV] at hinc
  have hminB := Finset.sum_le_sum (s:=B) (fun i hi => (binfo hi).2)
  simp only [Finset.sum_const,smul_eq_mul] at hminB
  have hp := price_cap S Y hlin B (fun i hi => (binfo hi).1)
  change k + _ ≤ _ at hp
  have hM := Finset.sum_le_sum (s:=B) (fun i hi => hm i hi)
  simp only [Finset.sum_const,smul_eq_mul] at hM
  have hpos : 0 < B.card := Finset.card_pos.mpr hne
  have key : (∑ i ∈ B, (S i).card) ≤ B.card * (k+1) + (S d).card + (k-1) := by
    generalize hr : B.card = r at *
    interval_cases r <;> norm_num [Nat.choose] at * <;> omega
  let b (i : Fin m) := (S i).card - (k+1)
  have splitB (i : Fin m) (hi : i ∈ B) : (S i).card = (k+1) + b i := by
    have h := (binfo hi).2
    dsimp [b]
    omega
  have heq := Finset.sum_congr (s₂:=B) rfl splitB
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at heq
  have hbudget : (∑ i ∈ B, b i) ≤ (S d).card + (k-1) := by omega
  have hper (i : Fin m) : (if Disjoint (S i) Y then (S i).card-k else 0) ≤
      (if i ∈ D then 1 else 0) + (if i ∈ B then b i else 0) := by
    by_cases hdY : Disjoint (S i) Y
    · by_cases hib : i ∈ B
      · have hs := (binfo hib).2
        have hid : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdY,by omega⟩
        simp [hdY, hib, hid, b]
        omega
      · have hs : (S i).card ≤ k+1 := by
          by_contra! h
          exact hib (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdY,by omega⟩)
        by_cases his : 2 ≤ (S i).card
        · have hid : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdY,his⟩
          simp [hdY, hib, hid]
          omega
        · simp [hdY, hib]
          omega
    · simp [hdY]
  have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hper i)
  rw [Finset.sum_add_distrib, Fintype.sum_ite_mem, Fintype.sum_ite_mem] at he
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at he
  refine Or.inr ⟨d,by omega,?_⟩
  change (∑ i, if Disjoint (S i) Y then (S i).card-k else 0) ≤ ((S d).card-k)+D.card+k+(k-1)
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997.Light

theorem size_window_sharp : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+4 ≤ 8*y.card)) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by

  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy
  by_cases hk : y.card ≤ 2
  · exact PEqualNP.Outside.L_meta_997_aux.two_window_of_card_le_two C y t S o hg hu hy hlin ho hk
  rcases geometry_sharp S y (by omega) (hn.resolve_left hk) hlin with hr | ⟨d,hds,hb⟩
  · exact window_bound_one_extra S C o t y hlin hg hu ho hlight hr
  · let D := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
    have href := disjoint_outputs_refunded S C o y D hlin ho (fun i hi => (Finset.mem_filter.mp hi).2)
    apply window_bound_from_row_alternative S d C o t y (by omega) hds hlin hg hu ho hlight hy (y.card-1)
    · intro i
      rcases low_sharp_private_or_extra C (S i) (o i) t (by omega) hg hu (ho i) hlight with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · change (∑ i, if Disjoint (S i) y then (S i).card - y.card else 0) ≤
        ((S d).card-y.card) + D.card + y.card + (y.card-1) at hb
      omega

theorem num_inputs_twenty : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 20 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  intro n m S C o t y hn
  apply size_window_sharp n m S C o t y
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small

lemma geometry_pool {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (V : Finset (Fin n)) (hpool : ∀ i, Disjoint (S i) Y → Y.card+2 ≤ (S i).card → S i ⊆ V)
    (hk : 3 ≤ Y.card) (hn : V.card ≤ 6*Y.card+1 ∧ V.card+4 ≤ 7*Y.card)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∀ i, Disjoint (S i) Y → (S i).card ≤ Y.card+1) ∨
    ∃ d, 2 ≤ (S d).card ∧ (∑ i, if Disjoint (S i) Y then (S i).card-Y.card else 0) ≤
      ((S d).card-Y.card) + (Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)).card + Y.card + (Y.card-1) := by
  classical
  let k := Y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ k+2 ≤ (S i).card)
  let D := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)
  by_cases hne : B.Nonempty
  swap
  · refine Or.inl ?_
    intro i hi
    by_contra! hs
    exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi,by dsimp [k]; omega⟩⟩
  obtain ⟨d,hd,hm⟩ := B.exists_max_image (fun i => (S i).card) hne
  have binfo {i} (hi : i ∈ B) : Disjoint (S i) Y ∧ k+2 ≤ (S i).card := (Finset.mem_filter.mp hi).2
  have hds := (binfo hd).2
  have hkk : 3 ≤ k := hk
  have h6 : B.card ≤ 9 := by
    by_contra! hlarge
    obtain ⟨I,hI,h10⟩ := Finset.exists_subset_card_eq (s:=B) (n:=10) (by omega)
    have hin (i) (hi : i ∈ I) : S i ⊆ V :=
      hpool i (binfo (hI hi)).1 (binfo (hI hi)).2
    have hinc := pair_incidence S I V hin hlin
    rw [h10] at hinc
    norm_num [Nat.choose] at hinc
    have hsum := Finset.sum_le_sum (s:=I) (fun i hi => (binfo (hI hi)).2)
    simp only [Finset.sum_const,h10,smul_eq_mul] at hsum
    change V.card ≤ 6*k+1 ∧ V.card+4 ≤ 7*k at hn
    omega
  have hinc := pair_incidence S B V (fun i hi => hpool i (binfo hi).1 (binfo hi).2) hlin
  have hsub : B.biUnion S ⊆ V := by
    intro x hx
    obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp hx
    exact hpool i (binfo hi).1 (binfo hi).2 he
  have hminB := Finset.sum_le_sum (s:=B) (fun i hi => (binfo hi).2)
  simp only [Finset.sum_const,smul_eq_mul] at hminB
  have hp := line_union S hlin B
  have hcapacity := Finset.card_le_card hsub
  have hM := Finset.sum_le_sum (s:=B) (fun i hi => hm i hi)
  simp only [Finset.sum_const,smul_eq_mul] at hM
  have hpos : 0 < B.card := Finset.card_pos.mpr hne
  have key : (∑ i ∈ B, (S i).card) ≤ B.card * (k+1) + (S d).card + (k-1) := by
    generalize hr : B.card = r at *
    interval_cases r <;> norm_num [Nat.choose] at * <;> omega
  let b (i : Fin m) := (S i).card - (k+1)
  have splitB (i : Fin m) (hi : i ∈ B) : (S i).card = (k+1) + b i := by
    have h := (binfo hi).2
    dsimp [b]
    omega
  have heq := Finset.sum_congr (s₂:=B) rfl splitB
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at heq
  have hbudget : (∑ i ∈ B, b i) ≤ (S d).card + (k-1) := by omega
  have hper (i : Fin m) : (if Disjoint (S i) Y then (S i).card-k else 0) ≤
      (if i ∈ D then 1 else 0) + (if i ∈ B then b i else 0) := by
    by_cases hdY : Disjoint (S i) Y
    · by_cases hib : i ∈ B
      · have hs := (binfo hib).2
        have hid : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdY,by omega⟩
        simp [hdY, hib, hid, b]
        omega
      · have hs : (S i).card ≤ k+1 := by
          by_contra! h
          exact hib (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdY,by omega⟩)
        by_cases his : 2 ≤ (S i).card
        · have hid : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdY,his⟩
          simp [hdY, hib, hid]
          omega
        · simp [hdY, hib]
          omega
    · simp [hdY]
  have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hper i)
  rw [Finset.sum_add_distrib, Fintype.sum_ite_mem, Fintype.sum_ite_mem] at he
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at he
  refine Or.inr ⟨d,by omega,?_⟩
  change (∑ i, if Disjoint (S i) Y then (S i).card-k else 0) ≤ ((S d).card-k)+D.card+k+(k-1)
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997.Light

theorem supported_large_rows : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card ≤ 2 ∨ ∃ V : Finset (Fin n), (∀ i, Disjoint (S i) y → y.card+2 ≤ (S i).card → S i ⊆ V) ∧
      V.card ≤ 6*y.card+1 ∧ V.card+4 ≤ 7*y.card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by

  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy
  by_cases hk : y.card ≤ 2
  · exact PEqualNP.Outside.L_meta_997_aux.two_window_of_card_le_two C y t S o hg hu hy hlin ho hk
  obtain ⟨V, hpool, hsize⟩ := hn.resolve_left hk
  rcases geometry_pool S y V hpool (by omega) hsize hlin with hr | ⟨d,hds,hb⟩
  · exact window_bound_one_extra S C o t y hlin hg hu ho hlight hr
  · let D := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
    have href := disjoint_outputs_refunded S C o y D hlin ho (fun i hi => (Finset.mem_filter.mp hi).2)
    apply window_bound_from_row_alternative S d C o t y (by omega) hds hlin hg hu ho hlight hy (y.card-1)
    · intro i
      rcases low_sharp_private_or_extra C (S i) (o i) t (by omega) hg hu (ho i) hlight with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · change (∑ i, if Disjoint (S i) y then (S i).card - y.card else 0) ≤
        ((S d).card-y.card) + D.card + y.card + (y.card-1) at hb
      omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

def hotEmpty {n : ℕ} (C : Circuit) (y : Fin n → Bool) : Finset ℕ :=
  (Finset.Ico n (n+C.size)).filter fun w => support (n:=n) C w = ∅ ∧ value C y w = true

lemma mintrue_hot_count {n k : ℕ} (C : Circuit) (hg : good C) (w : ℕ) (y : Fin n → Bool)
    (hy : value C y w = true)
    (hsmall : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x w = false) : k ≤ (hotEmpty (n:=n) C y).card + 1 := by
  classical
  let G := hotEmpty (n:=n) C y
  have hG (a) (ha : a ∈ G) : n ≤ a ∧ a < n+C.size := Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1
  obtain ⟨B,hd,hcap,transfer⟩ := cut C hg G hG (n+C.size) {w} (fun a _ ha => (hG a ha).2)
  let U := B.filter fun a => value C y a = true
  have hex (a : {a // a ∈ U}) : ∃ p : Fin n, p ∈ support C a.val := by
    have hdata := Finset.mem_filter.mp a.property
    by_cases hhi : a.val < n+C.size
    · by_cases hin : a.val < n
      · let p : Fin n := ⟨a.val,hin⟩
        refine ⟨p,(mem_support C a.val p).mpr ?_⟩
        exact (input_value C (fun v => decide (v=p)) p).trans (by simp)
      · by_contra! hemp
        have he : support (n:=n) C a.val = ∅ := Finset.eq_empty_iff_forall_notMem.mpr hemp
        exact Finset.disjoint_left.mp hd hdata.1
          (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,hhi⟩,he,hdata.2⟩)
    · have hf := missing_value C y a.val (by omega)
      exact False.elim (Bool.noConfusion (hf.symm.trans hdata.2))
  choose pt hpt using hex
  let X := U.attach.image pt
  let x := fun p : Fin n => decide (p ∈ X)
  have hxx : Finset.univ.filter (fun p => x p = true) = X := by ext p; simp [x]
  have hp (a) (ha : a ∈ B) (ht : value C y a = true) : value C x a = true := by
    let a' : {a // a ∈ U} := ⟨a,Finset.mem_filter.mpr ⟨ha,ht⟩⟩
    have hmem : pt a' ∈ X := Finset.mem_image.mpr ⟨a',Finset.mem_attach _ _,rfl⟩
    apply value_mono C hg (fun v => decide (v=pt a')) x _ a ((mem_support C a (pt a')).mp (hpt a'))
    intro v hv
    have he : v = pt a' := of_decide_eq_true hv
    simpa [x,he] using hmem
  have ht := transfer y x hp w (by simp) hy
  have hlow : k ≤ X.card := by
    by_contra! h
    have hf := hsmall x (by rwa [hxx])
    exact Bool.noConfusion (hf.symm.trans ht)
  have hU : X.card ≤ B.card := calc
    _ ≤ U.attach.card := Finset.card_image_le
    _ = U.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
  have h3 := Finset.card_filter_le G (fun w => w < n+C.size)
  change k ≤ G.card+1
  simp only [Finset.card_singleton] at hcap
  omega

lemma guard_hot_gates {n k : ℕ} (C : Circuit) (t : ℕ) (y : Finset (Fin n)) (hk : 0 < k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false) :
    ∃ A : Finset ℕ, k ≤ A.card+1 ∧ A ⊆ Finset.Ico n (n+t) ∧
      ∀ w ∈ A, support (n:=n) C w = ∅ ∧ value C (fun p => decide (p ∈ y)) w = true := by
  classical
  cases C with
  | mk gates out =>
    let C : Circuit := ⟨gates,out⟩
    have h0 := hl (fun _ => false) (by simpa using hk)
    have hvalid : t < gates.length := by
      by_contra! h
      have hf := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gates.length ≤ n+t; omega)
      exact Bool.noConfusion (hf.symm.trans h0)
    let j : Fin gates.length := ⟨t,hvalid⟩
    have hj : (gates.get j).op = .not := by
      by_contra hn
      have hm : good C := by
        intro g hgin
        obtain ⟨hops,hlen⟩ := hg g hgin
        refine ⟨?_,hlen⟩
        rcases hops with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp hgin
          have hop : (gates.get (⟨a,ha⟩ : Fin gates.length)).op = .not := (congrArg Gate.op he).trans h
          have hidx := hu ⟨a,ha⟩ hop
          have ej : (⟨a,ha⟩ : Fin gates.length) = j := Fin.ext hidx
          exact False.elim (hn (ej ▸ hop))
      have hh := value_mono C hm (fun _ => false) (fun p => decide (p ∈ y)) (by simp) (n+t) h0
      exact Bool.noConfusion (hy.symm.trans hh)
    let P : Circuit := ⟨gates.take t,0⟩
    let w := (gates.get j).inputs.headD (n+t)
    have hnot (x : Fin n → Bool) : value C x (n+t) = !(value P x w) := not_value_prefix gates j hj x
    have hw : value P (fun p => decide (p ∈ y)) w = true := by
      change value C _ (n+t) = false at hy
      rw [hnot] at hy
      simpa using hy
    have hsmall (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p = true)).card < k) :
        value P x w = false := by
      have h := hl x hx
      change value C x (n+t) = true at h
      rw [hnot] at h
      simpa using h
    have hgood : good P := pre_basis gates j hg (fun a ha => Fin.ext (hu a ha))
    refine ⟨hotEmpty (n:=n) P (fun p => decide (p ∈ y)),mintrue_hot_count P hgood w _ hw hsmall,?_,?_⟩
    · intro v hv
      have h := (Finset.mem_filter.mp hv).1
      simpa [P,Circuit.size,List.length_take,Nat.min_eq_left hvalid.le] using h
    · intro v hv
      have hi := Finset.mem_Ico.mp (Finset.mem_filter.mp hv).1
      have vlt : v < n+t := by simpa [P,Circuit.size,List.length_take,Nat.min_eq_left hvalid.le] using hi.2
      have es : support (n:=n) C v = support P v := by
        ext p
        rw [mem_support,mem_support]
        rw [show value C (fun a => decide (a=p)) v = value P _ v from prefix_value_eq gates j _ _ vlt]
      refine ⟨es.trans (Finset.mem_filter.mp hv).2.1,?_⟩
      rw [show value C (fun p => decide (p ∈ y)) v = value P _ v from prefix_value_eq gates j _ _ vlt]
      exact (Finset.mem_filter.mp hv).2.2

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem card_light_erase_switch {n k : ℕ} (T : Finset (Fin n)) (C : Circuit) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k → value C x (n+t) = true) :
    min k T.card ≤ ((assigned C T).erase (n+t)).card+1 := by
  classical
  by_cases hz : n+t ∈ assigned C T
  · have hall : ∀ p : Fin n, p ∈ T := by
      intro p
      apply (Finset.mem_filter.mp hz).2.1
      apply (mem_support C _ p).mpr
      apply hl
      have hsingle : Finset.univ.filter (fun r : Fin n => decide (r=p) = true) = {p} := by ext r; simp
      rw [hsingle,Finset.card_singleton]; omega
    have sub : dormant C T ⊆ (assigned C T).erase (n+t) := by
      intro w hw
      obtain ⟨hbound,hzero,hmany⟩ := Finset.mem_filter.mp hw
      have h0 := hl (fun _ => false) (by simpa using (show 0 < k by omega))
      refine Finset.mem_erase.mpr ⟨fun he => ?_,Finset.mem_filter.mpr ⟨hbound,fun p _ => hall p,?_⟩⟩
      · rw [he] at hzero
        exact Bool.noConfusion (hzero.symm.trans h0)
      · exact hmany.trans (Finset.card_le_card Finset.inter_subset_left)
    have hA := low_dormant_count C T o t hk hg hu hout hl
    have hc := Finset.card_le_card sub
    omega
  · rw [Finset.erase_eq_of_notMem hz]
    exact card_light T C o t hg hu hout hl

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

private lemma sameFilter {α : Type*} (p : α → Prop) (s : Finset α) (d e : DecidablePred p) :
    @Finset.filter α p d s = @Finset.filter α p e s := by
  have h : d = e := Subsingleton.elim _ _
  cases h
  rfl

lemma low_many_private_ands {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true)
    (hunder : (assigned C T).card+1 < T.card) : k ≤ ((assigned C T).filter (andAt C n)).card+1 := by
  classical
  cases C with
  | mk gates o' =>
    let C : Circuit := ⟨gates,o'⟩
    have hvalid : t < gates.length := by
      by_contra! h
      have hf := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gates.length ≤ n+t; omega)
      have ht := hlight (fun _ : Fin n => false) (by simpa using (show 0 < k by omega))
      exact Bool.noConfusion (hf.symm.trans ht)
    let j : Fin gates.length := ⟨t,hvalid⟩
    let D := frozen true gates t
    have hd : good D := fixed_gates true gates j hg fun i hi => Fin.ext (hu i hi)
    have eq_light (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p = true)).card < k)
        (w : ℕ) : value D x w = value C x w := fixed_eq true gates j o' x (hlight x hx) w
    have es (p : Fin n) (w : ℕ) : value D (fun r => decide (r=p)) w = value C (fun r => decide (r=p)) w := by
      apply eq_light
      have hf : Finset.univ.filter (fun r : Fin n => decide (r=p) = true) = {p} := by ext a; simp
      rw [hf,Finset.card_singleton]
      omega
    have sp (w : ℕ) : support (n:=n) D w = support C w := by
      ext p
      rw [mem_support, mem_support, es]
    have hsame : dormant D T = dormant C T := by
      ext w
      have ez := eq_light (fun _ => false) (by simpa using (show 0 < k by omega)) w
      simp only [dormant,Finset.mem_filter,sp,ez]
      rw [show D.size = C.size from fixed_size true gates t]
    have hassigned : assigned D T = assigned C T := by
      ext w
      simp only [assigned,Finset.mem_filter,sp]
      rw [show D.size = C.size from fixed_size true gates t]
    have hz : value D (fun _ : Fin n => false) o = false := by
      rw [eq_light _ (by simpa using (show 0 < k by omega)),hout]
      simp
    have hsupport : support D o = T := by
      ext p
      rw [mem_support,es,hout]
      simp
    have hsparse (x : Fin n → Bool) (hx : (Finset.univ.filter (fun q => x q = true)).card < k)
        (hn : ∀ q ∈ T, x q = false) : value D x o = false := by
      rw [eq_light x hx,hout]
      apply decide_eq_false
      rintro ⟨p,hp,ht⟩
      exact Bool.noConfusion ((hn p hp).symm.trans ht)
    have hpos (p : Fin n) : value D (fun q => decide (q=p)) o = true ↔ p ∈ T := by
      rw [←mem_support,hsupport]
    have hh := many_private_ands D T o hd hpos hsparse (by rwa [hassigned])
    have hnotfull : T ≠ Finset.univ := by
      intro hall
      have hr := dormant_count D T o hd (fun p hp => (hpos p).mpr hp) hz
      have hs : dormant D T ⊆ assigned D T := by
        intro w hw
        obtain ⟨hi,_,ht⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨hi,hall ▸ Finset.subset_univ _,ht.trans (Finset.card_le_card Finset.inter_subset_left)⟩
      have hb := hr.trans (Nat.add_le_add_right (Finset.card_le_card hs) _)
      rw [hassigned] at hb
      exact (Nat.not_lt_of_le hb) hunder
    have hstable : (assigned D T).filter (andAt D n) = (assigned C T).filter (andAt C n) := by
      rw [hassigned]
      apply Finset.filter_congr
      intro w hw
      obtain ⟨hi,ht,_⟩ := Finset.mem_filter.mp hw
      obtain ⟨lo,hi⟩ := Finset.mem_Ico.mp hi
      have hne : w ≠ n+t := by
        intro he
        apply hnotfull
        apply Finset.eq_univ_of_forall
        intro p
        apply ht
        apply (mem_support C w p).mpr
        rw [he,←es]
        exact fixed_value true gates j _
      have hglen : w-n < gates.length := by change w<n+gates.length at hi; omega
      have hglen' : w-n < D.gates.length := by simpa [D,frozen] using hglen
      have htne : t ≠ w-n := by omega
      simp [andAt,D,C,frozen,hglen,htne]
    rw [hstable] at hh
    exact hh.trans (le_of_eq (congrArg (fun z : Finset ℕ => z.card+1)
      (sameFilter (andAt C n) (assigned C T) _ _)))

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997_aux

private theorem terminal_switch_closed {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → i.val = t)
    (hl : PEqualNP.Outside.L_meta_997.Light.value C (fun _ : Fin n => false) (n+t) = true)
    (hy : PEqualNP.Outside.L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false) :
    n+t ∈ Finset.Ico n (n+C.size) ∧ Heavy.supp C Y (n+t) = ∅ := by
  classical
  have hb : t < C.gates.length := by
    by_contra! ht
    have hf := PEqualNP.Outside.L_meta_997.Light.missing_value C (fun _ : Fin n => false) (n+t)
      (by change n+C.gates.length ≤ n+t; omega)
    simp [hf] at hl
  refine ⟨Finset.mem_Ico.mpr ⟨by omega, by change n+t < n+C.gates.length; omega⟩,?_⟩
  obtain ⟨gs,oo⟩ := C
  let j : Fin gs.length := ⟨t,hb⟩
  have hj : (gs.get j).op = .not := by
    by_contra hn
    have hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hmem
      obtain ⟨hrs,hlen⟩ := hg g hmem
      refine ⟨?_,hlen⟩
      rcases hrs with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨a,ha,he⟩ := List.mem_iff_getElem.mp hmem
        have hop : (gs.get (⟨a,ha⟩ : Fin gs.length)).op = .not := (congrArg Gate.op he).trans h
        have ej : (⟨a,ha⟩ : Fin gs.length) = j := Fin.ext (hu _ hop)
        exact False.elim (hn (ej ▸ hop))
    have bad := PEqualNP.Outside.L_meta_997.Light.value_mono ⟨gs,oo⟩ hm (fun _ : Fin n => false) (fun p => decide (p ∈ Y)) (by simp) (n+t) hl
    exact Bool.noConfusion (hy.symm.trans bad)
  have hs := PEqualNP.Outside.L_meta_997.Light.pre_basis gs j hg (fun i hi => Fin.ext (hu i hi))
  have notval := PEqualNP.Outside.L_meta_997.Light.not_value_prefix (n:=n) gs j hj
  change PEqualNP.Outside.L_meta_997.Light.value ⟨gs,0⟩ (fun p : Fin n => decide (p ∈ Y)) (n+j.val) = false at hy
  rw [notval] at hy
  have hbase : PEqualNP.Outside.L_meta_997.Light.value ⟨gs.take j.val,0⟩ (fun p => decide (p ∈ Y))
      ((gs.get j).inputs.headD (n+j.val)) = true := by simpa using hy
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hnow := (Heavy.mem_supp _ _ _ _).mp hp
  change PEqualNP.Outside.L_meta_997.Light.value ⟨gs,0⟩ (fun v => decide (v ∈ Y ∨ v = p)) (n+j.val) = true at hnow
  rw [notval] at hnow
  have hhigh := PEqualNP.Outside.L_meta_997.Light.value_mono ⟨gs.take j.val,0⟩ hs (fun q => decide (q ∈ Y))
    (fun q => decide (q ∈ Y ∨ q = p)) (fun q hq => decide_eq_true (Or.inl (of_decide_eq_true hq))) _ hbase
  rw [hhigh] at hnow
  contradiction

/-- A disjoint output row has an actual OR with its exact high signature,
and all of its row's points already lie in this gate's low signature. -/
lemma terminal_or {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (o t : ℕ)
    (hcard : 2 ≤ T.card) (hdis : Disjoint T Y)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlzero : value C (fun _ : Fin n => false) (n+t) = true)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false) :
    ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ ¬ andAt C n w ∧ T ⊆ support C w ∧
      Heavy.supp C Y w = T ∧ w ≠ n+t := by
  classical
  let z : Fin n → Bool := fun r => decide (r ∉ T)
  let fire := fun (p : Fin n) (q : Fin n) => decide (q ∈ Y ∨ q=p)
  have hoff := (terminal_switch_closed C Y t hg hu hlzero hy).2
  obtain ⟨D,_,hgood,hagree⟩ := Heavy.heavy_model C Y t hg hu hy
  have above (p : Fin n) (q : Fin n) (hq : q ∈ Y) : fire p q = true :=
    decide_eq_true (Or.inl hq)
  have az (q : Fin n) (hq : q ∈ Y) : z q = true :=
    decide_eq_true (fun h => Finset.disjoint_left.mp hdis h hq)
  let result := ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ ¬ andAt C n w ∧ T ⊆ support C w ∧
      Heavy.supp C Y w = T ∧ w ≠ n+t
  have descend (w : ℕ) (hl : T ⊆ support C w) (hh : ∀ p ∈ T, value C (fire p) w = true)
      (hz : value C z w = false) : result := by
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      obtain ⟨lo,hi⟩ := support_gate C w (hcard.trans (Finset.card_le_card hl))
      have hidx : w-n < C.gates.length := by change w<n+C.gates.length at hi; omega
      let g := C.gates[w-n]
      have hne : w ≠ n+t := by
        intro he
        obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        have hab : p ∈ Heavy.supp C Y (n+t) := (Heavy.mem_supp ..).mpr (he ▸ hh p hp)
        simp [hoff] at hab
      obtain ⟨hop,_⟩ := hg g (List.getElem_mem _)
      rcases hop with hand | hor | hnot
      · let read := fun (x : Fin n → Bool) (r : ℕ) => if r<w then value C x r else false
        have hall (x : Fin n → Bool) : value C x w = true ↔ ∀ r ∈ g.inputs, read x r = true := by
          rw [gate_value C x w lo hi]
          change g.op.eval (g.inputs.map (read x)) = true ↔ _
          rw [hand]
          simp [GateOp.eval]
        have hfail : ¬∀ r ∈ g.inputs, read z r = true := by
          intro h
          exact Bool.noConfusion (hz.symm.trans ((hall z).mpr h))
        push Not at hfail
        obtain ⟨r,hr,hrc⟩ := hfail
        obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < T.card by omega)
        have hy := (hall _).mp (hh p hp) r hr
        have hrw : r<w := by by_contra h; simp [read,h] at hy
        apply ih r hrw
        · intro a ha
          apply (mem_support C r a).mpr
          simpa [read,hrw] using (hall _).mp ((mem_support C w a).mp (hl ha)) r hr
        · intro a ha
          simpa [read,hrw] using (hall _).mp (hh a ha) r hr
        · simpa [read,hrw] using hrc
      · refine ⟨w,Finset.mem_Ico.mpr ⟨lo,hi⟩,?_,hl,?_,hne⟩
        · simp [andAt,hidx,show C.gates[w-n].op = .or from hor]
        · ext p
          rw [Heavy.mem_supp]
          constructor
          · intro hp
            by_contra hpt
            have hle (q : Fin n) (hq : fire p q = true) : z q = true := by
              rcases of_decide_eq_true hq with h | h
              · exact az q h
              · exact h ▸ decide_eq_true hpt
            have ht : PEqualNP.Outside.L_meta_997.Light.value D (fire p) w = true := (hagree (fire p) (above p) w).trans hp
            have hr := PEqualNP.Outside.L_meta_997.Light.value_mono D hgood (fire p) z hle w ht
            exact Bool.noConfusion (hz.symm.trans ((hagree z az w).symm.trans hr))
          · exact hh p
      · have ht := hu (⟨w-n,hidx⟩ : Fin C.gates.length) hnot
        change w-n=t at ht
        exact (hne (by omega)).elim
  apply descend o
  · intro p hp
    apply (mem_support C o p).mpr
    rw [hout]
    exact decide_eq_true ⟨p,hp,by simp⟩
  · intro p hp
    rw [hout]
    exact decide_eq_true ⟨p,hp,decide_eq_true (Or.inr rfl)⟩
  · rw [hout]
    apply decide_eq_false
    rintro ⟨p,hp,hf⟩
    exact (of_decide_eq_true hf) hp

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997

def underpaid {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun i => (Light.assigned C (S i)).card+1 < (S i).card

abbrev opAnd (C : Circuit) (n w : ℕ) : Prop := Light.andAt C n w
end PEqualNP.Outside.L_meta_997_aux

namespace PEqualNP.Outside.L_meta_997_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997

def underDisjoint {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) :=
  (underpaid C S).filter fun i => Disjoint (S i) Y

theorem low_budget_with_gate_set {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → i.val = t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      PEqualNP.Outside.L_meta_997.Light.value C x (n+t) = true)
    (_hy : PEqualNP.Outside.L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), PEqualNP.Outside.L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (bonus : Fin m → ℕ)
    (hb : ∀ i, Disjoint (S i) Y → bonus i = 0)
    (hp : ∀ i, ¬Disjoint (S i) Y → min k (S i).card + bonus i ≤
      ((Light.assigned C (S i)).erase (n+t)).card+1)
    (A : Finset ℕ) (ar : A ⊆ Finset.Ico n (n+C.size))
    (az : n+t ∉ A)
    (ap : ∀ w ∈ A, ∀ i, w ∈ Light.assigned C (S i) →
      i ∈ underDisjoint C S Y ∧ ¬opAnd C n w)
    (af : ∀ w ∈ A, ∀ i ∈ underDisjoint C S Y, ¬opAnd C n w →
      S i ⊆ Light.support C w → Heavy.supp C Y w ≠ S i)
    (terminal : ∀ i ∈ underDisjoint C S Y, ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ w ≠ n+t ∧
      ¬opAnd C n w ∧ S i ⊆ Light.support C w ∧ Heavy.supp C Y w = S i) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min k (S i).card) + (∑ i, bonus i) + (A.card+1) ≤
      C.size + m + ∑ i ∈ underDisjoint C S Y, ((S i).card-(k+1)) := by
  classical
  let D := underDisjoint C S Y
  let z := n+t
  let B (i : Fin m) := (if i ∈ D then (Light.assigned C (S i)).filter (opAnd C n) else Light.assigned C (S i)).erase z
  let P := Finset.univ.biUnion B
  have own {i : Fin m} {w : ℕ} (h : w ∈ B i) : w ∈ Light.assigned C (S i) := by
    have hh := (Finset.mem_erase.mp h).2
    split at hh
    · exact (Finset.mem_filter.mp hh).1
    · exact hh
  have pair {i j : Fin m} (hne : i ≠ j) : Disjoint (B i) (B j) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hi hj
    obtain ⟨_,hs,hn⟩ := Finset.mem_filter.mp (own hi)
    have ht := (Finset.mem_filter.mp (own hj)).2.1
    have hsub : Light.support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hs hp,ht hp⟩
    have hh := (Finset.card_le_card hsub).trans (hlin i j hne)
    omega
  have pc : P.card = ∑ i, (B i).card :=
    Finset.card_biUnion (fun _ _ _ _ h => pair h)
  have dinfo {i : Fin m} (hi : i ∈ D) :
      (Light.assigned C (S i)).card+1 < (S i).card ∧ Disjoint (S i) Y :=
    ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2,(Finset.mem_filter.mp hi).2⟩
  have dlarge {i : Fin m} (hi : i ∈ D) : 2 ≤ (S i).card := by have := (dinfo hi).1; omega
  have zfree {i : Fin m} (hd : Disjoint (S i) Y) : z ∉ Light.assigned C (S i) := by
    intro hz
    obtain ⟨p,hp⟩ := hY
    have hs : p ∈ Light.support C z := by
      apply (Light.mem_support C z p).mpr
      apply hl
      have hsingle : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
      rw [hsingle,Finset.card_singleton]
      omega
    exact Finset.disjoint_left.mp hd ((Finset.mem_filter.mp hz).2.1 hs) hp
  have small (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min k (S i).card) + bonus i ≤
      (B i).card + 1 + (if i ∈ D then 1 else 0) + (if i ∈ D then (S i).card-(k+1) else 0) := by
    by_cases hi : i ∈ D
    · obtain ⟨hshort,hd⟩ := dinfo hi
      have hc := Light.low_many_private_ands C (S i) (o i) t hk hg hu (ho i) hl hshort
      change k ≤ ((Light.assigned C (S i)).filter (opAnd C n)).card+1 at hc
      have hnf : z ∉ (Light.assigned C (S i)).filter (opAnd C n) := fun h => zfree hd (Finset.mem_filter.mp h).1
      simp only [hb i hd,Nat.add_zero,hd,hi,B,ite_true,Finset.erase_eq_of_notMem hnf]
      omega
    · by_cases hd : Disjoint (S i) Y
      · have hgood : (S i).card ≤ (Light.assigned C (S i)).card+1 := by
          by_contra! hb
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,hd⟩)
        simpa [hb i hd,B,hi,hd,Finset.erase_eq_of_notMem (zfree hd)] using hgood
      · have hc := hp i hd
        simpa [B,hi,hd,z] using hc
  have term' (i : {i // i ∈ D}) := terminal i.val i.property
  choose f hf using term'
  let F := Finset.univ.image f
  have fcount : F.card = D.card := by
    have inj : Function.Injective f := by
      intro i j he
      apply Subtype.ext
      by_contra hne
      have eq : S i.val = S j.val := (hf i).2.2.2.2.symm.trans (he ▸ (hf j).2.2.2.2)
      have h := hlin i.val j.val hne
      rw [eq,Finset.inter_self] at h
      have := dlarge j.property
      omega
    simpa [F] using Finset.card_image_of_injective Finset.univ inj
  have disFP : Disjoint F P := by
    apply Finset.disjoint_left.mpr
    intro w hw hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
    by_cases he : j = i.val
    · subst j
      have hi := (Finset.mem_erase.mp hj).2
      simp only [i.property,ite_true] at hi
      exact (hf i).2.2.1 (Finset.mem_filter.mp hi).2
    · have hsub : S i.val ⊆ S i.val ∩ S j := fun p h =>
        Finset.mem_inter.mpr ⟨h,(Finset.mem_filter.mp (own hj)).2.1 ((hf i).2.2.2.1 h)⟩
      have h := (Finset.card_le_card hsub).trans (hlin i.val j (Ne.symm he))
      have := dlarge i.property
      omega
  have notZ : z ∉ F ∪ P := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i,_,hi⟩ := Finset.mem_image.mp h
      exact (hf i).2.1 hi
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_erase.mp hi).1 rfl
  have h0 := hl (fun _ => false) (by simpa using (show 0<k by omega))
  have hzr : z ∈ Finset.Ico n (n+C.size) := by
    apply Finset.mem_Ico.mpr
    refine ⟨by dsimp [z]; omega,?_⟩
    by_contra! hbad
    have hf := PEqualNP.Outside.L_meta_997.Light.missing_value C (fun _ : Fin n => false) z hbad
    exact Bool.noConfusion (hf.symm.trans h0)
  have dA : Disjoint A (insert z (F ∪ P)) := by
    refine Finset.disjoint_left.mpr ?_
    intro w ha hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact az ha
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
      exact af _ ha i i.property (hf i).2.2.1 (hf i).2.2.2.1 (hf i).2.2.2.2
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
      obtain ⟨hd,hn⟩ := ap w ha i (own hi)
      have hb := (Finset.mem_erase.mp hi).2
      change i ∈ D at hd
      simp only [hd,ite_true] at hb
      exact hn (Finset.mem_filter.mp hb).2
  have total : A ∪ insert z (F ∪ P) ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with ha | hw
    · exact ar ha
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hzr
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
      exact (hf i).1
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
      exact (Finset.mem_filter.mp (own hi)).1
  have ha := Finset.card_le_card total
  rw [Finset.card_union_of_disjoint dA,Finset.card_insert_of_notMem notZ,Finset.card_union_of_disjoint disFP,fcount,pc] at ha
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left] at ha
  have hdcard : (∑ i : Fin m, if i ∈ D then 1 else 0) = D.card := by simp
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin m))) (fun i _ => small i)
  simp only [Finset.sum_add_distrib,hdcard,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_one] at hs
  have heq : (∑ i, if i ∈ D then (S i).card - (k+1) else 0) = ∑ i ∈ D, ((S i).card-(k+1)) := by simp
  change _ ≤ C.size + m + ∑ i ∈ D, ((S i).card-(k+1))
  omega

theorem low_budget_with_terminal_bonus {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → i.val = t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      PEqualNP.Outside.L_meta_997.Light.value C x (n+t) = true)
    (hy : PEqualNP.Outside.L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), PEqualNP.Outside.L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (bonus : Fin m → ℕ)
    (hb : ∀ i, Disjoint (S i) Y → bonus i = 0)
    (hp : ∀ i, ¬Disjoint (S i) Y → min k (S i).card + bonus i ≤
      ((Light.assigned C (S i)).erase (n+t)).card+1)
    (terminal : ∀ i ∈ underDisjoint C S Y, ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ w ≠ n+t ∧
      ¬opAnd C n w ∧ S i ⊆ Light.support C w ∧ Heavy.supp C Y w = S i) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min k (S i).card) + (∑ i, bonus i) + k ≤
      C.size + m + ∑ i ∈ underDisjoint C S Y, ((S i).card-(k+1)) := by
  classical
  obtain ⟨A,ac,ar,ad⟩ := Light.guard_hot_gates C t Y (by omega : 0<k) hg hu hl hy
  have h0 := hl (fun _ => false) (by simpa using (show 0<k by omega))
  have hzr : n+t < n+C.size := by
    by_contra! hbad
    exact Bool.noConfusion ((Light.missing_value C (fun _ : Fin n => false) _ hbad).symm.trans h0)
  have h := low_budget_with_gate_set C Y t S o hk hY hg hu hl hy hlin ho bonus hb hp A
    (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1, (Finset.mem_Ico.mp (ar hw)).2.trans hzr⟩)
    (fun hw => (Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar hw)).2))
    (by
      intro w hw i hi
      have hs := (Finset.mem_filter.mp hi).2.2
      rw [(ad _ hw).1,Finset.card_empty] at hs
      omega)
    (by
      intro w hw i hi _ hsub
      have hs := Finset.card_le_card hsub
      rw [(ad _ hw).1,Finset.card_empty] at hs
      have hu := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      omega) terminal
  omega

theorem low_budget_with_terminals {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → i.val = t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      PEqualNP.Outside.L_meta_997.Light.value C x (n+t) = true)
    (hy : PEqualNP.Outside.L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), PEqualNP.Outside.L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (terminal : ∀ i ∈ underDisjoint C S Y, ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ w ≠ n+t ∧
      ¬opAnd C n w ∧ S i ⊆ Light.support C w ∧ Heavy.supp C Y w = S i) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min k (S i).card) + k ≤
      C.size + m + ∑ i ∈ underDisjoint C S Y, ((S i).card-(k+1)) := by
  simpa using low_budget_with_terminal_bonus C Y t S o hk hY hg hu hl hy hlin ho (fun _ => 0)
    (fun _ _ => rfl) (fun i _ => Light.card_light_erase_switch (S i) C (o i) t hk hg hu (ho i) hl) terminal
end PEqualNP.Outside.L_meta_997_aux

namespace PEqualNP.Outside.L_meta_997_aux
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997

theorem disjoint_terminal_deficit {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → i.val = t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      PEqualNP.Outside.L_meta_997.Light.value C x (n+t) = true)
    (hy : PEqualNP.Outside.L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), PEqualNP.Outside.L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    : (∑ i, if Disjoint (S i) Y then (S i).card else min k (S i).card) + k ≤
      C.size + m + ∑ i ∈ underDisjoint C S Y, ((S i).card-(k+1)) := by
  classical
  apply low_budget_with_terminals C Y t S o hk hY hg hu hl hy hlin ho
  intro i hi
  obtain ⟨hund,hd⟩ := Finset.mem_filter.mp hi
  have hshort := (Finset.mem_filter.mp hund).2
  have hs : 2 ≤ (S i).card := by omega
  obtain ⟨w,hw,ha,hL,hH,hz⟩ := Light.terminal_or C Y (S i) (o i) t hs hd hg hu (ho i)
    (hl (fun _ => false) (by simpa using (show 0<k by omega))) hy
  exact ⟨w,hw,hz,ha,hL,hH⟩

end PEqualNP.Outside.L_meta_997_aux

namespace PEqualNP.Outside.L_meta_997.Small

lemma quota_geometry {n m : ℕ} (S : Fin m → Finset (Fin n)) (B : Finset (Fin m))
    (k : ℕ) (V : Finset (Fin n)) (hk : 3 ≤ k) (hsize : V.card ≤ 6*k+1 ∧ V.card+3 ≤ 7*k)
    (hb : B.Nonempty) (hsub : ∀ i ∈ B, S i ⊆ V) (hbig : ∀ i ∈ B, k+2 ≤ (S i).card)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∃ d ∈ B, (∀ i ∈ B, (S i).card ≤ (S d).card) ∧
      ((∑ i ∈ B, (S i).card) ≤ B.card*(k+1)+(S d).card+(k-1) ∨
       (∑ i ∈ B, (S i).card) ≤ B.card*(k+2)+k) := by
  classical
  obtain ⟨d,hd,hm⟩ := B.exists_max_image (fun i => (S i).card) hb
  refine ⟨d,hd,hm,?_⟩
  have hcount : B.card ≤ 10 := by
    by_contra! hlarge
    obtain ⟨I,hI,h11⟩ := Finset.exists_subset_card_eq (s:=B) (n:=11) (by omega)
    have hinc := pair_incidence S I V (fun i hi => hsub i (hI hi)) hlin
    have hmin := Finset.sum_le_sum (s:=I) (fun i hi => hbig i (hI hi))
    simp only [Finset.sum_const,h11,smul_eq_mul] at hmin
    rw [h11] at hinc
    norm_num [Nat.choose] at hinc
    omega
  have hinc := pair_incidence S B V hsub hlin
  have hmin := Finset.sum_le_sum (s:=B) hbig
  have hmax := Finset.sum_le_sum (s:=B) hm
  simp only [Finset.sum_const,smul_eq_mul] at hmin hmax
  have hcap := line_union S hlin B
  have hU : B.biUnion S ⊆ V := by
    intro p hp
    obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp hp
    exact hsub i hi he
  have hV := Finset.card_le_card hU
  have hpos := Finset.card_pos.mpr hb
  generalize hr : B.card = r at *
  interval_cases r <;> norm_num [Nat.choose] at * <;> omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small

lemma excess_split {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (p : Fin m → Prop) [DecidablePred p] (k : ℕ) (hk : 2 ≤ k) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ p i ∧ k+2 ≤ (S i).card)
    let D := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)
    (∑ i, if Disjoint (S i) Y ∧ p i then (S i).card-k else 0) ≤
      D.card + ∑ i ∈ B, ((S i).card-(k+1)) := by
  classical
  intro B D
  have per (i) : (if Disjoint (S i) Y ∧ p i then (S i).card-k else 0) ≤
      (if i ∈ D then 1 else 0) + (if i ∈ B then (S i).card-(k+1) else 0) := by
    by_cases h : Disjoint (S i) Y ∧ p i
    · by_cases hs : k+2 ≤ (S i).card
      · have hb : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,h.2,hs⟩
        have hd : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,by omega⟩
        simp [h,hb,hd]; omega
      · by_cases hpos : k < (S i).card
        · have hd : i ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,by omega⟩
          simp [h,hd]; omega
        · simp [h,Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hpos)]
    · simp [h]
  have he := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simpa only [Finset.sum_add_distrib,Fintype.sum_ite_mem,Finset.sum_const,smul_eq_mul,mul_one] using he

lemma excess_identity {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (p : Fin m → Prop) [DecidablePred p] (k : ℕ) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) Y ∧ p i ∧ k+2 ≤ (S i).card)
    (∑ i, if Disjoint (S i) Y ∧ p i then (S i).card-(k+1) else 0) =
      ∑ i ∈ B, ((S i).card-(k+1)) := by
  classical
  intro B
  conv_rhs => rw [← Fintype.sum_ite_mem]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : Disjoint (S i) Y ∧ p i
  · by_cases hs : k+2 ≤ (S i).card
    · have hb : i ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,h.2,hs⟩
      simp [h,hb]
    · simp [h,Nat.sub_eq_zero_of_le (show (S i).card ≤ k+1 by omega)]
  · have hb : i ∉ B := fun hi => h ⟨(Finset.mem_filter.mp hi).2.1,(Finset.mem_filter.mp hi).2.2.1⟩
    simp [h,hb]

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma weak_disjoint_projection {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card) (hD : 2 ≤ (S d).card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hweak : (assigned C (S d)).card+1 < (S d).card)
    (_hdY : Disjoint (S d) y) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) +
        y.card + (y.card-1) + ((S d).card-y.card) ≤
      C.gates.length + m + ∑ i, if Disjoint (S i) y ∧
        (assigned C (S i)).card+1 < (S i).card then (S i).card-y.card else 0 := by
  classical
  let f (i : Fin m) := if Disjoint (S i) y ∧ (S i).card ≤ (assigned C (S i)).card+1
    then (S i).card else min y.card (S i).card
  let g (i : Fin m) := if Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card
    then (S i).card-y.card else 0
  have hweight (i : Fin m) : f i ≤ (assigned C (S i)).card+1 := by
    dsimp [f]
    split
    · rename_i h; exact h.2
    · exact card_light (S i) C (o i) t hg hu (hout i) hlight
  have hde : (S d).card = f d + ((S d).card-y.card) := by
    have hh : ¬ (S d).card ≤ (assigned C (S d)).card+1 := by omega
    simp [f,hh]
    omega
  have hq := (low_sharp_private_or_extra C (S d) (o d) t hk hg hu (hout d) hlight).resolve_left (by omega)
  have hall := weighted_exceptional_count S d C t y hk hD hpair hg hu hlight
      ((S d).card+(y.card-1)) (by omega) f (fun i _ => hweight i) hy
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) f (Finset.mem_univ d)
  have per (i : Fin m) : (if Disjoint (S i) y then (S i).card else min y.card (S i).card) =
      f i + g i := by
    by_cases h : Disjoint (S i) y
    · by_cases hs : (S i).card ≤ (assigned C (S i)).card+1
      · simp [f,g,h,hs,Nat.not_lt.mpr hs]
      · simp [f,g,h,hs, Nat.lt_of_not_ge hs]; omega
    · simp [f,g,h]
  have hsum := Finset.sum_congr (s₁:=(Finset.univ : Finset (Fin m))) rfl (fun i _ => per i)
  rw [Finset.sum_add_distrib] at hsum
  change _ ≤ C.gates.length + m + ∑ i, g i
  omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Small

lemma window_terminal_geometry {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hlarge : 3 ≤ y.card)
    (V : Finset (Fin n))
    (hcover : ∀ i, Disjoint (S i) y → (assigned C (S i)).card+1 < (S i).card →
      y.card+2 ≤ (S i).card → S i ⊆ V)
    (hV : V.card ≤ 6*y.card+1 ∧ V.card+3 ≤ 7*y.card)
    (hterminal : (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) + y.card ≤
      C.gates.length + m + ∑ i, if Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card
        then (S i).card-(y.card+1) else 0) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  let k := y.card
  let p := fun i => (assigned C (S i)).card+1 < (S i).card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧ p i ∧ k+2 ≤ (S i).card)
  let D := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  have data {i} (hi : i ∈ B) : Disjoint (S i) y ∧ p i ∧ k+2 ≤ (S i).card := (Finset.mem_filter.mp hi).2
  have hBD : B ⊆ D := by
    intro i hi
    have h := data hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,by omega⟩
  have href := disjoint_outputs_refunded S C o y D hpair hout (fun i hi => (Finset.mem_filter.mp hi).2)
  have hBr := (Finset.card_le_card hBD).trans href
  have eid := excess_identity S y p k
  change (∑ i, if Disjoint (S i) y ∧ p i then (S i).card-(k+1) else 0) =
      ∑ i ∈ B, ((S i).card-(k+1)) at eid
  change _ + k ≤ C.gates.length+m+∑ i, if Disjoint (S i) y ∧ p i then (S i).card-(k+1) else 0 at hterminal
  rw [eid] at hterminal
  by_cases hn : B.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.sum_empty] at hterminal
    omega
  obtain ⟨d,hd,_,hquota⟩ := quota_geometry S B k V hlarge hV hn
      (fun i hi => hcover i (data hi).1 (data hi).2.1 (data hi).2.2)
      (fun i hi => (data hi).2.2) hpair
  have splitcost (i) (hi : i ∈ B) : (S i).card = (k+1) + ((S i).card-(k+1)) := by
    have h := (data hi).2.2; omega
  have hsum := Finset.sum_congr (s₂:=B) rfl splitcost
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hsum
  rcases hquota with hprojection | hterm
  · have hDinfo := data hd
    have hcount := weak_disjoint_projection S d C o t y hk (by omega) hpair hg hu hout hlight hy hDinfo.2.1 hDinfo.1
    have ec := excess_split S y p k hk
    change (∑ i, if Disjoint (S i) y ∧ p i then (S i).card-k else 0) ≤ D.card+
      ∑ i ∈ B, ((S i).card-(k+1)) at ec
    change _ + k + (k-1) + ((S d).card-k) ≤ C.gates.length+m+
      ∑ i, if Disjoint (S i) y ∧ p i then (S i).card-k else 0 at hcount
    omega
  · have heq : B.card*(k+2) = B.card*(k+1)+B.card := by rw [show k+2 = (k+1)+1 by omega,Nat.mul_add,Nat.mul_one]
    omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma window_joint_pool {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hlarge : 3 ≤ y.card)
    (V : Finset (Fin n))
    (hcover : ∀ i, Disjoint (S i) y → (assigned C (S i)).card+1 < (S i).card →
      y.card+2 ≤ (S i).card → S i ⊆ V)
    (hV : V.card ≤ 6*y.card+1 ∧ V.card+3 ≤ 7*y.card) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  apply window_terminal_geometry S C o t y hk hpair hg hu hout hlight hy hlarge V hcover hV
  have ht := PEqualNP.Outside.L_meta_997_aux.disjoint_terminal_deficit C y t S o hk
    (Finset.card_pos.mp (by omega)) hg hu hlight hy hpair hout
  have he : PEqualNP.Outside.L_meta_997_aux.underDisjoint C S y =
      Finset.univ.filter (fun i => Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card) := by
    ext i
    simp [PEqualNP.Outside.L_meta_997_aux.underDisjoint,PEqualNP.Outside.L_meta_997_aux.underpaid,and_comm]
  rw [he] at ht
  simpa only [Finset.sum_filter,Circuit.size] using ht

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997.Light

theorem size_window_joint : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by

  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy
  by_cases hk : y.card ≤ 2
  · exact PEqualNP.Outside.L_meta_997_aux.two_window_of_card_le_two C y t S o hg hu hy hlin ho hk
  let V := Finset.univ \ y
  have hV : V.card = n-y.card := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y)]
  have hkN : y.card ≤ n := by simpa using Finset.card_le_univ y
  have hb := hn.resolve_left hk
  apply window_joint_pool S C o t y (by omega) hlin hg hu ho hlight hy (by omega) V
  · intro i hi _ _ p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hi hp⟩
  · omega

theorem num_inputs_twenty_one : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 21 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  intro n m S C o t y hn
  apply size_window_joint n m S C o t y
  omega

end PEqualNP.Outside.L_meta_997.Small


namespace PEqualNP.Outside.L_meta_997.Small

/-- On nineteen outside points the terminal count can miss by at most one
    gate whenever the distinguished-row count does not already suffice. -/
lemma quota_geometry_19 {n m : ℕ} (S : Fin m → Finset (Fin n)) (B : Finset (Fin m))
    (V : Finset (Fin n)) (hv : V.card ≤ 19)
    (hb : B.Nonempty) (hsub : ∀ i ∈ B, S i ⊆ V) (hbig : ∀ i ∈ B, 5 ≤ (S i).card)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∃ d ∈ B, ((∑ i ∈ B, (S i).card) ≤ B.card*4+(S d).card+2 ∨
       (∑ i ∈ B, (S i).card) ≤ B.card*5+4) := by
  classical
  obtain ⟨d,hd,hm⟩ := B.exists_max_image (fun i => (S i).card) hb
  refine ⟨d,hd,?_⟩
  have cap (I : Finset (Fin m)) (hI : I ⊆ B) :=
    pair_incidence S I V (fun i hi => hsub i (hI hi)) hlin
  have eight (I : Finset (Fin m)) (hI : I ⊆ B) (hc : I.card = 8) :
      (∑ i ∈ I, (S i).card) ≤ 42 := by
    have h := cap I hI
    rw [hc] at h
    norm_num [Nat.choose] at h
    omega
  by_cases large : 8 ≤ B.card
  · right
    let E := B.filter (fun i => 6 ≤ (S i).card)
    have hEB : E ⊆ B := Finset.filter_subset _ _
    have addcost (J I : Finset (Fin m)) (hJI : J ⊆ I) (hIB : I ⊆ B)
        (hJ : ∀ i ∈ J, 6 ≤ (S i).card) :
        5*I.card + J.card ≤ ∑ i ∈ I, (S i).card := by
      have hp := Finset.sum_le_sum (s:=I) (f:=fun i => 5+(if i ∈ J then 1 else 0))
        (g:=fun i => (S i).card) (fun i hi => by
          by_cases h : i ∈ J
          · simpa [h] using hJ i h
          · simpa [h] using hbig i (hIB hi))
      simpa [Finset.sum_add_distrib,Finset.sum_boole,Finset.inter_eq_right.mpr hJI,
        Nat.mul_comm] using hp
    have he : E.card ≤ 2 := by
      by_contra! h
      obtain ⟨J,hJE,h3⟩ := Finset.exists_subset_card_eq (s:=E) (n:=3) (by omega)
      obtain ⟨I,hJI,hIB,h8⟩ := Finset.exists_subsuperset_card_eq (hJE.trans hEB)
        (n:=8) (by omega) large
      have lo := addcost J I hJI hIB (fun i hi => (Finset.mem_filter.mp (hJE hi)).2)
      have up := eight I hIB h8
      omega
    obtain ⟨I,hEI,hIB,h8⟩ := Finset.exists_subsuperset_card_eq hEB (n:=8) (by omega) large
    have hout (i) (hi : i ∈ B \ I) : (S i).card = 5 := by
      obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp hi
      have hlo := hbig i hb
      have hu : ¬6 ≤ (S i).card := fun h => hn (hEI (Finset.mem_filter.mpr ⟨hb,h⟩))
      omega
    have hsum := Finset.sum_congr (s₁:=B \ I) rfl hout
    rw [Finset.sum_const,smul_eq_mul,Finset.card_sdiff_of_subset hIB,h8] at hsum
    have hsplit := Finset.sum_sdiff hIB (f:=fun i => (S i).card)
    have up := eight I hIB h8
    omega
  · have hinc := cap B (by rfl)
    have hmax := Finset.sum_le_sum (s:=B) hm
    simp only [Finset.sum_const,smul_eq_mul] at hmax
    have hcap := line_union S hlin B
    have hU : B.biUnion S ⊆ V := by
      intro p hp
      obtain ⟨i,hi,he⟩ := Finset.mem_biUnion.mp hp
      exact hsub i hi he
    have hV := Finset.card_le_card hU
    have hpos := Finset.card_pos.mpr hb
    generalize hr : B.card = r at *
    interval_cases r <;> norm_num [Nat.choose] at * <;> omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Small
lemma window_distinct_credit_bonus {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hk3 : y.card = 3)
    (V : Finset (Fin n))
    (hcover : ∀ i, Disjoint (S i) y → (assigned C (S i)).card+1 < (S i).card →
      y.card+2 ≤ (S i).card → S i ⊆ V)
    (hV : V.card ≤ 19) (slack : ℕ) (bonus : ℕ)
    (hfund : (Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)).card + 1 ≤
        (refunds S C y).card + slack + bonus)
    (hterminal : (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) + bonus + y.card ≤
      C.gates.length + m + ∑ i, if Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card
        then (S i).card-(y.card+1) else 0) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m + slack := by
  classical
  let k := y.card
  let p := fun i => (assigned C (S i)).card+1 < (S i).card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧ p i ∧ k+2 ≤ (S i).card)
  let D := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  have data {i} (hi : i ∈ B) : Disjoint (S i) y ∧ p i ∧ k+2 ≤ (S i).card := (Finset.mem_filter.mp hi).2
  change B.card+1 ≤ (refunds S C y).card+slack+bonus at hfund
  have h3 : k = 3 := hk3
  have hBD : B ⊆ D := by
    intro i hi
    have h := data hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.1,by omega⟩
  have href := disjoint_outputs_refunded S C o y D hpair hout (fun i hi => (Finset.mem_filter.mp hi).2)
  have hBr := (Finset.card_le_card hBD).trans href
  have eid := excess_identity S y p k
  change (∑ i, if Disjoint (S i) y ∧ p i then (S i).card-(k+1) else 0) =
      ∑ i ∈ B, ((S i).card-(k+1)) at eid
  change _ + bonus + k ≤ C.gates.length+m+∑ i, if Disjoint (S i) y ∧ p i then (S i).card-(k+1) else 0 at hterminal
  rw [eid] at hterminal
  by_cases hn : B.Nonempty
  swap
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he,Finset.sum_empty] at hterminal
    omega
  obtain ⟨d,hd,hquota⟩ := quota_geometry_19 S B V hV hn
      (fun i hi => hcover i (data hi).1 (data hi).2.1 (data hi).2.2)
      (fun i hi => by have h := (data hi).2.2; omega) hpair
  have splitcost (i) (hi : i ∈ B) : (S i).card = (k+1) + ((S i).card-(k+1)) := by
    have h := (data hi).2.2; omega
  have hsum := Finset.sum_congr (s₂:=B) rfl splitcost
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hsum
  have hmul : B.card*(k+1) = B.card*4 := by rw [h3]
  rw [hmul] at hsum
  rcases hquota with hprojection | hterm
  · have hDinfo := data hd
    have hcount := weak_disjoint_projection S d C o t y hk (by omega) hpair hg hu hout hlight hy hDinfo.2.1 hDinfo.1
    have ec := excess_split S y p k hk
    change (∑ i, if Disjoint (S i) y ∧ p i then (S i).card-k else 0) ≤ D.card+
      ∑ i ∈ B, ((S i).card-(k+1)) at ec
    change _ + k + (k-1) + ((S d).card-k) ≤ C.gates.length+m+
      ∑ i, if Disjoint (S i) y ∧ p i then (S i).card-k else 0 at hcount
    omega
  · have heq : B.card*5 = B.card*4+B.card := by omega
    omega
lemma window_distinct_credit {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hk3 : y.card = 3)
    (V : Finset (Fin n))
    (hcover : ∀ i, Disjoint (S i) y → (assigned C (S i)).card+1 < (S i).card →
      y.card+2 ≤ (S i).card → S i ⊆ V)
    (hV : V.card ≤ 19) (slack : ℕ)
    (hfund : (Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)).card + 1 ≤
        (refunds S C y).card + slack)
    (hterminal : (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) + y.card ≤
      C.gates.length + m + ∑ i, if Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card
        then (S i).card-(y.card+1) else 0) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m + slack := by
  apply window_distinct_credit_bonus S C o t y hk hpair hg hu hout hlight hy hk3 V hcover hV slack 0 hfund
  simpa using hterminal

lemma window_refund_22 {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < y.card →
      value C x (n+t) = true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hk3 : y.card = 3)
    (V : Finset (Fin n))
    (hcover : ∀ i, Disjoint (S i) y → (assigned C (S i)).card+1 < (S i).card →
      y.card+2 ≤ (S i).card → S i ⊆ V)
    (hV : V.card ≤ 19) (slack : ℕ)
    (hfund : (Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)).card + 1 ≤
        (refunds S C y).card + slack) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m + slack := by
  classical
  apply window_distinct_credit S C o t y hk hpair hg hu hout hlight hy hk3 V hcover hV slack hfund
  have ht := PEqualNP.Outside.L_meta_997_aux.disjoint_terminal_deficit C y t S o hk
    (Finset.card_pos.mp (by omega)) hg hu hlight hy hpair hout
  have he : PEqualNP.Outside.L_meta_997_aux.underDisjoint C S y =
      Finset.univ.filter (fun i => Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card) := by
    ext i
    simp [PEqualNP.Outside.L_meta_997_aux.underDisjoint,PEqualNP.Outside.L_meta_997_aux.underpaid,and_comm]
  rw [he] at ht
  simpa only [Finset.sum_filter,Circuit.size] using ht
end PEqualNP.Outside.L_meta_997.Light
namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997.Light
theorem num_inputs_twenty_two_one_gate : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m + 1 := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy
  by_cases hs : y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)
  · exact (size_window_joint n m S C o t y hs hlin hg hu ho hlight hy).trans (Nat.le_succ _)
  have hk3 : y.card = 3 := by omega
  let V := Finset.univ \ y
  have hV : V.card = n-y.card := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y)]
  apply window_refund_22 S C o t y (by omega) hlin hg hu ho hlight hy hk3 V
    (fun i hi _ _ p hp => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hi hp⟩) (by omega) 1
  · apply Nat.add_le_add_right
    apply disjoint_outputs_refunded S C o y _ hlin ho
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact ⟨h.1, by have hsize := h.2.2; omega⟩

theorem num_inputs_twenty_two_extra_refund : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (Finset.univ.filter (fun i =>
    Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card ∧
    y.card+2 ≤ (S i).card)).card < (refunds S C y).card → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  by_cases hs : y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)
  · exact size_window_joint n m S C o t y hs hlin hg hu ho hlight hy
  have hk3 : y.card = 3 := by omega
  let V := Finset.univ \ y
  have hV : V.card = n-y.card := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y)]
  have h := window_refund_22 S C o t y (by omega) hlin hg hu ho hlight hy hk3 V (fun i hi _ _ p hp => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hi hp⟩) (by omega) 0 (by omega)
  rw [Nat.add_zero] at h
  exact h

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997_refund PEqualNP.Outside.L_meta_997_aux

/-- A proper row longer than the light window pays one extra gate if its
output is not AND. In the underpaid case the output is separate from the
private AND gates, and the switch is excluded by an outside singleton. -/
lemma touching_spare {n m k : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (i : Fin m) (t : ℕ) (hk : 2 ≤ k)
    (hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ j : Fin C.gates.length, (C.gates.get j).op = .not → j.val = t)
    (ho : ∀ (j : Fin m) (x : Fin n → Bool), value C x (o j) = decide (∃ p ∈ S j, x p = true))
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k → value C x (n+t) = true)
    (hsize : k < (S i).card) (hproper : ∃ p, p ∉ S i)
    (hop : ¬andAt C n (o i)) : k ≤ ((assigned C (S i)).erase (n+t)).card := by
  classical
  obtain ⟨p,hp⟩ := hproper
  have hz : n+t ∉ assigned C (S i) := by
    intro ha
    apply hp ((Finset.mem_filter.mp ha).2.1 _)
    apply (mem_support C _ _).mpr
    apply hl
    have he : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [he,Finset.card_singleton]
    omega
  rw [Finset.erase_eq_of_notMem hz]
  by_cases h : (assigned C (S i)).card+1 < (S i).card
  · have hand := low_many_private_ands C (S i) (o i) t hk hg hu (ho i) hl h
    have hs : support C (o i) = S i := by
      ext p
      exact (mem_support C _ _).trans (output_singleton S C o ho i p)
    have hoA : o i ∈ assigned C (S i) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Ico.mpr (output_gate_of_card_two S C o ho i (by omega)), by rw [hs]; exact ⟨by rfl,by omega⟩⟩
    have hlt : ((assigned C (S i)).filter (andAt C n)).card < (assigned C (S i)).card := by
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr
        ⟨o i,hoA,fun he => hop (Finset.mem_filter.mp he).2⟩
    omega
  · omega

end PEqualNP.Outside.L_meta_997.Light

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997.Light PEqualNP.Outside.L_meta_997_aux
theorem num_inputs_twenty_two_touching_spare : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∃ i, ¬ Disjoint (S i) y ∧
    min y.card (S i).card ≤ ((assigned C (S i)).erase (n+t)).card) → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  by_cases hs : y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)
  · exact size_window_joint n m S C o t y hs hlin hg hu ho hlight hy
  have hk3 : y.card = 3 := by omega
  let V := Finset.univ \ y
  have hV : V.card = n-y.card := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y)]
  obtain ⟨d,hd,hspare⟩ := hmore
  let bonus (i : Fin m) : ℕ := if i=d then 1 else 0
  have hz : ∀ i, Disjoint (S i) y → bonus i = 0 := by
    intro i hi
    have hn : i ≠ d := fun e => hd (e ▸ hi)
    simp [bonus,hn]
  have hp : ∀ i, ¬ Disjoint (S i) y → min y.card (S i).card + bonus i ≤
      ((assigned C (S i)).erase (n+t)).card+1 := by
    intro i _
    by_cases hi : i=d
    · subst i
      simpa [bonus] using Nat.add_le_add_right hspare 1
    · simpa [bonus,hi] using card_light_erase_switch (S i) C (o i) t (by omega : 2 ≤ y.card) hg hu (ho i) hlight
  have ht := low_budget_with_terminal_bonus C y t S o (by omega : 2 ≤ y.card)
    (Finset.card_pos.mp (by omega)) hg hu hlight hy hlin ho bonus hz hp
  have hterm := ht (by
    intro i hi
    obtain ⟨hund,hd⟩ := Finset.mem_filter.mp hi
    have hshort := (Finset.mem_filter.mp hund).2
    obtain ⟨w,hw,ha,hL,hH,hwz⟩ := terminal_or C y (S i) (o i) t (by omega) hd hg hu (ho i)
      (hlight (fun _ => false) (by simpa using (show 0<y.card by omega))) hy
    exact ⟨w,hw,hwz,ha,hL,hH⟩)
  have hb : ∑ i, bonus i = 1 := by simp [bonus]
  rw [hb] at hterm
  have he : underDisjoint C S y =
      Finset.univ.filter (fun i => Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card) := by
    ext i
    simp [underDisjoint,underpaid,and_comm]
  rw [he] at hterm
  apply window_distinct_credit_bonus S C o t y (by omega) hlin hg hu ho hlight hy hk3 V
    (fun i hi _ _ p hp => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hi hp⟩)
    (by omega) 0 1
  · apply Nat.add_le_add_right
    apply disjoint_outputs_refunded S C o y _ hlin ho
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact ⟨h.1, by have hsize := h.2.2; omega⟩
  · simpa only [Finset.sum_filter,PEqualNP.CircuitLowerBounds.Circuit.size] using hterm

theorem num_inputs_twenty_two_touching_output : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∃ i, ¬ Disjoint (S i) y ∧ y.card < (S i).card ∧
    (∃ p, p ∉ S i) ∧ ¬andAt C n (o i)) → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  by_cases hs : y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)
  · exact size_window_joint n m S C o t y hs hlin hg hu ho hlight hy
  have hk3 : y.card = 3 := by omega
  apply num_inputs_twenty_two_touching_spare n m S C o t y hn hlin hg hu ho hlight hy
  obtain ⟨d,hd,hsize,hproper,hop⟩ := hmore
  refine ⟨d,hd,?_⟩
  rw [min_eq_left hsize.le]
  exact touching_spare S C o d t (by omega) hg hu ho hlight hsize hproper hop

theorem num_inputs_twenty_two_gate_set : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∃ A : Finset ℕ, y.card ≤ A.card ∧ A ⊆ Finset.Ico n (n+C.size) ∧ n+t ∉ A ∧
    (∀ w ∈ A, ∀ i, w ∈ assigned C (S i) → i ∈ underDisjoint C S y ∧ ¬andAt C n w) ∧
    (∀ w ∈ A, ∀ i ∈ underDisjoint C S y, ¬andAt C n w → S i ⊆ support C w →
      PEqualNP.Outside.L_meta_997_aux.Heavy.supp C y w ≠ S i)) → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  by_cases hs : y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)
  · exact size_window_joint n m S C o t y hs hlin hg hu ho hlight hy
  have hk3 : y.card = 3 := by omega
  let V := Finset.univ \ y
  have hV : V.card = n-y.card := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y)]
  obtain ⟨A,hc,ar,az,ap,af⟩ := hmore
  have ht := low_budget_with_gate_set C y t S o (by omega : 2 ≤ y.card)
    (Finset.card_pos.mp (by omega)) hg hu hlight hy hlin ho (fun _ => 0) (fun _ _ => rfl)
    (fun i _ => card_light_erase_switch (S i) C (o i) t (by omega) hg hu (ho i) hlight) A ar az ap af
  have hterm := ht (by
    intro i hi
    obtain ⟨hund,hd⟩ := Finset.mem_filter.mp hi
    have hshort := (Finset.mem_filter.mp hund).2
    obtain ⟨w,hw,ha,hL,hH,hwz⟩ := terminal_or C y (S i) (o i) t (by omega) hd hg hu (ho i)
      (hlight (fun _ => false) (by simpa using (show 0<y.card by omega))) hy
    exact ⟨w,hw,hwz,ha,hL,hH⟩)
  have he : underDisjoint C S y =
      Finset.univ.filter (fun i => Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card) := by
    ext i
    simp [underDisjoint,underpaid,and_comm]
  rw [he] at hterm
  apply window_distinct_credit_bonus S C o t y (by omega) hlin hg hu ho hlight hy hk3 V
    (fun i hi _ _ p hp => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hi hp⟩)
    (by omega) 0 1
  · apply Nat.add_le_add_right
    apply disjoint_outputs_refunded S C o y _ hlin ho
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact ⟨h.1, by have hsize := h.2.2; omega⟩
  · simp only [Finset.sum_const_zero,Nat.add_zero,Finset.sum_filter,PEqualNP.CircuitLowerBounds.Circuit.size] at hterm
    omega

theorem num_inputs_twenty_two_small_support : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (y.card ≤ ((Finset.Ico n (n+C.size)).filter (fun w =>
      w ≠ n+t ∧ (support (n:=n) C w).card ≤ 1)).card) → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  apply num_inputs_twenty_two_gate_set n m S C o t y hn hlin hg hu ho hlight hy
  refine ⟨_,hmore,Finset.filter_subset _ _,fun hw => (Finset.mem_filter.mp hw).2.1 rfl,?_,?_⟩
  · intro w hw i hi
    have h := (Finset.mem_filter.mp hw).2.2
    have hs := (Finset.mem_filter.mp hi).2.2
    omega
  · intro w hw i hi _ hsub
    have h := (Finset.mem_filter.mp hw).2.2
    have hs := Finset.card_le_card hsub
    have hu := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    omega

theorem num_inputs_twenty_two_rigidity : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m) →
    n = 22 ∧ y.card = 3 ∧ ∃ A : Finset ℕ, A.card = 2 ∧ A ⊆ Finset.Ico n (n+t) ∧
      (∀ w ∈ A, support (n:=n) C w = ∅ ∧ value C (fun p => decide (p ∈ y)) w = true) ∧
      ∀ w ∈ Finset.Ico n (n+C.size), w ≠ n+t → w ∉ A →
        (∃ i, w ∈ assigned C (S i) ∧ (i ∈ underDisjoint C S y → andAt C n w)) ∨
        (∃ i ∈ underDisjoint C S y, ¬andAt C n w ∧ S i ⊆ support C w ∧
          PEqualNP.Outside.L_meta_997_aux.Heavy.supp C y w = S i) := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  have hs : ¬(y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)) :=
    fun h => hbad (size_window_joint n m S C o t y h hlin hg hu ho hl hy)
  have hk : y.card = 3 := by omega
  have noSet := fun h => hbad (num_inputs_twenty_two_gate_set n m S C o t y hn hlin hg hu ho hl hy h)
  obtain ⟨A,ac,ar,ad⟩ := guard_hot_gates C t y (by omega : 0<y.card) hg hu hl hy
  have h0 := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have hzr : n+t < n+C.size := by
    by_contra! h
    exact Bool.noConfusion ((missing_value C (fun _ : Fin n => false) _ h).symm.trans h0)
  have inside : A ⊆ Finset.Ico n (n+C.size) := fun w hw =>
    Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1, (Finset.mem_Ico.mp (ar hw)).2.trans hzr⟩
  have az : n+t ∉ A := fun hw => Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar hw)).2
  have ap {w} (hw : w ∈ A) (i) (hi : w ∈ assigned C (S i)) : False := by
    have h := (Finset.mem_filter.mp hi).2.2
    rw [(ad _ hw).1,Finset.card_empty] at h
    omega
  have af {w} (hw : w ∈ A) {i} (hi : i ∈ underDisjoint C S y) (hsub : S i ⊆ support C w) : False := by
    have h := Finset.card_le_card hsub
    rw [(ad _ hw).1,Finset.card_empty] at h
    have hu := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    omega
  have hc : A.card = 2 := by
    by_contra h
    exact noSet ⟨A,by omega,inside,az,fun _ hw i hi => (ap hw i hi).elim,
      fun _ hw _ hi _ hsub => (af hw hi hsub).elim⟩
  refine ⟨by omega,hk,A,hc,ar,ad,?_⟩
  intro w hw hne ha
  by_contra h
  apply noSet
  refine ⟨insert w A,by rw [Finset.card_insert_of_notMem ha]; omega,
    Finset.insert_subset hw inside,by simpa [hne.symm] using az,?_,?_⟩
  · intro v hv i hi
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_contra hno
      apply h
      refine Or.inl ⟨i,hi,?_⟩
      intro hd
      by_contra hand
      exact hno ⟨hd,hand⟩
    · exact (ap hv i hi).elim
  · intro v hv i hi hop hsub heq
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact h (Or.inr ⟨i,hi,hop,hsub,heq⟩)
    · exact af hv hi hsub

theorem num_inputs_twenty_two_prefix : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m) →
    ∀ w ∈ Finset.Ico n (n+t), (support (n:=n) C w).Nonempty →
      ∃ i, w ∈ assigned C (S i) := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,A,_,_,ad,roles⟩ :=
    num_inputs_twenty_two_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
  have h0 := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have ht : t < C.gates.length := by
    by_contra! h
    exact Bool.noConfusion ((missing_value C (fun _ : Fin n => false) _ (by omega : n+C.gates.length ≤ n+t)).symm.trans h0)
  intro w hw hne
  obtain ⟨hwlo,hwlt⟩ := Finset.mem_Ico.mp hw
  have hw' : w ∈ Finset.Ico n (n+C.size) := Finset.mem_Ico.mpr ⟨hwlo,by change w<n+C.gates.length; omega⟩
  have hnA : w ∉ A := fun ha => (Finset.nonempty_iff_ne_empty.mp hne) (ad w ha).1
  rcases roles w hw' (by omega) hnA with ⟨i,hass,_⟩ | ⟨i,hi,_,hsub,he⟩
  · exact ⟨i,hass⟩
  have hinc : support C w ⊆ PEqualNP.Outside.L_meta_997_aux.Heavy.supp C y w := by
    intro p hp
    apply (PEqualNP.Outside.L_meta_997_aux.Heavy.mem_supp C y w p).mpr
    have hon := (mem_support C w p).mp hp
    cases C with
    | mk gs oo =>
      let j : Fin gs.length := ⟨t,ht⟩
      change value ⟨gs,0⟩ (fun v => decide (v=p)) w = true at hon
      change value ⟨gs,0⟩ (fun v => decide (v ∈ y ∨ v=p)) w = true
      rw [prefix_value_eq gs j _ w hwlt] at hon ⊢
      exact value_mono _ (pre_basis gs j hg (fun a h => Fin.ext (hu a h))) _ _
        (fun q h => decide_eq_true (Or.inr (of_decide_eq_true h))) w hon
  rw [he] at hinc
  have hshort := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hh := Finset.card_le_card hsub
  exact ⟨i,Finset.mem_filter.mpr ⟨hw',hinc,by omega⟩⟩

theorem num_inputs_twenty_two_prefix_pairs : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m) →
    ∀ i ∈ underDisjoint C S y, ∀ w < n+t, ((support C w) ∩ S i).card ≤ 1 := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,A,_,_,ad,roles⟩ :=
    num_inputs_twenty_two_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
  have pref := num_inputs_twenty_two_prefix n m S C o t y hn hlin hg hu ho hl hy hbad
  intro i hi
  have hshort := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have hpaid := card_light (S i) C (o i) t hg hu (ho i) hl
  have large : 3 < (S i).card := by omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_contra! hmore
    have hcount := Finset.card_le_card (Finset.inter_subset_left :
      support C w ∩ S i ⊆ support C w)
    have hs : 2 ≤ (support (n:=n) C w).card := by omega
    obtain ⟨lo,up⟩ := support_gate C w hs
    have hnA : w ∉ A := by
      intro ha
      rw [(ad w ha).1,Finset.card_empty] at hs
      omega
    have owner (j) (hsub : support C w ⊆ S j) : j=i := by
      by_contra hn
      have sub : support C w ∩ S i ⊆ S j ∩ S i :=
        fun p hp => Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hp).1,(Finset.mem_inter.mp hp).2⟩
      have := (Finset.card_le_card sub).trans (hlin _ _ hn)
      omega
    obtain ⟨b,hb⟩ := pref w (Finset.mem_Ico.mpr ⟨lo,hw⟩) (Finset.card_pos.mp (by omega))
    have bi := owner b (Finset.mem_filter.mp hb).2.1
    subst b
    have sub := (Finset.mem_filter.mp hb).2.1
    have hidx : w-n < C.gates.length := by change w<n+C.gates.length at up; omega
    let g := C.gates[w-n]
    have gin : g ∈ C.gates := List.getElem_mem _
    obtain ⟨hop,hlen⟩ := hg g gin
    let read (x : Fin n → Bool) (r : ℕ) := if r<w then value C x r else false
    have eval (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
      gate_value C x w lo up
    rcases hop with hand | hor | hnot
    · have hall (p : Fin n) (hp : p ∈ support C w) (r) (hr : r ∈ g.inputs) :
          read (fun v => decide (v=p)) r = true := by
        have hh := (mem_support C w p).mp hp
        rw [eval,hand] at hh
        simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using
          (show ∀ a ∈ g.inputs, read (fun v => decide (v=p)) a = true from by
            simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hh) r hr
      cases he : g.inputs with
      | nil =>
        have allp : ∀ p : Fin n, p ∈ S i := by
          intro p
          apply sub
          apply (mem_support C w p).mpr
          rw [eval,hand,he]
          rfl
        obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<y.card)
        exact Finset.disjoint_left.mp (Finset.mem_filter.mp hi).2 (allp p) hp
      | cons r rs =>
        have hr : r ∈ g.inputs := by simp [he]
        obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(support (n:=n) C w).card)
        have hlt : r<w := by
          by_contra hh
          have := hall p hp r hr
          simp [read,hh] at this
        have hsub : support C w ∩ S i ⊆ support C r ∩ S i := by
          intro q hq
          obtain ⟨hq,hi⟩ := Finset.mem_inter.mp hq
          exact Finset.mem_inter.mpr ⟨(mem_support C r q).mpr (by simpa [read,hlt] using hall q hq r hr),hi⟩
        have := (Finset.card_le_card hsub).trans (ih r hlt (hlt.trans hw))
        omega
    · have noAnd : ¬andAt C n w := by simp [andAt,hidx,show C.gates[w-n].op = .or from hor]
      have full : S i ⊆ support C w := by
        rcases roles w (Finset.mem_Ico.mpr ⟨lo,up⟩) (by omega) hnA with ⟨j,hj,ha⟩ | ⟨j,hj,_,ht,_⟩
        · have eq := owner j (Finset.mem_filter.mp hj).2.1
          subst j
          exact (noAnd (ha hi)).elim
        · have same : j=i := by
            by_contra hji
            have hrow : S j ⊆ S j ∩ S i := fun p hp => Finset.mem_inter.mpr ⟨hp,sub (ht hp)⟩
            have hle := (Finset.card_le_card hrow).trans (hlin _ _ hji)
            have hbig := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
            omega
          exact same ▸ ht
      let P := g.inputs.toFinset.filter (· < w)
      have cardP : P.card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen)
      have cover : S i ⊆ P.biUnion (fun r => support C r ∩ S i) := by
        intro p hp
        have hh := (mem_support C w p).mp (full hp)
        rw [eval,hor] at hh
        obtain ⟨r,hr,hon⟩ : ∃ r ∈ g.inputs, read (fun v => decide (v=p)) r = true := by
          simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hh
        have hlt : r<w := by by_contra h; simp [read,h] at hon
        exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hlt⟩,
          Finset.mem_inter.mpr ⟨(mem_support C r p).mpr (by simpa [read,hlt] using hon),hp⟩⟩
      have cost := Finset.card_biUnion_le_card_mul P (fun r => support C r ∩ S i) 1
        (fun r hr => ih r (Finset.mem_filter.mp hr).2 ((Finset.mem_filter.mp hr).2.trans hw))
      have := Finset.card_le_card cover
      omega
    · have ht := hu (⟨w-n,hidx⟩ : Fin C.gates.length) hnot
      change w-n=t at ht
      omega

theorem num_inputs_twenty_two_high_prefix : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m) →
    ∀ i ∈ underDisjoint C S y, ∀ w < n+t,
      PEqualNP.Outside.L_meta_997_aux.Heavy.supp C y w ⊆ S i →
      (PEqualNP.Outside.L_meta_997_aux.Heavy.supp C y w).card ≤ 1 := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,A,_,_,ad,roles⟩ :=
    num_inputs_twenty_two_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
  have pairs := num_inputs_twenty_two_prefix_pairs n m S C o t y hn hlin hg hu ho hl hy hbad
  have h0 := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have ht : t < C.gates.length := by
    by_contra! h
    exact Bool.noConfusion ((missing_value C (fun _ : Fin n => false) _ (by omega : n+C.gates.length ≤ n+t)).symm.trans h0)
  intro i hi w hw sub
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<y.card)
  have dis := (Finset.mem_filter.mp hi).2
  have cold : value C (fun v => decide (v ∈ y)) w ≠ true := by
    intro hot
    have he : (fun v : Fin n => decide (v ∈ y ∨ v=p)) = (fun v => decide (v ∈ y)) := by
      funext v
      by_cases e : v=p
      · subst v; simp [hp]
      · simp [e]
    exact Finset.disjoint_left.mp dis (sub ((Heavy.mem_supp C y w p).mpr (he.symm ▸ hot))) hp
  by_cases hwlo : w < n
  · let q : Fin n := ⟨w,hwlo⟩
    have hq : q ∉ y := by
      intro h
      apply cold
      exact (input_value C _ q).trans (decide_eq_true h)
    have ss : Heavy.supp C y w ⊆ {q} := by
      intro r hr
      have hh := (Heavy.mem_supp C y w r).mp hr
      change value C _ q.val = true at hh
      rw [input_value] at hh
      exact Finset.mem_singleton.mpr ((of_decide_eq_true hh).resolve_left hq).symm
    simpa using Finset.card_le_card ss
  · have hinc : support C w ⊆ Heavy.supp C y w := by
      intro r hr
      apply (Heavy.mem_supp C y w r).mpr
      have hon := (mem_support C w r).mp hr
      cases C with
      | mk gs oo =>
        let j : Fin gs.length := ⟨t,ht⟩
        change value ⟨gs,0⟩ (fun v => decide (v=r)) w = true at hon
        change value ⟨gs,0⟩ (fun v => decide (v ∈ y ∨ v=r)) w = true
        rw [prefix_value_eq gs j _ w hw] at hon ⊢
        exact value_mono _ (pre_basis gs j hg (fun a h => Fin.ext (hu a h))) _ _
          (fun q h => decide_eq_true (Or.inr (of_decide_eq_true h))) w hon
    have hsmall := pairs i hi w hw
    rw [Finset.inter_eq_left.mpr (hinc.trans sub)] at hsmall
    have rg : w ∈ Finset.Ico n (n+C.size) := Finset.mem_Ico.mpr ⟨by omega,by change w<n+C.gates.length; omega⟩
    rcases roles w rg (by omega) (fun ha => cold (ad w ha).2) with ⟨j,hj,_⟩ | ⟨j,hj,_,hsub,_⟩
    · have hs := (Finset.mem_filter.mp hj).2.2
      omega
    · have hs := Finset.card_le_card hsub
      have hshort := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
      omega

theorem num_inputs_twenty_two_cold_suffix : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m) →
    (∑ i ∈ underDisjoint C S y, ((S i).card-1)) ≤
      ((Finset.Ico (n+t+1) (n+C.size)).filter (fun w =>
        value C (fun p => decide (p ∈ y)) w = false)).card := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,_⟩ := num_inputs_twenty_two_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
  have before_switch := num_inputs_twenty_two_high_prefix n m S C o t y hn hlin hg hu ho hl hy hbad
  have sw := (terminal_switch_closed C y t hg hu
    (hl (fun _ => false) (by simpa using (show 0<y.card by omega))) hy).2
  obtain ⟨D,hlen,hgD,hagree⟩ := Heavy.heavy_model C y t hg hu hy
  let H := underDisjoint C S y
  let G := fun i => Heavy.heavyG C y (S i)
  have pair : (H : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    exact Heavy.heavy_disjoint C y (S i) (S j) (hlin i j hij)
  have cost : (∑ i ∈ H, ((S i).card-1)) ≤ (H.biUnion G).card := by
    rw [Finset.card_biUnion pair]
    apply Finset.sum_le_sum
    intro i hi
    have h := Heavy.heavy_per C D y (S i) (o i) hlen hgD hagree
      (Disjoint.symm (Finset.mem_filter.mp hi).2) (ho i)
    change (S i).card-1 ≤ (Heavy.heavyG C y (S i)).card
    omega
  apply cost.trans (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨i,hi,hgates⟩ := Finset.mem_biUnion.mp hw
  obtain ⟨hr,sub,hs,hcold⟩ := Finset.mem_filter.mp hgates
  have later : n+t < w := by
    by_contra! h
    rcases lt_or_eq_of_le h with hlt | rfl
    · have := before_switch i hi w hlt sub
      omega
    · rw [sw,Finset.card_empty] at hs
      omega
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega,(Finset.mem_Ico.mp hr).2⟩,hcold⟩

end PEqualNP.Outside.L_meta_997.Small
