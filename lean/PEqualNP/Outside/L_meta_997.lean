import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
-- The desk inequality holds for every circuit with at most 25 inputs.
-- It also holds in any dimension when |y| ≤ 2 or n ≤ 7|y|+1, and when
-- |y| ≥ 5 and n ≤ 7|y|+2.
-- When |y|=3, a tight folded projection leaves at most one gate with
-- singleton support. Every regular crossing triple needs the same
-- singleton point and a distinct point of y. This closes the three-row
-- cases at 25 inputs and excludes more profiles at 26 inputs.
-- The four-row case at 25 inputs uses a one-unit-slack projection and
-- an upper-window count of at least thirteen crossing triples.
-- The unrestricted case is open.
-- This file builds on Apache-2.0 code by contributors to brilliant-hq/pequalnp-proofs.
-- L_meta_270.lean, restored by ilyasudakov in PR 805, supplies the small-cut counting argument.
-- L_meta_988.lean, RepoTactics in PR 2015, supplies the sound-wire count on a fixed window.
-- L_meta_1377.lean, psosnin in PR 2757, supplies circuit semantics and the constant-gate replacement.
-- These arguments are adapted here to handle both values of the constrained wire.
-- Source commits are 5c4c77a55bcf447311a2eb7e7a4c05c303856342,
-- 48a1a46a56b8b906a7e15b4f98bbceb16b50e5d2 and 98648e41435898c7dc1fe68d052bc233217cbe7a respectively.

namespace PEqualNP.Outside

namespace L_meta_997.Light
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

abbrev hasAllowedGates (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

abbrev onlyNegAt (C : Circuit) (t : ℕ) : Prop :=
  ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = t

abbrev switchLight {n : ℕ} (C : Circuit) (t k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < k →
    (C.wires (List.ofFn x)).getD (n+t) false = true

abbrev computesRows {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) : Prop :=
  ∀ (i : Fin m) (x : Fin n → Bool),
    (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)

abbrev rowLinearity {n m : ℕ} (S : Fin m → Finset (Fin n)) : Prop :=
  ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1

abbrev rowOutputs {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) : Prop :=
  ∀ i (x : Fin n → Bool), value C x (o i) = decide (∃ p ∈ S i, x p = true)

abbrev lightOnSparse {n : ℕ} (C : Circuit) (t k : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
    value C x (n+t) = true

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
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
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

end L_meta_997.Light


namespace L_meta_997.Light
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
    (hpair : rowLinearity S)
    (hout : rowOutputs C S o)
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

end L_meta_997.Light

namespace L_meta_997.Light
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
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
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

end L_meta_997.Light

namespace L_meta_997.Light
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
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
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

end L_meta_997.Light


namespace L_meta_997_aux.Heavy
open L_meta_997.Light
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
    (hlin : rowLinearity S)
    (houtput : rowOutputs C S o) :
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
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
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
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : rowLinearity S)
    (houtput : rowOutputs C S o) :
    let H := Finset.univ.filter (fun i => Disjoint Y (S i))
    (∑ i ∈ H, ((S i).card - 1)) ≤ (H.biUnion (fun i => heavyG C Y (S i))).card := by
  obtain ⟨D,hlen,hgood,hagree⟩ := heavy_model C Y t hg hu hy
  exact heavy_window C D Y S o hlen hgood hagree hlin houtput

theorem heavy_charge_set {n m : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : rowLinearity S)
    (houtput : rowOutputs C S o) :
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

end L_meta_997_aux.Heavy

namespace L_meta_997_refund
open L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma output_singleton {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (out : rowOutputs C S o)
    (i : Fin m) (p : Fin n) : value C (fun v => decide (v = p)) (o i) = true ↔ p ∈ S i := by
  rw [out]; simp

lemma output_gate_of_card_two {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (o : Fin m → ℕ)
    (out : rowOutputs C S o)
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
    (out : rowOutputs C S o)
    (hcross : rowLinearity S)
    (i j : Fin m) (hc : 2 ≤ (S i).card) (hne : i ≠ j) : o i ≠ o j := by
  intro oe
  have sub : S i ⊆ S i ∩ S j := by
    intro p hp
    have on := (output_singleton S C o out i p).2 hp
    rw [oe] at on
    exact Finset.mem_inter.mpr ⟨hp,(output_singleton S C o out j p).1 on⟩
  have := (Finset.card_le_card sub).trans (hcross i j hne)
  omega

end L_meta_997_refund

namespace L_meta_997_aux

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

end L_meta_997_aux

namespace L_meta_997_aux

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

end L_meta_997_aux
namespace L_meta_997_aux
open PEqualNP.CircuitLowerBounds
open L_meta_997_refund L_meta_997.Light

lemma two_window_with_credits {n m : ℕ} (C : Circuit) (y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
    (hy : (C.wires (List.ofFn (fun p => decide (p ∈ y)))).getD (n+t) false = false)
    (hlin : rowLinearity S)
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
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
    (hy : (C.wires (List.ofFn (fun p => decide (p ∈ y)))).getD (n+t) false = false)
    (hlin : rowLinearity S)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true))
    (hsmall : y.card ≤ 2) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  apply two_window_with_credits C y t S o hg hu hy hlin ho
  have hzero (i : Fin m) : min y.card (S i).card - 2 = 0 := by omega
  simp [hzero]

end L_meta_997_aux

namespace L_meta_997.Small

lemma line_union {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : L_meta_997.Light.rowLinearity S) (I : Finset (Fin m)) :
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

end L_meta_997.Small

namespace L_meta_997.Light

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

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

def unionWire {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w ∧ value C (fun _ : Fin n => false) r = false) ∧
    support (n:=n) C w = P.biUnion (support (n:=n) C)

end L_meta_997.Light



namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem sum_row_weights {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (C : Circuit) (f : Fin m → ℕ)
    (hpair : rowLinearity S)
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

private lemma projection_gate_count {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (z : ℕ) (A : Finset ℕ) (hD : 2 ≤ (S d).card)
    (hpair : rowLinearity S)
    (hzrange : z ∈ Finset.Ico n (n+C.size)) (htz : value C (fun _ : Fin n => false) z=true)
    (hzs : ∀ p : Fin n, p ∈ support C z)
    (hAi : A ⊆ Finset.Ico n (n+C.size)) (hAz : z ∉ A) (hAs : ∀ w ∈ A, support (n:=n) C w=∅)
    (q : ℕ) (hdweight : q ≤ (dormant C (S d)).card+1)
    (f : Fin m → ℕ)
    (hweight : ∀ i, i ≠ d → f i ≤ (assigned C (S i)).card+1) :
    q + (∑ i ∈ Finset.univ.erase d, f i) + A.card+1 ≤ C.gates.length + m := by
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
  let W := insert z (U ∪ G)
  have disA : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro w wa ww
    rcases Finset.mem_insert.mp ww with hz | h
    · exact hAz (hz ▸ wa)
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
        · exact hAi ha
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
  change q + (∑ i ∈ I, f i) + A.card+1 ≤ _
  omega


lemma weighted_exceptional_count {n m k : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ k) (hD : 2 ≤ (S d).card)
    (hpair : rowLinearity S)
    (hg : L_meta_997.Light.hasAllowedGates C)
    (hu : L_meta_997.Light.onlyNegAt C t)
    (hlight : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p : Fin n => x p = true)).card < k →
      value C x (n+t) = true)
    (q : ℕ) (hdweight : q ≤ (dormant C (S d)).card+1)
    (f : Fin m → ℕ)
    (hweight : ∀ i, i ≠ d → f i ≤ (assigned C (S i)).card+1)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false) :
    q + (∑ i ∈ Finset.univ.erase d, f i) + k ≤ C.gates.length + m := by
  classical
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
  obtain ⟨A,hkA,hAi,hAs⟩ := guard_empty_gates C t y (by omega : 0 < k) hg hu hlight hy
  have cnt := projection_gate_count S d C z A hD hpair hzrange htz hzs (fun w hw =>
    Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (hAi hw)).1,(Finset.mem_Ico.mp (hAi hw)).2.trans (Finset.mem_Ico.mp hzrange).2⟩)
    (fun hw => Nat.lt_irrefl z (Finset.mem_Ico.mp (hAi hw)).2) hAs q hdweight f hweight
  omega

end L_meta_997.Light


namespace L_meta_997.Small

/-- Counting row pairs at each input bounds the total incidence in a linear family. -/
lemma weighted_pair_incidence {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (q : ℕ) (V : Finset (Fin n)) (hsub : ∀ i ∈ I, S i ⊆ V)
    (hlin : L_meta_997.Light.rowLinearity S) :
    q * (∑ i ∈ I, (S i).card) ≤ V.card * (q+1).choose 2 + I.card.choose 2 := by
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
  have per (q d : ℕ) : q*d ≤ (q+1).choose 2 + d.choose 2 := by
    induction q generalizing d with
    | zero => simp
    | succ q ih =>
      cases d with
      | zero => simp
      | succ d =>
        have h := ih d
        rw [Nat.choose_succ_succ (q+1) 1,Nat.choose_succ_succ d 1,
          Nat.choose_one_right,Nat.choose_one_right,Nat.succ_mul,Nat.mul_succ]
        simp only [show Nat.succ 1 = 2 from rfl]
        omega
  have hsum := Finset.sum_le_sum (s:=V) (fun p _ => per q (N p).card)
  rw [← Finset.mul_sum,incid,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at hsum
  omega

lemma pair_incidence {n m : ℕ} (S : Fin m → Finset (Fin n)) (I : Finset (Fin m))
    (V : Finset (Fin n)) (hsub : ∀ i ∈ I, S i ⊆ V)
    (hlin : L_meta_997.Light.rowLinearity S) :
    2 * (∑ i ∈ I, (S i).card) ≤ 3 * V.card + I.card.choose 2 := by
  simpa [Nat.choose,Nat.mul_comm] using weighted_pair_incidence S I 2 V hsub hlin

end L_meta_997.Small


open L_meta_997.Light (hasAllowedGates onlyNegAt switchLight computesRows refunds)


namespace L_meta_997.Light

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

end L_meta_997.Light

namespace L_meta_997.Light
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

end L_meta_997.Light

namespace L_meta_997.Light
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

end L_meta_997.Light

namespace L_meta_997.Light
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

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma low_sharp_private_or_extra {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
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

end L_meta_997.Light






namespace L_meta_997.Light
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
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
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

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem card_light_erase_switch {n k : ℕ} (T : Finset (Fin n)) (C : Circuit) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
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

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

private lemma sameFilter {α : Type*} (p : α → Prop) (s : Finset α) (d e : DecidablePred p) :
    @Finset.filter α p d s = @Finset.filter α p e s := by
  have h : d = e := Subsingleton.elim _ _
  cases h
  rfl

lemma low_many_private_ands {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ)
    (hk : 2 ≤ k)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
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

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

private theorem terminal_switch_closed {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hl : L_meta_997.Light.value C (fun _ : Fin n => false) (n+t) = true)
    (hy : L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false) :
    n+t ∈ Finset.Ico n (n+C.size) ∧ Heavy.supp C Y (n+t) = ∅ := by
  classical
  have hb : t < C.gates.length := by
    by_contra! ht
    have hf := L_meta_997.Light.missing_value C (fun _ : Fin n => false) (n+t)
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
    have bad := L_meta_997.Light.value_mono ⟨gs,oo⟩ hm (fun _ : Fin n => false) (fun p => decide (p ∈ Y)) (by simp) (n+t) hl
    exact Bool.noConfusion (hy.symm.trans bad)
  have hs := L_meta_997.Light.pre_basis gs j hg (fun i hi => Fin.ext (hu i hi))
  have notval := L_meta_997.Light.not_value_prefix (n:=n) gs j hj
  change L_meta_997.Light.value ⟨gs,0⟩ (fun p : Fin n => decide (p ∈ Y)) (n+j.val) = false at hy
  rw [notval] at hy
  have hbase : L_meta_997.Light.value ⟨gs.take j.val,0⟩ (fun p => decide (p ∈ Y))
      ((gs.get j).inputs.headD (n+j.val)) = true := by simpa using hy
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hnow := (Heavy.mem_supp _ _ _ _).mp hp
  change L_meta_997.Light.value ⟨gs,0⟩ (fun v => decide (v ∈ Y ∨ v = p)) (n+j.val) = true at hnow
  rw [notval] at hnow
  have hhigh := L_meta_997.Light.value_mono ⟨gs.take j.val,0⟩ hs (fun q => decide (q ∈ Y))
    (fun q => decide (q ∈ Y ∨ q = p)) (fun q hq => decide_eq_true (Or.inl (of_decide_eq_true hq))) _ hbase
  rw [hhigh] at hnow
  contradiction

/-- A disjoint output row has an actual OR with its exact high signature,
and all of its row's points already lie in this gate's low signature. -/
lemma terminal_or_ordered {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (o t : ℕ)
    (hcard : 2 ≤ T.card) (hdis : Disjoint T Y)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlzero : value C (fun _ : Fin n => false) (n+t) = true)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false) :
    ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ ¬ andAt C n w ∧ T ⊆ support C w ∧
      Heavy.supp C Y w = T ∧ w ≠ n+t ∧ value C (fun p => decide (p ∉ T)) w = false ∧ w ≤ o := by
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
      Heavy.supp C Y w = T ∧ w ≠ n+t ∧ value C z w = false ∧ w ≤ o
  have descend (w : ℕ) (hl : T ⊆ support C w) (hh : ∀ p ∈ T, value C (fire p) w = true)
      (hz : value C z w = false) (wo : w ≤ o) : result := by
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
        · exact hrw.le.trans wo
      · refine ⟨w,Finset.mem_Ico.mpr ⟨lo,hi⟩,?_,hl,?_,hne,hz,wo⟩
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
            have ht : L_meta_997.Light.value D (fire p) w = true := (hagree (fire p) (above p) w).trans hp
            have hr := L_meta_997.Light.value_mono D hgood (fire p) z hle w ht
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
  · exact Nat.le_refl _


lemma terminal_or {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (o t : ℕ)
    (hcard : 2 ≤ T.card) (hdis : Disjoint T Y)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hlzero : value C (fun _ : Fin n => false) (n+t) = true)
    (hy : value C (fun p => decide (p ∈ Y)) (n+t) = false) :
    ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ ¬ andAt C n w ∧ T ⊆ support C w ∧
      Heavy.supp C Y w = T ∧ w ≠ n+t := by
  obtain ⟨w,hw,op,lo,hi,hne,_,_⟩ :=
    terminal_or_ordered C Y T o t hcard hdis hg hu hout hlzero hy
  exact ⟨w,hw,op,lo,hi,hne⟩

end L_meta_997.Light

namespace L_meta_997_aux
open PEqualNP.CircuitLowerBounds L_meta_997

def underpaid {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun i => (Light.assigned C (S i)).card+1 < (S i).card

abbrev opAnd (C : Circuit) (n w : ℕ) : Prop := Light.andAt C n w
end L_meta_997_aux

namespace L_meta_997_aux
open PEqualNP.CircuitLowerBounds L_meta_997

def underDisjoint {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) :=
  (underpaid C S).filter fun i => Disjoint (S i) Y

theorem low_budget_with_qualified_gate_set {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      L_meta_997.Light.value C x (n+t) = true)
    (_hy : L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : L_meta_997.Light.rowLinearity S)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (bonus : Fin m → ℕ)
    (hb : ∀ i, Disjoint (S i) Y → bonus i = 0)
    (hp : ∀ i, ¬Disjoint (S i) Y → min k (S i).card + bonus i ≤
      ((Light.assigned C (S i)).erase (n+t)).card+1)
    (A : Finset ℕ) (ar : A ⊆ Finset.Ico n (n+C.size))
    (az : n+t ∉ A)
    (ap : ∀ w ∈ A, ∀ i, w ∈ Light.assigned C (S i) →
      i ∈ underDisjoint C S Y ∧ ¬opAnd C n w)
    (qualifies : ℕ → Fin m → Prop)
    (af : ∀ w ∈ A, ∀ i ∈ underDisjoint C S Y, ¬opAnd C n w →
      S i ⊆ Light.support C w →
      qualifies w i → Heavy.supp C Y w ≠ S i)
    (terminal : ∀ i ∈ underDisjoint C S Y, ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ w ≠ n+t ∧
      ¬opAnd C n w ∧ S i ⊆ Light.support C w ∧ Heavy.supp C Y w = S i ∧
      qualifies w i) :
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
      have eq : S i.val = S j.val := (hf i).2.2.2.2.1.symm.trans (he ▸ (hf j).2.2.2.2.1)
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
    have hf := L_meta_997.Light.missing_value C (fun _ : Fin n => false) z hbad
    exact Bool.noConfusion (hf.symm.trans h0)
  have dA : Disjoint A (insert z (F ∪ P)) := by
    refine Finset.disjoint_left.mpr ?_
    intro w ha hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact az ha
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
      exact af _ ha i i.property (hf i).2.2.1 (hf i).2.2.2.1 (hf i).2.2.2.2.2 (hf i).2.2.2.2.1
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


theorem low_budget_with_gate_set {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      L_meta_997.Light.value C x (n+t) = true)
    (_hy : L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : L_meta_997.Light.rowLinearity S)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
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
  apply low_budget_with_qualified_gate_set C Y t S o hk hY hg hu hl _hy hlin ho bonus hb hp A ar az ap
    (fun _ _ => True)
  · intro w hw i hi op support _ sig
    exact af w hw i hi op support sig
  · intro i hi
    obtain ⟨w,wr,wz,op,support,sig⟩ := terminal i hi
    exact ⟨w,wr,wz,op,support,sig,True.intro⟩

theorem low_budget_with_ordered_gate_set {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      L_meta_997.Light.value C x (n+t) = true)
    (_hy : L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : L_meta_997.Light.rowLinearity S)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (bonus : Fin m → ℕ)
    (hb : ∀ i, Disjoint (S i) Y → bonus i = 0)
    (hp : ∀ i, ¬Disjoint (S i) Y → min k (S i).card + bonus i ≤
      ((Light.assigned C (S i)).erase (n+t)).card+1)
    (A : Finset ℕ) (ar : A ⊆ Finset.Ico n (n+C.size))
    (az : n+t ∉ A)
    (ap : ∀ w ∈ A, ∀ i, w ∈ Light.assigned C (S i) →
      i ∈ underDisjoint C S Y ∧ ¬opAnd C n w)
    (af : ∀ w ∈ A, ∀ i ∈ underDisjoint C S Y, ¬opAnd C n w →
      S i ⊆ Light.support C w →
      Light.value C (fun p => decide (p ∉ S i)) w = false → w ≤ o i → Heavy.supp C Y w ≠ S i)
    (terminal : ∀ i ∈ underDisjoint C S Y, ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ w ≠ n+t ∧
      ¬opAnd C n w ∧ S i ⊆ Light.support C w ∧ Heavy.supp C Y w = S i ∧
      Light.value C (fun p => decide (p ∉ S i)) w = false ∧ w ≤ o i) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min k (S i).card) + (∑ i, bonus i) + (A.card+1) ≤
      C.size + m + ∑ i ∈ underDisjoint C S Y, ((S i).card-(k+1)) := by
  refine low_budget_with_qualified_gate_set C Y t S o hk hY hg hu hl _hy hlin ho bonus hb hp A ar az ap
    (fun w i => Light.value C (fun p => decide (p ∉ S i)) w = false ∧ w ≤ o i) ?_ terminal
  intro w hw i hi op support extra sig
  exact af w hw i hi op support extra.1 extra.2 sig

theorem low_budget_with_terminal_bonus {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      L_meta_997.Light.value C x (n+t) = true)
    (hy : L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : L_meta_997.Light.rowLinearity S)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
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
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      L_meta_997.Light.value C x (n+t) = true)
    (hy : L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : L_meta_997.Light.rowLinearity S)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (terminal : ∀ i ∈ underDisjoint C S Y, ∃ w, w ∈ Finset.Ico n (n+C.size) ∧ w ≠ n+t ∧
      ¬opAnd C n w ∧ S i ⊆ Light.support C w ∧ Heavy.supp C Y w = S i) :
    (∑ i, if Disjoint (S i) Y then (S i).card else min k (S i).card) + k ≤
      C.size + m + ∑ i ∈ underDisjoint C S Y, ((S i).card-(k+1)) := by
  simpa using low_budget_with_terminal_bonus C Y t S o hk hY hg hu hl hy hlin ho (fun _ => 0)
    (fun _ _ => rfl) (fun i _ => Light.card_light_erase_switch (S i) C (o i) t hk hg hu (ho i) hl) terminal
end L_meta_997_aux

namespace L_meta_997_aux
open PEqualNP.CircuitLowerBounds L_meta_997

theorem disjoint_terminal_deficit {n m k : ℕ} (C : Circuit) (Y : Finset (Fin n)) (t : ℕ)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (hk : 2 ≤ k) (hY : Y.Nonempty)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      L_meta_997.Light.value C x (n+t) = true)
    (hy : L_meta_997.Light.value C (fun p => decide (p ∈ Y)) (n+t) = false)
    (hlin : L_meta_997.Light.rowLinearity S)
    (ho : ∀ (i : Fin m) (x : Fin n → Bool), L_meta_997.Light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
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

end L_meta_997_aux

namespace L_meta_997.Small

lemma quota_geometry {n m : ℕ} (S : Fin m → Finset (Fin n)) (B : Finset (Fin m))
    (k : ℕ) (V : Finset (Fin n)) (hk : 3 ≤ k) (hsize : V.card ≤ 6*k+1 ∧ V.card+3 ≤ 7*k)
    (hb : B.Nonempty) (hsub : ∀ i ∈ B, S i ⊆ V) (hbig : ∀ i ∈ B, k+2 ≤ (S i).card)
    (hlin : L_meta_997.Light.rowLinearity S) :
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

end L_meta_997.Small

namespace L_meta_997.Small

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

end L_meta_997.Small

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma weak_disjoint_projection {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card) (hD : 2 ≤ (S d).card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : rowOutputs C S o)
    (hlight : lightOnSparse (n:=n) C t y.card)
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

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997.Small

lemma window_terminal_geometry {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : rowOutputs C S o)
    (hlight : lightOnSparse (n:=n) C t y.card)
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

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

lemma window_joint_pool {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : rowOutputs C S o)
    (hlight : lightOnSparse (n:=n) C t y.card)
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
  have ht := L_meta_997_aux.disjoint_terminal_deficit C y t S o hk
    (Finset.card_pos.mp (by omega)) hg hu hlight hy hpair hout
  have he : L_meta_997_aux.underDisjoint C S y =
      Finset.univ.filter (fun i => Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card) := by
    ext i
    simp [L_meta_997_aux.underDisjoint,L_meta_997_aux.underpaid,and_comm]
  rw [he] at ht
  simpa only [Finset.sum_filter,Circuit.size] using ht

end L_meta_997.Light

namespace L_meta_997.Small
open L_meta_997.Light

theorem size_window_joint : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by

  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy
  by_cases hk : y.card ≤ 2
  · exact L_meta_997_aux.two_window_of_card_le_two C y t S o hg hu hy hlin ho hk
  let V := Finset.univ \ y
  have hV : V.card = n-y.card := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y)]
  have hkN : y.card ≤ n := by simpa using Finset.card_le_univ y
  have hb := hn.resolve_left hk
  apply window_joint_pool S C o t y (by omega) hlin hg hu ho hlight hy (by omega) V
  · intro i hi _ _ p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp hi hp⟩
  · omega

end L_meta_997.Small



namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997.Small
/-- The two counting bounds needed for witness size three. Only the row
sizes enter after selecting the underpaid disjoint rows of size at least five. -/
def threeRowQuota {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit) (y : Finset (Fin n)) : Prop :=
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
  B.Nonempty → ∃ d ∈ B, (∑ i ∈ B, (S i).card) ≤ B.card*4+(S d).card+2 ∨
    (∑ i ∈ B, (S i).card) ≤ B.card*5+4

lemma window_quota_credit {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : rowOutputs C S o)
    (hlight : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hk3 : y.card = 3)
    (hq : threeRowQuota S C y) (slack : ℕ) (bonus : ℕ)
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
  obtain ⟨d,hd,hquota⟩ := hq hn
  change (∑ i ∈ B, (S i).card) ≤ B.card*4+(S d).card+2 ∨
    (∑ i ∈ B, (S i).card) ≤ B.card*5+4 at hquota
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
end L_meta_997.Light
namespace L_meta_997.Small
open L_meta_997.Light
theorem three_window_extra_refund : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (Finset.univ.filter (fun i =>
    Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card ∧
    y.card+2 ≤ (S i).card)).card < (refunds S C y).card → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  obtain ⟨hk3,hquota⟩ := hn
  apply window_quota_credit S C o t y (by omega) hlin hg hu ho hlight hy hk3 hquota 0 0 (by omega)
  have ht := L_meta_997_aux.disjoint_terminal_deficit C y t S o (by omega : 2 ≤ y.card)
    (Finset.card_pos.mp (by omega)) hg hu hlight hy hlin ho
  have he : L_meta_997_aux.underDisjoint C S y =
      Finset.univ.filter (fun i => Disjoint (S i) y ∧ (assigned C (S i)).card+1 < (S i).card) := by
    ext i
    simp [L_meta_997_aux.underDisjoint,L_meta_997_aux.underpaid,and_comm]
  rw [he] at ht
  simpa only [Finset.sum_filter,PEqualNP.CircuitLowerBounds.Circuit.size,Nat.add_zero] using ht


end L_meta_997.Small


namespace L_meta_997.Small
open L_meta_997.Light L_meta_997_aux
theorem three_window_touching_spare : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∃ i, ¬ Disjoint (S i) y ∧
    min y.card (S i).card ≤ ((assigned C (S i)).erase (n+t)).card) → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  obtain ⟨hk3,hquota⟩ := hn
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
  apply window_quota_credit S C o t y (by omega) hlin hg hu ho hlight hy hk3 hquota 0 1
  · apply Nat.add_le_add_right
    apply disjoint_outputs_refunded S C o y _ hlin ho
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact ⟨h.1, by have hsize := h.2.2; omega⟩
  · simpa only [Finset.sum_filter,PEqualNP.CircuitLowerBounds.Circuit.size] using hterm


theorem three_window_gate_set : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∃ A : Finset ℕ, y.card ≤ A.card ∧ A ⊆ Finset.Ico n (n+C.size) ∧ n+t ∉ A ∧
    (∀ w ∈ A, ∀ i, w ∈ assigned C (S i) → i ∈ underDisjoint C S y ∧ ¬andAt C n w) ∧
    (∀ w ∈ A, ∀ i ∈ underDisjoint C S y, ¬andAt C n w → S i ⊆ support C w →
      L_meta_997_aux.Heavy.supp C y w ≠ S i)) → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy hmore
  obtain ⟨hk3,hquota⟩ := hn
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
  apply window_quota_credit S C o t y (by omega) hlin hg hu ho hlight hy hk3 hquota 0 1
  · apply Nat.add_le_add_right
    apply disjoint_outputs_refunded S C o y _ hlin ho
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact ⟨h.1, by have hsize := h.2.2; omega⟩
  · simp only [Finset.sum_const_zero,Nat.add_zero,Finset.sum_filter,PEqualNP.CircuitLowerBounds.Circuit.size] at hterm
    omega


theorem three_window_rigidity : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m) →
    22 ≤ n ∧ y.card = 3 ∧ ∃ A : Finset ℕ, A.card = 2 ∧ A ⊆ Finset.Ico n (n+t) ∧
      (∀ w ∈ A, support (n:=n) C w = ∅ ∧ value C (fun p => decide (p ∈ y)) w = true) ∧
      ∀ w ∈ Finset.Ico n (n+C.size), w ≠ n+t → w ∉ A →
        (∃ i, w ∈ assigned C (S i) ∧ (i ∈ underDisjoint C S y → andAt C n w)) ∨
        (∃ i ∈ underDisjoint C S y, ¬andAt C n w ∧ S i ⊆ support C w ∧
          L_meta_997_aux.Heavy.supp C y w = S i) := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  have hs : ¬(y.card ≤ 2 ∨ (n ≤ 7*y.card+1 ∧ n+3 ≤ 8*y.card)) :=
    fun h => hbad (size_window_joint n m S C o t y h hlin hg hu ho hl hy)
  have hk : y.card = 3 := hn.1
  have noSet := fun h => hbad (three_window_gate_set n m S C o t y hn hlin hg hu ho hl hy h)
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


theorem three_window_prefix : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m) →
    ∀ w ∈ Finset.Ico n (n+t), (support (n:=n) C w).Nonempty →
      ∃ i, w ∈ assigned C (S i) := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,A,_,_,ad,roles⟩ :=
    three_window_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
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
  have hinc : support C w ⊆ L_meta_997_aux.Heavy.supp C y w := by
    intro p hp
    apply (L_meta_997_aux.Heavy.mem_supp C y w p).mpr
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


theorem three_window_prefix_pairs : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m) →
    ∀ i ∈ underDisjoint C S y, ∀ w < n+t, ((support C w) ∩ S i).card ≤ 1 := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,A,_,_,ad,roles⟩ :=
    three_window_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
  have pref := three_window_prefix n m S C o t y hn hlin hg hu ho hl hy hbad
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


theorem three_window_high_prefix : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m) →
    ∀ i ∈ underDisjoint C S y, ∀ w < n+t,
      L_meta_997_aux.Heavy.supp C y w ⊆ S i →
      (L_meta_997_aux.Heavy.supp C y w).card ≤ 1 := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,A,_,_,ad,roles⟩ :=
    three_window_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
  have pairs := three_window_prefix_pairs n m S C o t y hn hlin hg hu ho hl hy hbad
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


theorem three_window_first_pair : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m) →
    ∃ w r : ℕ, n+t < r ∧ r < w ∧
      (∃ g ∈ C.gates[w-n]?, g.op = .or ∧
        (g.inputs = [n+t,r] ∨ g.inputs = [r,n+t])) ∧
      support (n:=n) C w = Finset.univ ∧
      (∃ j ∈ underDisjoint C S y, Heavy.supp C y r = S j ∧ Heavy.supp C y w = S j) ∧
      (∃ b, b ∉ underDisjoint C S y ∧ r ∈ assigned C (S b)) ∧
      (∀ v < w, v ≠ n+t → ∀ j ∈ underDisjoint C S y, (support C v ∩ S j).card ≤ 1) := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy hbad
  obtain ⟨_,hk,A,_,ar,ad,roles⟩ := three_window_rigidity n m S C o t y hn hlin hg hu ho hl hy hbad
  let D := underDisjoint C S y
  have large {i} (hi : i ∈ D) : 3 < (S i).card := by
    have hshort := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
    have hpaid := card_light (S i) C (o i) t hg hu (ho i) hl
    omega
  have neD : D.Nonempty := by
    by_contra hh
    have emp := Finset.not_nonempty_iff_eq_empty.mp hh
    have h := disjoint_terminal_deficit C y t S o (by omega : 2 ≤ y.card)
      (Finset.card_pos.mp (by omega)) hg hu hl hy hlin ho
    change _ ≤ C.size + m + ∑ i ∈ D, _ at h
    rw [emp,Finset.sum_empty] at h
    apply hbad
    change _ ≤ C.size + (refunds S C y).card + m
    omega
  have sw0 := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have swH := (terminal_switch_closed C y t hg hu sw0 hy).2
  have swL (p : Fin n) : value C (fun q => decide (q=p)) (n+t) = true := by
    apply hl
    have h : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [h,Finset.card_singleton]; omega
  let hit (v : ℕ) := v ≠ n+t ∧ ∃ i ∈ D, 2 ≤ (support C v ∩ S i).card
  have existsHit : ∃ v, hit v := by
    obtain ⟨i,hi⟩ := neD
    have hs : support C (o i) = S i := by ext p; exact (mem_support C _ _).trans (L_meta_997_refund.output_singleton S C o ho i p)
    refine ⟨o i,?_,i,hi,?_⟩
    · intro e
      rw [← e,ho] at sw0
      simp at sw0
    · rw [hs,Finset.inter_self]; have := large hi; omega
  let w := Nat.find existsHit
  obtain ⟨wn,i,hi,hitw⟩ := (show hit w from Nat.find_spec existsHit)
  change 2 ≤ (support C w ∩ S i).card at hitw
  change w ≠ n+t at wn
  have early (v) (hv : v<w) (hn : v ≠ n+t) (j) (hj : j ∈ D) :
      (support C v ∩ S j).card ≤ 1 := by
    by_contra! h
    exact Nat.find_min existsHit hv ⟨hn,j,hj,by omega⟩
  have pre := three_window_prefix_pairs n m S C o t y hn hlin hg hu ho hl hy hbad
  have after : n+t < w := by
    by_contra! h
    have := pre i hi w (lt_of_le_of_ne h wn)
    omega
  have sc := Finset.card_le_card (Finset.inter_subset_left : support C w ∩ S i ⊆ support C w)
  obtain ⟨lo,up⟩ := support_gate C w (by omega : 2 ≤ (support (n:=n) C w).card)
  have idx : w-n < C.gates.length := by change w<n+C.gates.length at up; omega
  let g := C.gates[w-n]
  have gsome : C.gates[w-n]? = some g := by simp [g,idx]
  obtain ⟨ops,len⟩ := hg g (List.getElem_mem _)
  let read (x : Fin n → Bool) (v : ℕ) := if v<w then value C x v else false
  have eval (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x w lo up
  have wroles := roles w (Finset.mem_Ico.mpr ⟨lo,up⟩) wn
    (fun ha => (Nat.lt_asymm after) (Finset.mem_Ico.mp (ar ha)).2)
  have own {b} (hb : w ∈ assigned C (S b)) : b=i := by
    by_contra h
    have sub : support C w ∩ S i ⊆ S b ∩ S i := fun p hp =>
      Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hb).2.1 (Finset.mem_inter.mp hp).1,(Finset.mem_inter.mp hp).2⟩
    have := (Finset.card_le_card sub).trans (hlin b i h)
    omega
  have hor : g.op = .or := by
    rcases ops with hand | hor | hnot
    · have andw : andAt C n w := by simp [andAt,gsome,hand]
      obtain ⟨b,hb,_⟩ := wroles.resolve_right (fun ⟨_,_,ha,_,_⟩ => ha andw)
      have eq := own hb
      subst b
      have hall (p : Fin n) : p ∈ support C w ↔ ∀ r ∈ g.inputs, read (fun q => decide (q=p)) r = true := by
        rw [mem_support,eval,hand]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      have same (r) (hr : r ∈ g.inputs) : r=n+t := by
        by_contra hne
        obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(support (n:=n) C w).card)
        have hon := (hall p).mp hp r hr
        have lt : r<w := by by_contra h; simp [read,h] at hon
        have sub : support C w ∩ S i ⊆ support C r ∩ S i := by
          intro q hq
          obtain ⟨hq,hs⟩ := Finset.mem_inter.mp hq
          exact Finset.mem_inter.mpr ⟨(mem_support C r q).mpr (by simpa [read,lt] using (hall q).mp hq r hr), hs⟩
        have := (Finset.card_le_card sub).trans (early r lt hne i hi)
        omega
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<y.card)
      have hpw := (hall p).mpr (fun r hr => by rw [same r hr]; simpa [read,after] using swL p)
      exact (Finset.disjoint_left.mp (Finset.mem_filter.mp hi).2 ((Finset.mem_filter.mp hb).2.1 hpw) hp).elim
    · exact hor
    · have h := hu ⟨w-n,idx⟩ hnot
      change w-n=t at h
      omega
  have notAnd : ¬andAt C n w := by simp [andAt,gsome,hor]
  obtain ⟨j,hj,_,sub,high⟩ := wroles.resolve_left (fun ⟨b,hb,ha⟩ => notAnd (ha ((own hb).symm ▸ hi)))
  have anyOn (x : Fin n → Bool) : value C x w = true ↔ ∃ v ∈ g.inputs, read x v = true := by
    rw [eval,hor]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
  have member : n+t ∈ g.inputs := by
    by_contra h
    let P := g.inputs.toFinset.filter (· < w)
    have cardP : P.card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans len)
    have cover : S j ⊆ P.biUnion (fun r => support C r ∩ S j) := by
      intro p hp
      obtain ⟨r,hr,hron⟩ := (anyOn _).mp ((mem_support C w p).mp (sub hp))
      have lt : r<w := by by_contra hh; simp [read,hh] at hron
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,lt⟩,
        Finset.mem_inter.mpr ⟨(mem_support C r p).mpr (by simpa [read,lt] using hron),hp⟩⟩
    have c := Finset.card_biUnion_le_card_mul P (fun r => support C r ∩ S j) 1 (fun r hr =>
      early r (Finset.mem_filter.mp hr).2 (fun he => h (he ▸ List.mem_toFinset.mp (Finset.mem_filter.mp hr).1)) j hj)
    have := Finset.card_le_card cover
    have := large hj
    omega
  have allL : support (n:=n) C w = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    exact (mem_support C w p).mpr ((anyOn _).mpr ⟨_,member,by simpa [read,after] using swL p⟩)
  let fire (p : Fin n) (v : Fin n) := decide (v ∈ y ∨ v=p)
  have off (p : Fin n) : value C (fire p) (n+t) ≠ true := by
    intro h
    have hp := (Heavy.mem_supp C y (n+t) p).mpr h
    simp [swH] at hp
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0<(S j).card by have := large hj; omega)
  obtain ⟨r,hr,hon⟩ := (anyOn (fire p)).mp ((Heavy.mem_supp C y w p).mp (high.symm ▸ hp))
  have rlt : r<w := by by_contra h; simp [read,h] at hon
  have rne : r ≠ n+t := by intro he; exact off p (by simpa [read,he,after] using hon)
  have shape : g.inputs = [n+t,r] ∨ g.inputs = [r,n+t] := by
    rcases hlist : g.inputs with _ | ⟨a,tail⟩
    · simp [hlist] at hr
    · rcases tail with _ | ⟨b,rest⟩
      · simp [hlist] at member hr
        exact (rne (hr.trans member.symm)).elim
      · have hem : rest = [] := by
          apply List.length_eq_zero_iff.mp
          have hh : (a :: b :: rest).length ≤ 2 := hlist ▸ len
          simpa using hh
        subst rest
        simp [hlist] at member hr
        rcases member with ha | hb <;> rcases hr with hc | hd <;> simp_all
  have rh : Heavy.supp C y r = S j := by
    rw [← high]
    ext q
    rw [Heavy.mem_supp,Heavy.mem_supp,anyOn]
    change value C (fire q) r = true ↔ ∃ v ∈ g.inputs, read (fire q) v = true
    rcases shape with he | he <;> simp [he,read,after,rlt,off]
  have ra : n+t < r := by
    by_contra! h
    have c := three_window_high_prefix n m S C o t y hn hlin hg hu ho hl hy hbad
      j hj r (lt_of_le_of_ne h rne) (by rw [rh])
    rw [rh] at c
    have := large hj
    omega
  have rrange : r ∈ Finset.Ico n (n+C.size) := Finset.mem_Ico.mpr ⟨by omega,rlt.trans up⟩
  have rr := roles r rrange rne (fun ha => (Nat.lt_asymm ra) (Finset.mem_Ico.mp (ar ha)).2)
  have exc {b} (hb : b ∈ D) (sub : S b ⊆ support C r) : False := by
    have h := early r rlt rne b hb
    rw [Finset.inter_eq_right.mpr sub] at h
    have := large hb
    omega
  obtain ⟨b,hb,_⟩ := rr.resolve_right (fun ⟨b,hb,_,sub,_⟩ => exc hb sub)
  have hnb : b ∉ D := by
    intro h
    have hc := early r rlt rne b h
    rw [Finset.inter_eq_left.mpr (Finset.mem_filter.mp hb).2.1] at hc
    have := (Finset.mem_filter.mp hb).2.2
    omega
  exact ⟨w,r,ra,rlt,⟨g,by simp [gsome],hor,shape⟩,allL,⟨j,hj,rh,high⟩,⟨b,hnb,hb⟩,early⟩


end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

private lemma two_distinct_inputs {a b : ℕ} (l : List ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hne : a ≠ b) (hlen : l.length ≤ 2) : l = [a,b] ∨ l = [b,a] := by
  rcases l with _ | ⟨c,tail⟩
  · simp at ha
  · rcases tail with _ | ⟨d,rest⟩
    · simp at ha hb; exact (hne (ha.trans hb.symm)).elim
    · have e : rest = [] := by apply List.length_eq_zero_iff.mp; simpa using hlen
      subst rest
      simp at ha hb
      rcases ha with h | h <;> rcases hb with h' | h' <;> simp_all

/-- Stop at a gate after the switch and the output. All light-window charges
for this row can be taken strictly before the stopping gate. -/
private lemma before_output_charge {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t v : ℕ)
    (j : Fin C.gates.length) (hj : n+j.val=v) (ho : o<v) (hz : n+t<v)
    (k : ℕ) (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (n+t) = true) (hk : 2 ≤ k) :
    min k T.card ≤ (((assigned C T).erase (n+t)).filter (· < v)).card+1 := by
  classical
  cases C with
  | mk gs oo =>
    let P : Circuit := ⟨gs.take j.val,0⟩
    have agree (x : Fin n → Bool) (q : ℕ) (hq : q<v) :
        value ⟨gs,oo⟩ x q = value P x q := prefix_value_eq gs j x q (hj ▸ hq)
    have gh : ∀ g ∈ P.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 :=
      fun g hm => hg g (List.mem_of_mem_take hm)
    have uniq (i : Fin P.gates.length) (hi : (P.gates.get i).op = .not) : i.val=t := by
      have il : i.val < j.val := by simpa [P,List.length_take,Nat.min_eq_left j.isLt.le] using i.isLt
      let a : Fin gs.length := ⟨i.val,il.trans j.isLt⟩
      exact hu a (by simpa [P,a,List.get_eq_getElem] using hi)
    have h := card_light_erase_switch T P o t hk gh uniq
      (fun x => (agree x o ho).symm.trans (hout x))
      (fun x hx => (agree x _ hz).symm.trans (hl x hx))
    apply h.trans (Nat.add_le_add_right (Finset.card_le_card ?_) 1)
    intro u hm
    obtain ⟨hne,hh⟩ := Finset.mem_erase.mp hm
    obtain ⟨hr,hs,hc⟩ := Finset.mem_filter.mp hh
    have lr := Finset.mem_Ico.mp hr
    have ult : u<v := by
      have e : P.size=j.val := by simp [P,Circuit.size,List.length_take]
      rw [e,hj] at lr
      exact lr.2
    have es : support (n:=n) P u = support ⟨gs,oo⟩ u := by
      ext p
      rw [mem_support,mem_support,agree _ _ ult]
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne,Finset.mem_filter.mpr ⟨?_,es ▸ hs,es ▸ hc⟩⟩,ult⟩
    exact Finset.mem_Ico.mpr ⟨lr.1,by change u<n+gs.length; have hjj : j.val < gs.length := j.isLt; omega⟩

set_option maxHeartbeats 1400000 in
theorem three_window_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card = 3 ∧ threeRowQuota S C y) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy
  by_contra bad
  obtain ⟨_,hk,A,_,ar,_,roles⟩ := three_window_rigidity n m S C o t y hn hlin hg hu ho hl hy bad
  obtain ⟨w,r,ra,rw',_,_,⟨j,hj,rhigh,_⟩,⟨b0,_,rass⟩,early⟩ :=
    three_window_first_pair n m S C o t y hn hlin hg hu ho hl hy bad
  let D := underDisjoint C S y
  have big {a} (ha : a ∈ D) : 3 < (S a).card := by
    have h := (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2
    have h' := card_light (S a) C (o a) t hg hu (ho a) hl
    omega
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
  have hscarce : (refunds S C y).card ≤ B.card := by
    by_contra! h; exact bad (three_window_extra_refund n m S C o t y hn hlin hg hu ho hl hy h)
  have touching {b} (hb : b ∉ D) (hc : 2 ≤ (S b).card) : ¬Disjoint (S b) y := by
    intro hd
    have hnot : b ∉ B := fun hm => hb (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,(Finset.mem_filter.mp hm).2.2.1⟩,hd⟩)
    have credit := disjoint_outputs_refunded S C o y (insert b B) hlin ho (by
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · exact ⟨hd,hc⟩
      · have data := (Finset.mem_filter.mp hi).2
        exact ⟨data.1,by have := data.2.2; omega⟩)
    rw [Finset.card_insert_of_notMem hnot] at credit
    omega
  have scarce {b} (ht : ¬Disjoint (S b) y) :
      ((assigned C (S b)).erase (n+t)).card < min y.card (S b).card := by
    by_contra! h
    exact bad (three_window_touching_spare n m S C o t y hn hlin hg hu ho hl hy ⟨b,ht,h⟩)
  have swL (p : Fin n) : value C (fun q => decide (q=p)) (n+t) = true := by
    apply hl
    have e : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [e,Finset.card_singleton]; omega
  have notFull {v} (lt : v<w) (ne : v≠n+t) (hfull : ∀ p : Fin n, p ∈ support C v) : False := by
    have ec := early v lt ne j hj
    rw [Finset.inter_eq_right.mpr (fun p _ => hfull p)] at ec
    have := big hj
    omega
  have noconsume {v} (vsw : n+t<v) (vw : v<w) (idx : v-n<C.gates.length) :
      n+t ∉ C.gates[v-n].inputs := by
    intro consumes
    let g := C.gates[v-n]
    change n+t ∈ g.inputs at consumes
    have inRange : v ∈ Finset.Ico n (n+C.size) := Finset.mem_Ico.mpr ⟨by omega,by change v<n+C.gates.length; omega⟩
    have rc := roles v inRange (by omega) (fun ha => Nat.lt_asymm vsw (Finset.mem_Ico.mp (ar ha)).2)
    obtain ⟨b,ass,_⟩ := rc.resolve_right (by
      rintro ⟨a,ha,_,hs,_⟩
      have ec := early v vw (by omega) a ha
      rw [Finset.inter_eq_right.mpr hs] at ec
      have := big ha
      omega)
    have inD : b ∉ D := by
      intro h
      have ec := early v vw (by omega) b h
      rw [Finset.inter_eq_left.mpr (Finset.mem_filter.mp ass).2.1] at ec
      have := (Finset.mem_filter.mp ass).2.2
      omega
    have mV := (Finset.mem_filter.mp ass).2.2
    have mB := mV.trans (Finset.card_le_card (Finset.mem_filter.mp ass).2.1)
    have ht := touching inD mB
    have count := scarce ht
    let read (x : Fin n → Bool) (q : ℕ) := if q<v then value C x q else false
    have eval (x : Fin n → Bool) : value C x v = g.op.eval (g.inputs.map (read x)) :=
      gate_value C x v (Finset.mem_Ico.mp inRange).1 (Finset.mem_Ico.mp inRange).2
    obtain ⟨ops,len⟩ := hg g (List.getElem_mem _)
    have hand : g.op = .and := by
      rcases ops with h | h | h
      · exact h
      · apply False.elim
        apply notFull vw (by omega)
        intro p
        apply (mem_support _ _ _).mpr
        rw [eval,h]
        simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
        exact ⟨_,⟨_,consumes,rfl⟩,by simpa [read,vsw] using swL p⟩
      · have e := hu ⟨v-n,idx⟩ h
        change v-n=t at e
        omega
    have hall (x : Fin n → Bool) : value C x v = true ↔ ∀ u ∈ g.inputs, read x u = true := by
      rw [eval,hand]; simp [GateOp.eval]
    have other : ∃ u ∈ g.inputs, u ≠ n+t := by
      by_contra! h
      apply notFull vw (by omega)
      intro p
      exact (mem_support _ _ _).mpr ((hall _).mpr (fun q hq => by rw [h q hq]; simpa [read,vsw] using swL p))
    obtain ⟨u,huin,une⟩ := other
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(support (n:=n) C v).card)
    have hread := (hall _).mp ((mem_support _ _ _).mp hp) u huin
    have uv : u<v := by by_contra h; simp [read,h] at hread
    have either (a) (ha : a ∈ g.inputs) : a=n+t ∨ a=u := by
      rcases two_distinct_inputs g.inputs consumes huin une.symm len with e | e
      · simpa [e] using ha
      · simpa [e,or_comm] using ha
    have same : support (n:=n) C v = support C u := by
      ext p
      rw [mem_support,mem_support,hall]
      exact ⟨fun h => by simpa [read,uv] using h u huin, fun h q hq => by
        rcases either q hq with rfl | rfl
        · simpa [read,vsw] using swL p
        · simpa [read,uv] using h⟩
    let P := (assigned C (S b)).erase (n+t)
    have vP : v ∈ P := Finset.mem_erase.mpr ⟨by omega,ass⟩
    have uP : u ∈ P := by
      have es := (Finset.mem_filter.mp ass).2
      rw [same] at es
      exact Finset.mem_erase.mpr ⟨une,Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C u es.2),es⟩⟩
    have oe : support C (o b) = S b := by ext p; exact (mem_support _ _ _).trans (L_meta_997_refund.output_singleton S C o ho b p)
    have oz : o b ≠ n+t := by
      intro eq
      have h0 := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
      rw [←eq,ho] at h0
      simp at h0
    have oP : o b ∈ P := Finset.mem_erase.mpr ⟨oz,Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr (support_gate C (o b) (by simpa [oe] using mB)),by rw [oe]; exact ⟨by rfl,mB⟩⟩⟩
    have ov : o b ≠ v := by
      intro e
      obtain ⟨q,hq,hqy⟩ := Finset.not_disjoint_iff.mp ht
      have on := (ho b (fun p => decide (p ∈ y))).symm
      have hot : value C (fun p => decide (p ∈ y)) v = true := (e ▸ on.symm).trans (decide_eq_true ⟨q,hq,decide_eq_true hqy⟩)
      have hh := (hall _).mp hot _ consumes
      change value C (fun p => decide (p ∈ y)) (n+t) = false at hy
      simp [read,vsw,hy] at hh
    change P.card < min y.card (S b).card at count
    have ou : o b = u := by
      by_contra h
      have sub : {o b,u,v} ⊆ P := Finset.insert_subset oP (Finset.insert_subset uP (Finset.singleton_subset_iff.mpr vP))
      have c := Finset.card_le_card sub
      simp [h,ov,ne_of_lt uv] at c
      omega
    have c := before_output_charge C (S b) (o b) t v ⟨v-n,idx⟩ (by simp; omega)
      (ou ▸ uv) vsw y.card hg hu (ho b) hl (by omega)
    have filt : P.filter (· < v) ⊂ P := Finset.ssubset_iff_of_subset (Finset.filter_subset _ _) |>.mpr
      ⟨v,vP,fun hm => Nat.lt_irrefl _ (Finset.mem_filter.mp hm).2⟩
    have sm := Finset.card_lt_card filt
    change min y.card (S b).card ≤ (P.filter (· < v)).card+1 at c
    omega
  have monotone (v) (vw : v<w) (vn : v ≠ n+t) : support C v ⊆ Heavy.supp C y v := by
    induction v using Nat.strong_induction_on with
    | ind v ih =>
      intro p hp
      let x : Fin n → Bool := fun q => decide (q=p)
      let z : Fin n → Bool := fun q => decide (q∈y ∨ q=p)
      have hv : value C x v = true := (mem_support C v p).mp hp
      apply (Heavy.mem_supp C y v p).mpr
      change value C z v = true
      by_cases vin : v<n
      · let q : Fin n := ⟨v,vin⟩
        change value C x q.val = true at hv
        change value C z q.val = true
        rw [input_value] at hv ⊢
        exact decide_eq_true (Or.inr (of_decide_eq_true hv))
      by_cases range : v < n+C.size
      swap
      · rw [missing_value C _ _ (by omega)] at hv; contradiction
      have idx : v-n<C.gates.length := by change v<n+C.gates.length at range; omega
      let g := C.gates[v-n]
      let rd (a : Fin n → Bool) (u : ℕ) := if u<v then value C a u else false
      have ev (a : Fin n → Bool) : value C a v = g.op.eval (g.inputs.map (rd a)) :=
        gate_value C a v (by omega) range
      have step (u) (huin : u ∈ g.inputs) : rd x u = true → rd z u = true := by
        by_cases below : u<v
        · have une : u≠n+t := by
            rintro rfl
            exact noconsume below vw idx huin
          simp only [rd,ite_eq_left below]
          exact fun h => (Heavy.mem_supp C y u p).mp (ih u below (below.trans vw) une ((mem_support C u p).mpr h))
        · simp [rd,below]
      obtain ⟨ops,_⟩ := hg g (List.getElem_mem _)
      rw [ev] at hv ⊢
      rcases ops with op | op | op
      · simp [op,GateOp.eval] at hv ⊢
        exact fun u hu => step u hu (hv u hu)
      · simp [op,GateOp.eval] at hv ⊢
        obtain ⟨u,hu,hh⟩ := hv
        exact ⟨u,hu,step u hu hh⟩
      · have e := hu ⟨v-n,idx⟩ op
        change v-n=t at e
        omega
  have sub := monotone r rw' (by omega)
  rw [rhigh] at sub
  have ec := early r rw' (by omega) j hj
  rw [Finset.inter_eq_left.mpr sub] at ec
  have := (Finset.mem_filter.mp rass).2.2
  omega



end L_meta_997.Small

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

/-- Erase a gate whose value is a copy of an older wire. Only later uses
are redirected, so an out-of-range reference at an earlier gate stays false. -/
private lemma bypass_copy {n : ℕ} (E : Circuit) (v u : ℕ) (hv : n ≤ v ∧ v<n+E.size)
    (hu : u<v) (hg : good E) (he : ∀ x : Fin n → Bool, value E x v = value E x u) :
    ∃ D : Circuit, good D ∧ D.size=E.size ∧
      (∀ x : Fin n → Bool, value D x v = false) ∧
      (∀ x : Fin n → Bool, ∀ w, w≠v → value D x w=value E x w) ∧
      (∀ i, n+i<v → D.gates[i]?=E.gates[i]?) ∧
      (∀ w, n≤w → w≠v → (andAt D n w ↔ andAt E n w)) := by
  classical
  let replace (w r : ℕ) := if v<w ∧ r=v then u else r
  let gate (i : Fin E.gates.length) : Gate := if n+i.val=v then ⟨.or,[]⟩
    else ⟨(E.gates.get i).op,(E.gates.get i).inputs.map (replace (n+i.val))⟩
  let D : Circuit := ⟨List.ofFn gate,0⟩
  have len : D.size=E.size := by simp [D,Circuit.size]
  have get (i : ℕ) (hi : i<E.gates.length) : D.gates[i]'(by simpa [D] using hi) = gate ⟨i,hi⟩ := by simp [D]
  have step (x : Fin n → Bool) (w : ℕ) (lo : n ≤ w) (up : w<n+E.size) :
      value D x w = (gate ⟨w-n,by change w<n+E.gates.length at up; omega⟩).op.eval
        ((gate ⟨w-n,by change w<n+E.gates.length at up; omega⟩).inputs.map fun r =>
          if r<w then value D x r else false) := by
    rw [gate_value D x w lo (len ▸ up),get]
  refine ⟨D,?_,len,?_,?_,?_,?_⟩
  · intro g hm
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
    have h := hg _ (List.get_mem E.gates i)
    dsimp [gate]
    split <;> simp_all
  · intro x
    rw [step x v hv.1 hv.2]
    simp [gate,Nat.add_sub_of_le hv.1,GateOp.eval]
  · intro x w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ne
      by_cases inp : w<n
      · let p : Fin n := ⟨w,inp⟩
        change value D x p.val=value E x p.val
        rw [input_value,input_value]
      by_cases up : w<n+E.size
      swap
      · rw [missing_value E _ _ (by omega),missing_value D _ _ (by rw [len]; omega)]
      have lo : n ≤ w := by omega
      rw [step x w lo up, gate_value E x w lo up]
      simp only [gate,Nat.add_sub_of_le lo,ite_eq_right ne,List.map_map,List.get_eq_getElem]
      congr 1
      apply List.map_congr_left
      intro r _
      by_cases lt : r<w
      · by_cases rv : r=v
        · subst r
          simpa [Function.comp_def,replace,lt,hu.trans lt,ih u (hu.trans lt) (ne_of_lt hu)] using (he x).symm
        · simp [replace,rv,lt,ih r lt rv]
      · have nh : ¬(v<w ∧ r=v) := fun h => lt (h.2 ▸ h.1)
        simp [replace,lt,nh]
  · intro i hi
    have ei : i<E.gates.length := by have up := hv.2; change v<n+E.gates.length at up; omega
    have di : i<D.gates.length := by change i<D.size; rw [len]; exact ei
    rw [List.getElem?_eq_getElem di,List.getElem?_eq_getElem ei,get i ei]
    simp [gate,replace,ne_of_lt hi,not_lt_of_ge hi.le]
  · intro w lo ne
    by_cases up : w<n+E.size
    · have ei : w-n<E.gates.length := by change w<n+E.gates.length at up; omega
      have di : w-n<D.gates.length := by change w-n<D.size; rw [len]; exact ei
      unfold andAt
      rw [List.getElem?_eq_getElem di,List.getElem?_eq_getElem ei,get (w-n) ei]
      simp [gate,Nat.add_sub_of_le lo,ne,List.get_eq_getElem]
    · have ei : E.gates.length ≤ w-n := by have eu : n+E.gates.length ≤ w := Nat.le_of_not_gt up; omega
      have di : D.gates.length ≤ w-n := by change D.size ≤ w-n; rw [len]; exact ei
      unfold andAt
      rw [List.getElem?_eq_none di,List.getElem?_eq_none ei]

/-- In the monotone low-window circuit the switch is constant true.
A gate reading it is constant or copies its other input, including unary
and repeated-input cases. -/
private lemma fold_consumer {n : ℕ} (E : Circuit) (hg : good E) (z v : ℕ)
    (range : n ≤ v ∧ v<n+E.size) (zv : z<v)
    (idx : v-n<E.gates.length) (mem : z ∈ E.gates[v-n].inputs)
    (hot : ∀ x : Fin n → Bool, value E x z=true) :
    ∃ D : Circuit, ∃ f : ℕ → ℕ, good D ∧ D.size=E.size ∧
      (∀ x : Fin n → Bool, value D x v=false) ∧
      (∀ x : Fin n → Bool, ∀ w, value D x (f w)=value E x w) ∧
      (∀ w, w≠v → f w=w) ∧
      (∀ i, n+i<v → D.gates[i]?=E.gates[i]?) ∧
      (∀ w, n≤w → w≠v → (andAt D n w ↔ andAt E n w)) ∧ f v≤v := by
  classical
  let g := E.gates[v-n]
  have ⟨hop,hlen⟩ := hg g (List.getElem_mem _)
  let rd (x : Fin n → Bool) (r : ℕ) := if r<v then value E x r else false
  have ev (x : Fin n → Bool) : value E x v=g.op.eval (g.inputs.map (rd x)) :=
    gate_value E x v range.1 range.2
  have key : (∀ x : Fin n → Bool, value E x v=false) ∨
      ∃ u<v, ∀ x : Fin n → Bool, value E x v=value E x u := by
    change z ∈ g.inputs at mem
    rcases hop with hand | hor
    · obtain ⟨a,tail,eq⟩ : ∃ a tail, g.inputs=a::tail := by
        cases h : g.inputs with
        | nil => simp [h] at mem
        | cons a t => exact ⟨a,t,rfl⟩
      cases tail with
      | nil =>
        have az : z=a := by simpa [eq] using mem
        subst a
        exact Or.inr ⟨z,zv,fun x => by simp [ev x,hand,eq,GateOp.eval,rd,zv]⟩
      | cons b rest =>
        have er : rest=[] := by
          apply List.length_eq_zero_iff.mp
          have h : (a::b::rest).length ≤ 2 := eq ▸ hlen
          simpa using h
        subst rest
        have ab : z=a ∨ z=b := by simpa [eq] using mem
        have take (u : ℕ) (h : ∀ x : Fin n → Bool, value E x v=rd x u) :
            (∀ x : Fin n → Bool, value E x v=false) ∨ ∃ u<v, ∀ x : Fin n → Bool, value E x v=value E x u := by
          by_cases lt : u<v
          · exact Or.inr ⟨u,lt,fun x => by simpa [rd,lt] using h x⟩
          · exact Or.inl (fun x => by simpa [rd,lt] using h x)
        rcases ab with rfl | rfl
        · apply take b
          intro x; simp [ev x,hand,eq,GateOp.eval,rd,zv,hot]
        · apply take a
          intro x; simp [ev x,hand,eq,GateOp.eval,rd,zv,hot]
    · right
      refine ⟨z,zv,?_⟩
      intro x
      rw [hot,ev x,hor]
      simp only [GateOp.eval,List.any_eq_true,List.mem_map,id_eq]
      exact ⟨_,⟨z,mem,rfl⟩,by simp [rd,zv,hot]⟩
  rcases key with hf | ⟨u,uv,he⟩
  · exact ⟨E,id,hg,rfl,hf,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ _ => Iff.rfl,le_rfl⟩
  · obtain ⟨D,hd,sz,dead,agree,pre,stable⟩ := bypass_copy E v u range uv hg he
    refine ⟨D,(fun w => if w=v then u else w),hd,sz,dead,?_,?_,pre,stable,by simpa using uv.le⟩
    · intro x w
      by_cases eq : w=v
      · subst w; simpa [he x] using agree x u (ne_of_lt uv)
      · simpa [eq] using agree x w eq
    · intro w ne; simp [ne]

lemma fold_one_reader_stable {n k : ℕ} (C : Circuit) (t : ℕ) (a : Fin C.gates.length)
    (after : t<a.val) (reads : n+t ∈ (C.gates.get a).inputs)
    (gates : hasAllowedGates C)
    (uniqueNot : ∀ j : Fin C.gates.length, (C.gates.get j).op = .not → j.val=t)
    (light : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card<k →
      value C x (n+t)=true) :
    ∃ (D : Circuit) (f : ℕ → ℕ), good D ∧ D.size=C.size ∧
      (∀ x : Fin n → Bool, value D x (n+a.val)=false) ∧
      (∀ w, w≠n+a.val → f w=w) ∧
      (∀ (x : Fin n → Bool), (Finset.univ.filter (fun p => x p=true)).card<k →
        ∀ w, value D x (f w)=value C x w) ∧
      (∀ w, n≤w → w≠n+a.val → w≠n+t → (andAt D n w ↔ andAt C n w)) ∧ f (n+a.val) ≤ n+a.val := by
  classical
  obtain ⟨gs,o⟩ := C
  let C : Circuit := ⟨gs,o⟩
  let v := n+a.val
  let z := n+t
  have tv : t<gs.length := after.trans a.isLt
  let j : Fin gs.length := ⟨t,tv⟩
  let E := frozen true gs t
  have eg : good E := fixed_gates true gs j gates (fun i h => Fin.ext (uniqueNot i h))
  have es : E.size=gs.length := fixed_size ..
  have er : n ≤ v ∧ v<n+E.size := by
    rw [es]
    have h := a.isLt
    change a.val<gs.length at h
    dsimp [v]
    omega
  have ei : v-n<E.gates.length := by change v-n<E.size; have h:=er.2; omega
  have em : E.gates[v-n]'ei = gs.get a := by
    have ne : a.val≠t := by omega
    simpa [E,frozen,v,ne,Ne.symm ne,List.get_eq_getElem]
  have eh (x : Fin n → Bool) : value E x z=true := fixed_value true gs j x
  obtain ⟨D,f,hd,ds,dead,agree,unchanged,_,same,older⟩ := fold_consumer E eg z v er
    (by dsimp [z,v]; omega) ei (em.symm ▸ reads) eh
  refine ⟨D,f,hd,ds.trans es,dead,unchanged,
    fun x hx w => (agree x w).trans (fixed_eq true gs j o x (light x hx) w),?_,older⟩
  intro w lo ne nz
  apply (same w lo ne).trans
  have trel : t≠w-n := by omega
  by_cases hi : w-n<gs.length
  · have hi' : w-n<E.gates.length := by change w-n<E.size; rw [es]; exact hi
    unfold andAt
    change (E.gates[w-n]?).map Gate.op = some .and ↔ (gs[w-n]?).map Gate.op = some .and
    rw [List.getElem?_eq_getElem hi',List.getElem?_eq_getElem hi]
    simp [E,frozen,trel,Ne.symm trel]
  · have hi' : E.gates.length≤w-n := by change E.size≤w-n; rw [es]; omega
    unfold andAt
    change (E.gates[w-n]?).map Gate.op = some .and ↔ (gs[w-n]?).map Gate.op = some .and
    rw [List.getElem?_eq_none hi',List.getElem?_eq_none (by omega)]

lemma switch_has_reader {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ) (hk : 2 ≤ k)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card<k → value C x (n+t)=true)
    (short : (assigned C T).card+1<T.card) :
    ∃ a : Fin C.gates.length, t<a.val ∧ n+t ∈ (C.gates.get a).inputs := by
  classical
  cases C with
  | mk gs oo =>
    let C : Circuit := ⟨gs,oo⟩
    have h0 := hl (fun _ => false) (by simpa using (show 0<k by omega))
    have tv : t<gs.length := by
      by_contra! h
      have e := missing_value C (fun _ : Fin n => false) (n+t) (by change n+gs.length ≤ n+t; omega)
      exact Bool.noConfusion (e.symm.trans h0)
    let j : Fin gs.length := ⟨t,tv⟩
    have hoz : o≠n+t := by
      rintro rfl
      rw [out] at h0
      simp at h0
    have used : ∃ a : Fin gs.length, t<a.val ∧ n+t ∈ (gs.get a).inputs := by
      by_contra! unused
      let F := frozen false gs t
      have fg : good F := fixed_gates false gs j hg (fun i h => Fin.ext (hu i h))
      have agree (x : Fin n → Bool) (w : ℕ) (ne : w≠n+t) : value F x w=value C x w := by
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          by_cases inp : w<n
          · let p : Fin n := ⟨w,inp⟩
            change value F x p.val=value C x p.val
            rw [input_value,input_value]
          by_cases up : w<n+gs.length
          swap
          · rw [missing_value F _ _ (by rw [show F.size=gs.length from fixed_size ..]; omega),
                missing_value C _ _ (by change n+gs.length ≤ w; omega)]
          rw [show value F x w = _ from fixed_other false gs t x w (by omega) up ne,
              show value C x w = _ from orig_value gs oo x w (by omega) up]
          apply repl_eval_congr
          intro r hr
          by_cases below : r<w
          · have rn : r≠n+t := by
              rintro rfl
              exact unused (⟨w-n,by omega⟩ : Fin gs.length) (by change t<w-n; omega) hr
            simpa only [ite_eq_left below] using ih r below rn
          · simp [below]
      have sc : assigned F T ⊆ assigned C T := by
        intro w hw
        obtain ⟨hr,hs,hc⟩ := Finset.mem_filter.mp hw
        have ne : w≠n+t := by
          rintro rfl
          have em : support (n:=n) F (n+t)=∅ := by
            ext p
            simp [mem_support,show value F (fun q : Fin n => decide (q=p)) (n+t)=false from fixed_value false gs j _]
          rw [em,Finset.card_empty] at hc
          omega
        have eq : support (n:=n) F w=support C w := by ext p; rw [mem_support,mem_support,agree _ _ ne]
        exact Finset.mem_filter.mpr ⟨by simpa only [show F.size=C.size from fixed_size ..] using hr,eq ▸ hs,eq ▸ hc⟩
      have cnt := card_assigned (k:=T.card) (c:=T.card-1) F T o fg
        (fun p => by rw [agree _ _ hoz]; change value ⟨gs,oo⟩ _ o = true ↔ _; rw [out]; simp)
        (fun x _ off => by rw [agree _ _ hoz]; exact (out x).trans (decide_eq_false (fun ⟨p,hp,on⟩ => Bool.noConfusion ((off p hp).symm.trans on))))
        (by omega) (by omega)
      have := Finset.card_le_card sc
      change (assigned C T).card+1<T.card at short
      omega
    exact used

private lemma low_spare_model {n k : ℕ} (C : Circuit) (T : Finset (Fin n)) (o t : ℕ) (hk : 2 ≤ k)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ T, x p = true))
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card<k → value C x (n+t)=true)
    (short : (assigned C T).card+1<T.card) :
    ∃ (D : Circuit) (f : ℕ → ℕ) (v : ℕ), good D ∧ D.size=C.size ∧ n+t<v ∧ v<n+C.size ∧
      (∀ x : Fin n → Bool, value D x v=false) ∧ (∀ w, w≠v → f w=w) ∧
      ∀ (x : Fin n → Bool), (Finset.univ.filter (fun p => x p=true)).card<k →
        ∀ w, value D x (f w)=value C x w := by
  classical
  cases C with
  | mk gs oo =>
    let C : Circuit := ⟨gs,oo⟩
    have tv : t<gs.length := by
      have ⟨u,hu',_⟩ := switch_has_reader C T o t hk hg hu out hl short
      exact hu'.trans u.isLt
    let j : Fin gs.length := ⟨t,tv⟩
    obtain ⟨a,ta,mem⟩ := switch_has_reader C T o t hk hg hu out hl short
    have al : a.val < gs.length := a.isLt
    let E := frozen true gs t
    have eop : good E := fixed_gates true gs j hg (fun i h => Fin.ext (hu i h))
    have es : E.size = gs.length := fixed_size ..
    let v := n+a.val
    have ix : v-n<E.gates.length := by change v-n<E.size; rw [es]; simp [v,al]
    have ein : n+t ∈ E.gates[v-n].inputs := by
      have ne : a.val≠t := by omega
      simpa [E,frozen,v,ne,Ne.symm ne,List.get_eq_getElem] using mem
    obtain ⟨D,f,goodD,sz,dead,all,other,_,_,_⟩ := fold_consumer E eop (n+t) v
      ⟨by dsimp [v]; omega,by rw [es]; dsimp [v]; have := a.isLt; omega⟩
      (by dsimp [v]; omega) ix ein (fun x => fixed_value true gs j x)
    exact ⟨D,f,v,goodD,sz.trans es,by dsimp [v]; omega,by change n+a.val<n+gs.length; omega,
      dead,other,fun x hx w => (all x w).trans (fixed_eq true gs j oo x (hl x hx) w)⟩


/-- Folding one direct use of the switch gives one more unit in the
distinguished-row count. A fully paid disjoint row can spend its own
output refund if the folded gate was among its private gates. -/
-- Count refunds only for disjoint rows longer than the light-window quota.
-- Refunds above that count add directly to the distinguished-row quota.
theorem folded_projection_with_paid_slack {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (hs : (assigned C (S d)).card+1 < (S d).card)
    (slack : ℕ)
    (extra_refunds : (Finset.univ.filter (fun i => Disjoint (S i) y ∧ y.card < (S i).card)).card + slack ≤
      (refunds S C y).card)
    (quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
       (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+slack) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  let k := y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ k+2 ≤ (S i).card)
  let R := Finset.univ.filter (fun i => Disjoint (S i) y ∧ k < (S i).card)
  have hk' : 2 ≤ k := hk
  have hbig : k < (S d).card := by have := card_light (S d) C (o d) t hg hu (out d) hl; change min k (S d).card ≤ _ at this; omega
  obtain ⟨D,f,v,goodD,sz,after,vr,dead,unchanged,agree⟩ :=
    low_spare_model C (S d) (o d) t hk hg hu (out d) hl hs
  have zero : (Finset.univ.filter (fun _ : Fin n => false = true)).card < y.card := by simpa using (show 0<y.card by omega)
  have sing (p : Fin n) : (Finset.univ.filter (fun q : Fin n => decide (q=p) = true)).card < y.card := by
    have e : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [e,Finset.card_singleton]; omega
  have same (w : ℕ) (ne : w≠v) : support (n:=n) D w=support C w := by
    ext p; rw [mem_support,mem_support]
    rw [← unchanged w ne,agree _ (sing p) w,unchanged w ne]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,dead]
  have contain (i) : assigned D (S i) ⊆ assigned C (S i) := by
    intro w hw
    obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
    have ne : w≠v := by rintro rfl; rw [empty,Finset.card_empty] at hc; omega
    rw [same w ne] at hsub hc
    exact Finset.mem_filter.mpr ⟨sz ▸ hr,hsub,hc⟩
  have lose (i) : (assigned C (S i)).card ≤ (assigned D (S i)).card+1 := by
    have sub : assigned C (S i) ⊆ insert v (assigned D (S i)) := by
      intro w hw
      by_cases e : w=v
      · exact Finset.mem_insert.mpr (Or.inl e)
      obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
      rw [←same w e] at hsub hc
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨sz.symm ▸ hr,hsub,hc⟩))
    exact (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  have output (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) :
      value D x (f (o i))=decide (∃ p ∈ S i, x p=true) := (agree x hx _).trans (out i x)
  have singleton (i) (p : Fin n) : value D (fun q => decide (q=p)) (f (o i))=true ↔ p ∈ S i := by
    rw [output i _ (sing p)]; simp
  have sparse (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k)
      (off : ∀ p ∈ S i, x p=false) : value D x (f (o i))=false := by
    rw [output i x hx]; exact decide_eq_false (fun ⟨p,hp,on⟩ => Bool.noConfusion ((off p hp).symm.trans on))
  have mincount (i) : min k (S i).card ≤ (assigned D (S i)).card+1 := by
    by_cases e : (S i).card=0
    · simp [e]
    have cnt := card_assigned (k:=k-1) (c:=min k (S i).card-1) D (S i) (f (o i)) goodD (singleton i)
      (fun x hx => sparse i x (by omega)) (by omega) (by omega)
    omega
  have extra := (sharp_private_or_extra D (S d) (f (o d)) goodD
    (by rw [output d _ zero]; simp) (by ext p; exact (mem_support _ _ _).trans (singleton d p)) (sparse d)).resolve_left
    (by have h := Finset.card_le_card (contain d); omega)
  let weight (i : Fin m) := if Disjoint (S i) y ∧ k < (S i).card ∧ (S i).card ≤ (assigned C (S i)).card+1
    then (S i).card-1 else min k (S i).card
  have fund (i) : weight i ≤ (assigned D (S i)).card+1 := by
    dsimp [weight]; split
    · rename_i h; have := lose i; have := h.2.2; omega
    · exact mincount i
  obtain ⟨A,ac,ar,ae⟩ := guard_empty_gates C t y (by omega : 0<y.card) hg hu hl hy
  let z := n+t
  have zlt : z<v := after
  have za : z ∉ A := fun ha => Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar ha)).2
  have va : v ∉ A := fun ha => Nat.lt_asymm after (Finset.mem_Ico.mp (ar ha)).2
  have zOn (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) : value D x z=true := by
    have eq := agree x hx z
    rw [unchanged z (ne_of_lt zlt)] at eq
    exact eq.trans (hl x hx)
  have calcD := projection_gate_count S d D z (insert v A) (by omega) hpair
    (Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩) (zOn _ zero)
    (fun p => (mem_support _ _ _).mpr (zOn _ (sing p)))
    (Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by rw [sz]; have h := (Finset.mem_Ico.mp (ar hw)).2; omega⟩))
    (by simpa [ne_of_lt zlt] using za)
    (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact empty
      · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw))
    ((S d).card+k-1) (by omega) weight (fun i _ => fund i)
  rw [Finset.card_insert_of_notMem va] at calcD
  have hlen : D.gates.length=C.gates.length := sz
  rw [hlen] at calcD
  have wd : weight d=k := by simp [weight,Nat.not_le.mpr hs,min_eq_left (by omega : k≤(S d).card)]
  have cut := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) weight (Finset.mem_univ d)
  rw [wd] at cut
  have per (i) : (if Disjoint (S i) y then (S i).card else min k (S i).card) ≤
      weight i + (if i ∈ R then 1 else 0) + (if i ∈ B then (S i).card-(k+1) else 0) := by
    by_cases hd : Disjoint (S i) y
    swap
    · simp [weight,B,R,hd]
    by_cases paid : (S i).card ≤ (assigned C (S i)).card+1
    · have notshort := Nat.not_lt.mpr paid
      by_cases large : k < (S i).card
      · simp [weight,B,R,hd,paid,notshort,large]
        omega
      · have small : (S i).card ≤ k := by omega
        simp [weight,B,R,hd,paid,notshort,large,min_eq_right small]
    · have short := Nat.lt_of_not_ge paid
      by_cases large : k < (S i).card
      · have le : k ≤ (S i).card := by omega
        simp [weight,B,R,hd,paid,short,large,min_eq_left le]
        split_ifs <;> omega
      · have small : (S i).card ≤ k := by omega
        have noBig : ¬ k+2 ≤ (S i).card := by omega
        simp [weight,B,R,hd,paid,short,large,noBig,min_eq_right small]
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simp only [Finset.sum_add_distrib,Fintype.sum_ite_mem,Finset.sum_const,smul_eq_mul,mul_one] at total
  have split := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl (g:=fun i => (k+1)+((S i).card-(k+1))) (fun i hi => by
    have h := (Finset.mem_filter.mp hi).2.2.2; omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_comm B.card (k+1)] at split
  change (∑ i ∈ B, (S i).card) ≤ (k+1)*B.card+(S d).card+k+slack at quota
  change R.card + slack ≤ (refunds S C y).card at extra_refunds
  change (∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤ _
  change k ≤ A.card+1 at ac
  omega



theorem folded_projection {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (hs : (assigned C (S d)).card+1 < (S d).card)
    (quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
       (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  refine folded_projection_with_paid_slack S d C o t y hk hpair hg hu out hl hy hs 0 ?_ ?_
  · rw [Nat.add_zero]
    apply disjoint_outputs_refunded S C o y _ hpair out
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    exact ⟨h.1,by omega⟩
  · simpa only [Nat.add_zero] using quota

private lemma projection_gate_count_tight {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (z : ℕ) (A : Finset ℕ) (hD : 2 ≤ (S d).card)
    (hpair : rowLinearity S)
    (hzrange : z ∈ Finset.Ico n (n+C.size)) (htz : value C (fun _ : Fin n => false) z=true)
    (hzs : ∀ p : Fin n, p ∈ support C z)
    (hAi : A ⊆ Finset.Ico n (n+C.size)) (hAz : z ∉ A) (hAs : ∀ w ∈ A, support (n:=n) C w=∅)
    (q : ℕ) (hdweight : q ≤ (dormant C (S d)).card+1)
    (f : Fin m → ℕ)
    (hweight : ∀ i, i ≠ d → f i ≤ (assigned C (S i)).card+1)
    (tight : C.gates.length + m ≤ q + (∑ i ∈ Finset.univ.erase d, f i) + A.card+1) :
    (dormant C (S d)).card+1=q ∧
      (∀ i, i ≠ d → (assigned C (S i)).card+1=f i) ∧
      (∀ w ∈ Finset.Ico n (n+C.size), w ∉ A → w≠z →
        (∃ i, i ≠ d ∧ w ∈ assigned C (S i)) ∨ w ∈ dormant C (S d)) := by
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
  let W := insert z (U ∪ G)
  have disA : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro w wa ww
    rcases Finset.mem_insert.mp ww with hz | h
    · exact hAz (hz ▸ wa)
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i,_,hw⟩ := Finset.mem_biUnion.mp h
        have hc := (Finset.mem_filter.mp hw).2.2
        rw [hAs w wa] at hc
        simp at hc
      · have hc := (Finset.mem_filter.mp h).2.2
        rw [hAs w wa] at hc
        simp at hc
  have sub : A ∪ W ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with ha | hw
    · exact hAi ha
    · rcases Finset.mem_insert.mp hw with h | hw
      · exact h ▸ hzrange
      · rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
          exact (Finset.mem_filter.mp hi).1
        · exact (Finset.mem_filter.mp hw).1
  have Wcard : (A ∪ W).card = A.card + (U.card + G.card + 1) := by
    rw [Finset.card_union_of_disjoint disA]
    simp only [W,Finset.card_insert_of_notMem hnotin,Finset.card_union_of_disjoint dis]
  have hgate := Finset.card_le_card sub
  rw [Wcard] at hgate
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left,Circuit.size] at hgate
  have hcard := Finset.card_erase_add_one (Finset.mem_univ d)
  change I.card + 1 = _ at hcard
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  have hgeneral := sum_row_weights S I C f hpair (fun i hi => hweight i (Finset.mem_erase.mp hi).1)
  change (∑ i ∈ I, f i) ≤ U.card + I.card at hgeneral
  change C.gates.length + m ≤ q + (∑ i ∈ I, f i) + A.card+1 at tight
  have hfull : A ∪ W = Finset.Ico n (n+C.size) := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [Wcard]
    simp only [Nat.card_Ico,Nat.add_sub_cancel_left,Circuit.size]
    change q ≤ G.card+1 at hdweight
    omega
  change q ≤ G.card+1 at hdweight
  refine ⟨by change G.card+1=q; omega,?_,?_⟩
  · intro i ne
    have hi : i ∈ I := Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩
    let f' := fun j => f j + if j=i then 1 else 0
    by_contra neq
    have hpoint (j) (hj : j ∈ I) : f' j ≤ (assigned C (S j)).card+1 := by
      by_cases e : j=i
      · subst j
        have h := hweight i ne
        simp only [f',ite_true]
        omega
      · simpa only [f',ite_eq_right e,Nat.add_zero] using hweight j (Finset.mem_erase.mp hj).1
    have hh := sum_row_weights S I C f' hpair hpoint
    change (∑ j ∈ I, f' j) ≤ U.card + I.card at hh
    simp only [f',Finset.sum_add_distrib,Finset.sum_ite_eq',hi,ite_true] at hh
    omega
  · intro w wr wa wz
    have hh : w∈A∪W := hfull.symm ▸ wr
    have hw : w∈U∪G := (Finset.mem_insert.mp ((Finset.mem_union.mp hh).resolve_left wa)).resolve_left wz
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨i,hi,wi⟩ := Finset.mem_biUnion.mp h
      exact Or.inl ⟨i,(Finset.mem_erase.mp hi).1,wi⟩
    · exact Or.inr h

theorem folded_model_tight {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hs : (assigned C (S d)).card+1 < (S d).card)
    (quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
       (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+1)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m))
    (D : Circuit) (f : ℕ → ℕ) (v : ℕ) (goodD : good D) (sz : D.size=C.size)
    (after : n+t<v) (vr : v<n+C.size) (dead : ∀ x : Fin n → Bool, value D x v=false)
    (unchanged : ∀ w, w≠v → f w=w)
    (agree : ∀ (x : Fin n → Bool), (Finset.univ.filter (fun p => x p=true)).card<y.card →
      ∀ w, value D x (f w)=value C x w)
    (A : Finset ℕ) (ac : y.card ≤ A.card+1) (ar : A ⊆ Finset.Ico n (n+t))
    (ae : ∀ w ∈ A, support (n:=n) C w=∅) :
    A.card+1=y.card ∧
      (∀ i, Disjoint (S i) y → 2 ≤ (S i).card → y.card < (S i).card) ∧
      (refunds S C y).card = (Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)).card ∧
      (dormant D (S d)).card+1=(S d).card+y.card-1 ∧
      (∀ i, i≠d → (assigned D (S i)).card+1 =
        if Disjoint (S i) y ∧ y.card < (S i).card ∧ (S i).card ≤ (assigned C (S i)).card+1
        then (S i).card-1 else min y.card (S i).card) ∧
      (∀ w ∈ Finset.Ico n (n+D.size), w ∉ A → w≠v → w≠n+t →
        (∃ i, i≠d ∧ w ∈ assigned D (S i)) ∨ w ∈ dormant D (S d)) := by
  classical
  let k := y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ k+2 ≤ (S i).card)
  let R := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  have hk' : 2 ≤ k := hk
  have hbig : k < (S d).card := by have := card_light (S d) C (o d) t hg hu (out d) hl; change min k (S d).card ≤ _ at this; omega
  have zero : (Finset.univ.filter (fun _ : Fin n => false = true)).card < y.card := by simpa using (show 0<y.card by omega)
  have sing (p : Fin n) : (Finset.univ.filter (fun q : Fin n => decide (q=p) = true)).card < y.card := by
    have e : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [e,Finset.card_singleton]; omega
  have same (w : ℕ) (ne : w≠v) : support (n:=n) D w=support C w := by
    ext p; rw [mem_support,mem_support]
    rw [← unchanged w ne,agree _ (sing p) w,unchanged w ne]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,dead]
  have contain (i) : assigned D (S i) ⊆ assigned C (S i) := by
    intro w hw
    obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
    have ne : w≠v := by rintro rfl; rw [empty,Finset.card_empty] at hc; omega
    rw [same w ne] at hsub hc
    exact Finset.mem_filter.mpr ⟨sz ▸ hr,hsub,hc⟩
  have lose (i) : (assigned C (S i)).card ≤ (assigned D (S i)).card+1 := by
    have sub : assigned C (S i) ⊆ insert v (assigned D (S i)) := by
      intro w hw
      by_cases e : w=v
      · exact Finset.mem_insert.mpr (Or.inl e)
      obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
      rw [←same w e] at hsub hc
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨sz.symm ▸ hr,hsub,hc⟩))
    exact (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  have output (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) :
      value D x (f (o i))=decide (∃ p ∈ S i, x p=true) := (agree x hx _).trans (out i x)
  have singleton (i) (p : Fin n) : value D (fun q => decide (q=p)) (f (o i))=true ↔ p ∈ S i := by
    rw [output i _ (sing p)]; simp
  have sparse (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k)
      (off : ∀ p ∈ S i, x p=false) : value D x (f (o i))=false := by
    rw [output i x hx]; exact decide_eq_false (fun ⟨p,hp,on⟩ => Bool.noConfusion ((off p hp).symm.trans on))
  have mincount (i) : min k (S i).card ≤ (assigned D (S i)).card+1 := by
    by_cases e : (S i).card=0
    · simp [e]
    have cnt := card_assigned (k:=k-1) (c:=min k (S i).card-1) D (S i) (f (o i)) goodD (singleton i)
      (fun x hx => sparse i x (by omega)) (by omega) (by omega)
    omega
  have extra := (sharp_private_or_extra D (S d) (f (o d)) goodD
    (by rw [output d _ zero]; simp) (by ext p; exact (mem_support _ _ _).trans (singleton d p)) (sparse d)).resolve_left
    (by have h := Finset.card_le_card (contain d); omega)
  let weight (i : Fin m) := if Disjoint (S i) y ∧ k < (S i).card ∧ (S i).card ≤ (assigned C (S i)).card+1
    then (S i).card-1 else min k (S i).card
  have fund (i) : weight i ≤ (assigned D (S i)).card+1 := by
    dsimp [weight]; split
    · rename_i h; have := lose i; have := h.2.2; omega
    · exact mincount i
  let z := n+t
  have zlt : z<v := after
  have za : z ∉ A := fun ha => Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar ha)).2
  have va : v ∉ A := fun ha => Nat.lt_asymm after (Finset.mem_Ico.mp (ar ha)).2
  have zOn (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) : value D x z=true := by
    have eq := agree x hx z
    rw [unchanged z (ne_of_lt zlt)] at eq
    exact eq.trans (hl x hx)
  have computed := projection_gate_count S d D z (insert v A) (by omega) hpair
    (Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩) (zOn _ zero)
    (fun p => (mem_support _ _ _).mpr (zOn _ (sing p)))
    (Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by rw [sz]; have h := (Finset.mem_Ico.mp (ar hw)).2; omega⟩))
    (by simpa [ne_of_lt zlt] using za)
    (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact empty
      · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw))
    ((S d).card+k-1) (by omega) weight (fun i _ => fund i)
  have calcD := computed
  rw [Finset.card_insert_of_notMem va] at calcD
  have hlen : D.gates.length=C.gates.length := sz
  rw [hlen] at calcD
  have wd : weight d=k := by simp [weight,Nat.not_le.mpr hs,min_eq_left (by omega : k≤(S d).card)]
  have cut := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) weight (Finset.mem_univ d)
  rw [wd] at cut
  have per (i) : (if Disjoint (S i) y then (S i).card else min k (S i).card) ≤
      weight i + (if i ∈ R then 1 else 0) + (if i ∈ B then (S i).card-(k+1) else 0) := by
    by_cases hd : Disjoint (S i) y
    swap
    · simp [weight,B,R,hd]
    by_cases paid : (S i).card ≤ (assigned C (S i)).card+1
    · have notshort := Nat.not_lt.mpr paid
      simp [weight,B,R,hd,paid,notshort]
      split_ifs <;> omega
    · have short := Nat.lt_of_not_ge paid
      simp [weight,B,R,hd,paid,short]
      split_ifs <;> omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simp only [Finset.sum_add_distrib,Fintype.sum_ite_mem,Finset.sum_const,smul_eq_mul,mul_one] at total
  have split := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl (g:=fun i => (k+1)+((S i).card-(k+1))) (fun i hi => by
    have h := (Finset.mem_filter.mp hi).2.2.2; omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_comm B.card (k+1)] at split
  change (∑ i ∈ B, (S i).card) ≤ (k+1)*B.card+(S d).card+k+1 at quota
  have ref := disjoint_outputs_refunded S C o y R hpair out (fun i hi => (Finset.mem_filter.mp hi).2)
  change ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤ _) at bad
  change k ≤ A.card+1 at ac
  have cycle : D.gates.length+m ≤ (S d).card+k-1 +
      (∑ i ∈ Finset.univ.erase d, weight i)+(insert v A).card+1 := by
    rw [hlen,Finset.card_insert_of_notMem va]; omega
  have model := projection_gate_count_tight S d D z (insert v A) (by omega) hpair
    (Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩) (zOn _ zero)
    (fun p => (mem_support _ _ _).mpr (zOn _ (sing p)))
    (Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by rw [sz]; have h := (Finset.mem_Ico.mp (ar hw)).2; omega⟩))
    (by simpa [ne_of_lt zlt] using za)
    (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact empty
      · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw))
    ((S d).card+k-1) (by omega) weight (fun i _ => fund i) cycle
  have sumEq : (∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) =
      ∑ i, (weight i + (if i ∈ R then 1 else 0) + (if i ∈ B then (S i).card-(k+1) else 0)) := by
    simp only [Finset.sum_add_distrib,Fintype.sum_ite_mem,Finset.sum_const,smul_eq_mul,mul_one]
    omega
  have perEq := (Finset.sum_eq_sum_iff_of_le (s:=Finset.univ) (fun i _ => per i)).mp sumEq
  refine ⟨by omega,?_,by change (refunds S C y).card=R.card; omega,model.1,model.2.1,?_⟩
  · intro i dis big
    by_contra! small
    have eq := perEq i (Finset.mem_univ _)
    change (S i).card ≤ k at small
    have hmR : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis,big⟩
    have hmB : i ∉ B := by
      intro mem
      have := (Finset.mem_filter.mp mem).2.2.2
      omega
    simp [weight,dis,Nat.not_lt.mpr small,min_eq_right small,hmR,hmB] at eq
  · intro w wr wa wv wz
    exact model.2.2 w wr (by simp [wv,wa]) wz

end L_meta_997.Light

namespace L_meta_997.Small
open L_meta_997.Light
private lemma folded_geometry {n m : ℕ} (S : Fin m → Finset (Fin n)) (B : Finset (Fin m))
    (k : ℕ) (V : Finset (Fin n)) (hk : 5 ≤ k) (hsize : V.card ≤ 6*k+2)
    (hb : B.Nonempty) (hsub : ∀ i ∈ B, S i ⊆ V) (hbig : ∀ i ∈ B, k+2 ≤ (S i).card)
    (hlin : rowLinearity S) :
    ∃ d ∈ B, (∀ i ∈ B, (S i).card ≤ (S d).card) ∧
      ((∑ i ∈ B, (S i).card) ≤ B.card*(k+1)+(S d).card+k ∨
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

theorem size_window_five_or_more : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), 5 ≤ y.card → n ≤ 7*y.card+2 → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  classical
  intro n m S C o t y hk hn hlin hg hu ho hl hy
  let k := y.card
  let p := fun i => (assigned C (S i)).card+1 < (S i).card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧ p i ∧ k+2 ≤ (S i).card)
  let V := Finset.univ \ y
  have hV : V.card ≤ 6*k+2 := by
    simp only [V,Finset.card_sdiff_of_subset (Finset.subset_univ y),Finset.card_univ,Fintype.card_fin]
    dsimp [k]; omega
  have data {i} (hi : i ∈ B) : Disjoint (S i) y ∧ p i ∧ k+2 ≤ (S i).card := (Finset.mem_filter.mp hi).2
  have ct := L_meta_997_aux.disjoint_terminal_deficit C y t S o (by omega : 2 ≤ y.card)
    (Finset.card_pos.mp (by omega)) hg hu hl hy hlin ho
  have he : L_meta_997_aux.underDisjoint C S y =
      Finset.univ.filter (fun i => Disjoint (S i) y ∧ p i) := by
    ext i
    simp [p,L_meta_997_aux.underDisjoint,L_meta_997_aux.underpaid,and_comm]
  rw [he,Finset.sum_filter] at ct
  have eid := excess_identity S y p k
  change (∑ i, if Disjoint (S i) y ∧ p i then (S i).card-(k+1) else 0) =
    ∑ i ∈ B, ((S i).card-(k+1)) at eid
  change _ + k ≤ C.size + m + ∑ i, if Disjoint (S i) y ∧ p i then (S i).card-(k+1) else 0 at ct
  rw [eid] at ct
  change (∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤ C.size+(refunds S C y).card+m
  change (∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) + k ≤ _ at ct
  by_cases nonempty : B.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty,Finset.sum_empty] at ct
    omega
  obtain ⟨d,hd,_,pr | tr⟩ := folded_geometry S B k V hk hV nonempty
    (fun i hi a ha => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp (data hi).1 ha⟩)
    (fun i hi => (data hi).2.2) hlin
  · apply folded_projection S d C o t y (by omega) hlin hg hu ho hl hy (data hd).2.1
    simpa [Nat.mul_comm] using pr
  · have ref := disjoint_outputs_refunded S C o y B hlin ho (fun i hi => ⟨(data hi).1,
        by have h := (data hi).2.2; omega⟩)
    have split := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl
      (g:=fun i => k+1+((S i).card-(k+1))) (fun i hi => by have h := (data hi).2.2; omega)
    rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at split
    have eq : B.card*(k+2) = B.card*(k+1)+B.card := by rw [show k+2=(k+1)+1 by omega,Nat.mul_add,Nat.mul_one]
    omega

open L_meta_997_aux
end L_meta_997.Small
namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

-- Trace a disjoint row back from the assignment setting all inputs outside
-- the row to true. At a false AND one false parent suffices. Only OR gates
-- can branch in this trace.
noncomputable def highOrGates {n : ℕ} (C : Circuit) (y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Heavy.heavyG C y T).filter (fun w => ¬andAt C n w)

theorem high_or_count {n : ℕ} (C : Circuit) (y T : Finset (Fin n)) (o t : ℕ)
    (dis : Disjoint y T)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : ∀ x : Fin n → Bool, value C x o=decide (∃ p ∈ T, x p=true))
    (zero : value C (fun _ : Fin n => false) (n+t)=true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false) :
    T.card ≤ (highOrGates C y T).card+1 := by
  classical
  let top := fun p : Fin n => decide (p ∉ T)
  let fire := fun (p q : Fin n) => decide (q ∈ y ∨ q=p)
  let L := fun w => if value C top w=false then Heavy.supp C y w else ∅
  let G := highOrGates C y T
  obtain ⟨D,sz,good,agree⟩ := Heavy.heavy_model C y t hg hu hy
  have above : ∀ p ∈ y, top p=true := fun p hp => decide_eq_true (Finset.disjoint_left.mp dis hp)
  have fireOn p : ∀ a ∈ y, fire p a=true := fun a ha => decide_eq_true (Or.inl ha)
  have sig w : Heavy.supp D y w=Heavy.supp C y w := by
    ext p; rw [Heavy.mem_supp,Heavy.mem_supp,agree (fire p) (fireOn p)]
  have info (w) (c : 2 ≤ (L w).card) : w ∈ Heavy.heavyG C y T ∧ value C top w=false := by
    have off : value C top w=false := by by_contra h; simp [L,h] at c
    have big : 2 ≤ (Heavy.supp C y w).card := by simpa [L,off] using c
    have sound : Heavy.sound D T w := by
      intro x hx
      by_contra! nope
      have le (p) (hp : x p=true) : top p=true := decide_eq_true (fun h => by have he := nope p h; simp [hp] at he)
      have on := value_mono D good x top le w hx
      rw [agree top above,off] at on
      contradiction
    have reg := Heavy.supp_gate D y T w dis sound (sig w ▸ big)
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨reg.1,by rw [←sz]; exact reg.2⟩,?_,big,?_⟩,off⟩
    · intro p hp
      have v := (Heavy.mem_supp D y w p).mp ((sig w).symm ▸ hp)
      obtain ⟨q,hq,h⟩ := sound _ v
      rcases of_decide_eq_true h with hqy | rfl
      · exact (Finset.disjoint_left.mp dis hqy hq).elim
      · exact hq
    · apply Bool.eq_false_iff.mpr
      intro h
      have on := (agree (fun p => decide (p∈y)) (fun _ hp => decide_eq_true hp) w).trans h
      obtain ⟨p,hp,py⟩ := sound _ on
      exact Finset.disjoint_left.mp dis (of_decide_eq_true py) hp
  have zempty := (terminal_switch_closed C y t hg hu zero hy).2
  have step (w) (big : 2 ≤ (L w).card) : ∃ P : Finset ℕ, (∀ r ∈ P, r<w) ∧
      P.card ≤ (if w ∈ G then 2 else 1) ∧ L w ⊆ P.biUnion L := by
    obtain ⟨hw,off⟩ := info w big
    obtain ⟨wr,_,sc,_⟩ := Finset.mem_filter.mp hw
    obtain ⟨lo,up⟩ := Finset.mem_Ico.mp wr
    have ix : w-n<C.gates.length := by change w<n+C.gates.length at up; omega
    let g := C.gates[w-n]
    let read := fun (x : Fin n → Bool) (r : ℕ) => if r<w then value C x r else false
    have ev (x : Fin n → Bool) : value C x w=g.op.eval (g.inputs.map (read x)) := gate_value C x w lo up
    obtain ⟨ops,len⟩ := hg g (List.getElem_mem _)
    rcases ops with hand | hor | hn
    · have all (x : Fin n → Bool) : value C x w=true ↔ ∀ r ∈ g.inputs, read x r=true := by rw [ev,hand]; simp [GateOp.eval]
      have neg : ¬ ∀ r ∈ g.inputs, read top r=true := fun h => Bool.noConfusion (off.symm.trans ((all _).mpr h))
      push Not at neg
      obtain ⟨r,hr,hr0⟩ := neg
      obtain ⟨p,hp⟩ := Finset.card_pos.mp (by omega : 0<(Heavy.supp C y w).card)
      have on := (all _).mp ((Heavy.mem_supp C y w p).mp hp) r hr
      have rw' : r<w := by by_contra h; simp [read,h] at on
      have roff : value C top r=false := by simpa [read,rw'] using hr0
      refine ⟨{r},by simpa using rw',by split <;> simp,?_⟩
      intro a ha
      have hh := (all _).mp ((Heavy.mem_supp C y w a).mp (by simpa [L,off] using ha)) r hr
      have rr := (Heavy.mem_supp C y r a).mpr (by simpa [read,rw'] using hh)
      simpa [L,roff] using rr
    · have any (x : Fin n → Bool) : value C x w=true ↔ ∃ r ∈ g.inputs, read x r=true := by rw [ev,hor]; simp [GateOp.eval]
      let P := g.inputs.toFinset.filter (· < w)
      have wg : w ∈ G := Finset.mem_filter.mpr ⟨hw,by simp [andAt,ix,show C.gates[w-n].op=.or from hor]⟩
      refine ⟨P,fun r hr => (Finset.mem_filter.mp hr).2,?_,?_⟩
      · simpa only [ite_eq_left wg] using (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans len)
      · intro p hp
        obtain ⟨r,hr,hr1⟩ := (any _).mp ((Heavy.mem_supp C y w p).mp (by simpa [L,off] using hp))
        have rw' : r<w := by by_contra h; simp [read,h] at hr1
        have roff : value C top r=false := by
          apply Bool.eq_false_iff.mpr
          intro on
          exact Bool.noConfusion (off.symm.trans ((any top).mpr ⟨r,hr,by simpa [read,rw'] using on⟩))
        refine Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,rw'⟩,?_⟩
        simpa [L,roff] using (Heavy.mem_supp C y r p).mpr (by simpa [read,rw'] using hr1)
    · have e := hu ⟨w-n,ix⟩ hn
      change w-n=t at e
      have eq : w=n+t := by omega
      rw [eq,zempty,Finset.card_empty] at sc
      omega
  have target : L o=T := by
    have off : value C top o=false := by rw [out]; simp [top]
    simp only [L,off,ite_true]
    ext p; rw [Heavy.mem_supp,out]
    constructor
    · intro h
      obtain ⟨q,hq,h⟩ := of_decide_eq_true h
      rcases of_decide_eq_true h with hy' | rfl
      · exact (Finset.disjoint_left.mp dis hy' hq).elim
      · exact hq
    · intro hp; exact decide_eq_true ⟨p,hp,decide_eq_true (Or.inr rfl)⟩
  have res := branching_cover L G step (n+C.size) {o} (fun w _ c =>
    (Finset.mem_Ico.mp (Finset.mem_filter.mp (info w c).1).1).2)
  simp only [Finset.singleton_biUnion,target,Finset.card_singleton] at res
  have cut := Finset.card_filter_le G (· < n+C.size)
  change T.card ≤ G.card+1
  omega

end L_meta_997.Light
namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

-- A row meeting y loses a gate to the upper window only if two or more
-- singleton inputs of that row and two or more upper-window inputs of a
-- different, disjoint row activate the same gate.
noncomputable def highRowGates {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (y : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.univ.filter (fun j => Disjoint y (S j))).biUnion (fun j => highOrGates C y (S j))

def crossingDeficit {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (t : ℕ) (y : Finset (Fin n)) (i : Fin m) : Prop :=
  ¬ Disjoint (S i) y ∧
    (((assigned C (S i)).erase (n+t)) \ highRowGates S C y).card+1 < min y.card (S i).card

open Classical in
theorem crossing_budget {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) + y.card ≤
      C.size + m + ∑ i ∈ Finset.univ.filter (fun i => crossingDeficit S C t y i),
        (min y.card (S i).card-2) := by
  classical
  let H := Finset.univ.filter (fun j => Disjoint y (S j))
  let U := H.biUnion (fun j => highOrGates C y (S j))
  let z := n+t
  let P (i : Fin m) := if Disjoint (S i) y then ∅ else ((assigned C (S i)).erase z) \ U
  let T := Finset.univ.biUnion P
  let X := Finset.univ.filter (fun i => crossingDeficit S C t y i)
  let a (i : Fin m) := if i ∈ H then (S i).card-1 else 0
  let loss (i : Fin m) := if i ∈ X then min y.card (S i).card-2 else 0
  have hzero := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have ucount : (∑ i ∈ H, ((S i).card-1)) ≤ U.card := by
    have pair : (H : Set (Fin m)).PairwiseDisjoint (fun i => highOrGates C y (S i)) := by
      intro i _ j _ ne
      exact (Heavy.heavy_disjoint C y (S i) (S j) (hpair i j ne)).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [show U.card=∑ i ∈ H, (highOrGates C y (S i)).card from Finset.card_biUnion pair]
    apply Finset.sum_le_sum
    intro i hi
    have c := high_or_count C y (S i) (o i) t (Finset.mem_filter.mp hi).2 hg hu (out i) hzero hy
    omega
  have ea : ∑ i, a i = ∑ i ∈ H, ((S i).card-1) := by simp [a]
  have data {w} (hw : w ∈ U) :
      ∃ j, Disjoint y (S j) ∧ w ∈ Heavy.heavyG C y (S j) := by
    obtain ⟨j,hj,hw⟩ := Finset.mem_biUnion.mp hw
    exact ⟨j,(Finset.mem_filter.mp hj).2,(Finset.mem_filter.mp hw).1⟩
  have pd {i w} (hw : w ∈ P i) : w ∈ assigned C (S i) ∧ w ≠ z ∧ w ∉ U := by
    simp only [P] at hw
    split at hw
    · simp at hw
    · have he := Finset.mem_erase.mp (Finset.mem_sdiff.mp hw).1
      exact ⟨he.2,he.1,(Finset.mem_sdiff.mp hw).2⟩
  have tc : T.card=∑ i, (P i).card := by
    apply Finset.card_biUnion
    intro i _ j _ ne
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have li := (Finset.mem_filter.mp (pd hi).1).2
    have lj := (Finset.mem_filter.mp (pd hj).1).2
    have sub : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨li.1 hp,lj.1 hp⟩
    have := (Finset.card_le_card sub).trans (hpair i j ne)
    omega
  obtain ⟨zr,zh⟩ := terminal_switch_closed C y t hg hu hzero hy
  obtain ⟨A,ac,ar,ad⟩ := guard_hot_gates C t y (by omega : 0<y.card) hg hu hl hy
  have du : Disjoint U T := Finset.disjoint_left.mpr (by
    intro w wu wt
    obtain ⟨i,_,wi⟩ := Finset.mem_biUnion.mp wt
    exact (pd wi).2.2 wu)
  have zu : z ∉ U ∪ T := by
    intro h
    rcases Finset.mem_union.mp h with u | v
    · obtain ⟨j,_,wj⟩ := data u
      have c := (Finset.mem_filter.mp wj).2.2.1
      change 2 ≤ (Heavy.supp C y (n+t)).card at c
      rw [zh,Finset.card_empty] at c
      omega
    · obtain ⟨i,_,wi⟩ := Finset.mem_biUnion.mp v
      exact (pd wi).2.1 rfl
  have da : Disjoint A (insert z (U ∪ T)) := Finset.disjoint_left.mpr (by
    intro w wa ww
    rcases Finset.mem_insert.mp ww with rfl | wu
    · exact Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar wa)).2
    rcases Finset.mem_union.mp wu with u | v
    · obtain ⟨j,_,wj⟩ := data u
      exact Bool.noConfusion ((ad w wa).2.symm.trans (Finset.mem_filter.mp wj).2.2.2)
    · obtain ⟨i,_,wi⟩ := Finset.mem_biUnion.mp v
      have c := (Finset.mem_filter.mp (pd wi).1).2.2
      rw [(ad w wa).1,Finset.card_empty] at c
      omega)
  have inside : A ∪ insert z (U ∪ T) ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with wa | ww
    · have ra := Finset.mem_Ico.mp (ar wa)
      exact Finset.mem_Ico.mpr ⟨ra.1,ra.2.trans (Finset.mem_Ico.mp zr).2⟩
    rcases Finset.mem_insert.mp ww with rfl | ww
    · exact zr
    rcases Finset.mem_union.mp ww with u | v
    · obtain ⟨j,_,wj⟩ := data u
      exact (Finset.mem_filter.mp wj).1
    · obtain ⟨i,_,wi⟩ := Finset.mem_biUnion.mp v
      exact (Finset.mem_filter.mp (pd wi).1).1
  have count := Finset.card_le_card inside
  rw [Finset.card_union_of_disjoint da,Finset.card_insert_of_notMem zu,Finset.card_union_of_disjoint du,tc] at count
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left] at count
  have each (i : Fin m) : (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      a i + (P i).card + 1 + loss i := by
    by_cases hd : Disjoint (S i) y
    · have hi : i ∈ H := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.symm⟩
      simp only [hd,ite_true,a,hi]; omega
    have hi : i ∉ H := fun h => hd (Finset.mem_filter.mp h).2.symm
    simp only [hd,ite_false,a,hi]
    by_cases hx : i ∈ X
    · have drop : loss i = min y.card (S i).card-2 := by simp [loss,hx]
      by_cases two : 2 ≤ (S i).card
      swap
      · omega
      have eq : support C (o i) = S i := by ext p; rw [mem_support,out]; simp
      have ass : o i ∈ assigned C (S i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C (o i) (eq.symm ▸ two)),
          eq ▸ Finset.Subset.rfl,eq.symm ▸ two⟩
      have ne : o i ≠ z := by intro h; change o i=n+t at h; rw [← h,out] at hzero; simp at hzero
      have hot : o i ∉ U := by
        intro h
        obtain ⟨j,_,wj⟩ := data h
        obtain ⟨p,hp,hpy⟩ := Finset.not_disjoint_iff.mp hd
        have off := (Finset.mem_filter.mp wj).2.2.2
        rw [out] at off
        exact (of_decide_eq_false off) ⟨p,hp,decide_eq_true hpy⟩
      have op : o i ∈ P i := by simpa only [P,hd,ite_false] using
          (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨ne,ass⟩,hot⟩)
      have := Finset.card_pos.mpr ⟨o i,op⟩
      omega
    · have paid : min y.card (S i).card ≤ ((((assigned C (S i)).erase z) \ U).card+1) := by
        by_contra! short
        exact hx (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd,short⟩)
      simpa [P,hd,loss,hx] using paid
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => each i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at sum
  have e : ∑ i, loss i = ∑ i ∈ X, (min y.card (S i).card-2) := by simp [loss]
  rw [e,ea] at sum
  change _ ≤ C.size + m + ∑ i ∈ X, _
  omega

end L_meta_997.Light
namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

theorem crossing_gate_in_suffix {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (t : ℕ) (y : Finset (Fin n)) (i j : Fin m) (w : ℕ)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : ∀ j : Fin C.gates.length, (C.gates.get j).op = .not → j.val=t)
    (hzero : value C (fun _ : Fin n => false) (n+t)=true)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (ht : ¬Disjoint (S i) y) (hj : Disjoint y (S j))
    (wi : w ∈ assigned C (S i)) (wj : w ∈ Heavy.heavyG C y (S j)) :
    n+t<w ∧
      (support C w \ S j).Nonempty ∧ (Heavy.supp C y w \ S i).Nonempty := by
  classical
  have ne : i ≠ j := fun e => ht (e ▸ hj.symm)
  have ld := (Finset.mem_filter.mp wi).2
  have hd := (Finset.mem_filter.mp wj).2
  have lon : (support C w \ S j).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro sub
    have all : support C w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨ld.1 hp,sub hp⟩
    have := (Finset.card_le_card all).trans (hpair i j ne)
    omega
  have hin : (Heavy.supp C y w \ S i).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro sub
    have all : Heavy.supp C y w ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨sub hp,hd.1 hp⟩
    have := (Finset.card_le_card all).trans (hpair i j ne)
    omega
  refine ⟨?_,lon,hin⟩
  obtain ⟨zr,zh⟩ := terminal_switch_closed C y t hg hu hzero hy
  have late : w ≠ n+t := by
    rintro rfl
    have c := hd.2.1
    rw [zh,Finset.card_empty] at c
    omega
  by_contra! early
  have pre : w<n+t := lt_of_le_of_ne early late
  obtain ⟨p,hp⟩ := lon
  have l := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
  have miss := (Finset.mem_sdiff.mp hp).2
  cases C with
  | mk gs oo =>
    let a : Fin gs.length := ⟨t,by have u := (Finset.mem_Ico.mp zr).2; change n+t<n+gs.length at u; omega⟩
    let x := fun q : Fin n => decide (q=p)
    let y' := fun q : Fin n => decide (q∈y ∨ q=p)
    change value ⟨gs,0⟩ x w=true at l
    rw [prefix_value_eq gs a x w pre] at l
    have mon := value_mono ⟨gs.take a.val,0⟩ (pre_basis gs a hg (fun b e => Fin.ext (hu b e)))
      x y' (fun q h => decide_eq_true (Or.inr (of_decide_eq_true h))) w l
    rw [←prefix_value_eq gs a y' w pre] at mon
    exact miss (hd.1 ((Heavy.mem_supp ⟨gs,oo⟩ y w p).mpr mon))

end L_meta_997.Light
namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux
open Classical in
theorem three_crossing_rows {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : y.card=3)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length+(refunds S C y).card+m)) :
    (refunds S C y).card+4 ≤ (Finset.univ.filter (crossingDeficit S C t y)).card := by
  classical
  have ledger := crossing_budget S C o t y (by omega) hpair hg hu out hl hy
  let X := Finset.univ.filter (crossingDeficit S C t y)
  have le := Finset.sum_le_sum (s:=X) (g:=fun _ => 1) (fun i _ => show min y.card (S i).card-2 ≤ 1 by omega)
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at le
  change _+y.card ≤ C.size+m+∑ i ∈ X, (min y.card (S i).card-2) at ledger
  change ¬(_ ≤ C.size+(refunds S C y).card+m) at bad
  change _ ≤ X.card
  omega

theorem three_crossing_gate {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : y.card=3)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (i : Fin m) (hi : crossingDeficit S C t y i) :
    3 ≤ (S i).card ∧
      (((assigned C (S i)).erase (n+t)).erase (o i)).Nonempty ∧
      ∀ w ∈ ((assigned C (S i)).erase (n+t)).erase (o i), n+t<w ∧
        ∃ j, Disjoint y (S j) ∧ w ∈ highOrGates C y (S j) ∧
          (support C w \ S j).Nonempty ∧ (Heavy.supp C y w \ S i).Nonempty := by
  classical
  let P := (assigned C (S i)).erase (n+t)
  let U := highRowGates S C y
  obtain ⟨ht,short⟩ := hi
  change (P \ U).card+1 < min y.card (S i).card at short
  have two : 2 ≤ (S i).card := by omega
  have eq : support C (o i) = S i := by ext p; rw [mem_support,out]; simp
  have ass : o i ∈ assigned C (S i) := Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr (support_gate C (o i) (eq.symm ▸ two)),eq ▸ Finset.Subset.rfl,eq.symm ▸ two⟩
  have hz := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have ne : o i ≠ n+t := by intro h; rw [←h,out] at hz; simp at hz
  have op : o i ∈ P := Finset.mem_erase.mpr ⟨ne,ass⟩
  have ou : o i ∉ U := by
    intro u
    obtain ⟨j,_,wj⟩ := Finset.mem_biUnion.mp u
    obtain ⟨p,hp,hpy⟩ := Finset.not_disjoint_iff.mp ht
    have off := (Finset.mem_filter.mp (Finset.mem_filter.mp wj).1).2.2.2
    rw [out] at off
    exact (of_decide_eq_false off) ⟨p,hp,decide_eq_true hpy⟩
  have oo : o i ∈ P \ U := Finset.mem_sdiff.mpr ⟨op,ou⟩
  have pos := Finset.card_pos.mpr ⟨o i,oo⟩
  have large : 3 ≤ (S i).card := by omega
  have pay := card_light_erase_switch (S i) C (o i) t (by omega : 2≤y.card) hg hu (out i) hl
  change min y.card (S i).card ≤ P.card+1 at pay
  have pc := Finset.card_erase_add_one op
  refine ⟨large,Finset.card_pos.mp (show 0<(P.erase (o i)).card by omega),?_⟩
  intro w hw
  obtain ⟨wo,wp⟩ := Finset.mem_erase.mp hw
  have wu : w ∈ U := by
    by_contra h
    have sub : {w,o i} ⊆ P \ U := Finset.insert_subset (Finset.mem_sdiff.mpr ⟨wp,h⟩) (Finset.singleton_subset_iff.mpr oo)
    have c := Finset.card_le_card sub
    simp [wo] at c
    omega
  obtain ⟨j,hj,wj⟩ := Finset.mem_biUnion.mp wu
  have dis := (Finset.mem_filter.mp hj).2
  obtain ⟨later,lp,hp⟩ := crossing_gate_in_suffix S C t y i j w hpair hg hu hz hy ht dis (Finset.mem_erase.mp wp).2 (Finset.mem_filter.mp wj).1
  exact ⟨later,j,dis,wj,lp,hp⟩

end L_meta_997.Light
namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

-- The upper-window trace uses no AND. Whenever a touching row has too
-- few private gates outside that trace, it was fully paid on singletons.
theorem crossing_paid {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (i : Fin m) (hi : crossingDeficit S C t y i) :
    (S i).card ≤ (assigned C (S i)).card+1 := by
  classical
  by_contra! short
  have kcount := low_many_private_ands C (S i) (o i) t hk hg hu (out i) hl short
  let A := (assigned C (S i)).filter (andAt C n)
  let P := ((assigned C (S i)).erase (n+t)) \ highRowGates S C y
  have hz := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have zn : ¬andAt C n (n+t) := by
    intro andZ
    have goodC : good C := by
      intro g mem
      obtain ⟨ops,len⟩ := hg g mem
      refine ⟨?_,len⟩
      rcases ops with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨j,jb,eq⟩ := List.mem_iff_getElem.mp mem
        have op : C.gates[j].op=.not := eq ▸ h
        have jt := hu ⟨j,jb⟩ op
        change j=t at jt
        subst j
        simp [andAt,jb,op] at andZ
    have on := value_mono C goodC (fun _ : Fin n => false) (fun p => decide (p∈y)) (by simp) (n+t) hz
    exact Bool.noConfusion (hy.symm.trans on)
  have sub : A ⊆ P := by
    intro w hw
    have aw := Finset.mem_filter.mp hw
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨fun he => zn (he ▸ aw.2),aw.1⟩,?_⟩
    rintro h
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp hj).2 aw.2
  have cut := Finset.card_le_card sub
  have cost := hi.2
  change P.card+1 < min y.card (S i).card at cost
  change y.card ≤ A.card+1 at kcount
  omega

end L_meta_997.Light



namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

lemma crossing_parent_signatures {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o t w : ℕ) (y : Finset (Fin n)) (i j : Fin m) (A F : Finset ℕ)
    (hT : (S i).card = 3)
    (hA : ∀ r ∈ A, value C (fun p => decide (p ∈ y)) r = true)
    (roles : ∀ r ∈ Finset.Ico n (n+C.size), r ≠ n+t → r ∉ A → r ∉ F →
        (∃ a, r ∈ assigned C (S a) ∧ (a ∈ underDisjoint C S y → andAt C n r)) ∨
        (∃ a ∈ underDisjoint C S y, ¬andAt C n r ∧ S a ⊆ support C r ∧ Heavy.supp C y r = S a))
    (hg : hasAllowedGates C)
    (hu : ∀ a : Fin C.gates.length, (C.gates.get a).op = .not → (a : ℕ) = t)
    (hsw : ∀ p : Fin n, p ∈ support C (n+t))
    (hwa : n+t < w) (hwo : w < o) (hasg : assigned C (S i) = {w,o})
    (hw : w ∈ highOrGates C y (S j)) (hout : (support C w \ S j).Nonempty) :
    ∃ (u v : ℕ) (p r : Fin n), u ∈ F ∧ u ≠ v ∧ p ≠ r ∧
      support C u = {p} ∧ support C v = {r} ∧ p ∉ Heavy.supp C y u ∧
      value C (fun a => decide (a ∈ y)) u = false ∧
      value C (fun a => decide (a ∈ y)) v = false ∧
      support C w = {p,r} ∧ Heavy.supp C y w = Heavy.supp C y u ∪ Heavy.supp C y v ∧
      ((Heavy.supp C y u = ∅) → v ∈ F) := by
  classical
  have hwi : w ∈ assigned C (S i) := by simp [hasg]
  obtain ⟨_, hws, hwc⟩ := Finset.mem_filter.mp hwi
  obtain ⟨hhigh, hnand⟩ := Finset.mem_filter.mp hw
  obtain ⟨hrange,hupper,hhighCard,hcold⟩ := Finset.mem_filter.mp hhigh
  obtain ⟨hn,hnw⟩ := Finset.mem_Ico.mp hrange
  have hidx : w-n < C.gates.length := by change w<n+C.gates.length at hnw; omega
  let g := C.gates[w-n]
  obtain ⟨hop, hlen⟩ := hg g (List.getElem_mem _)
  have hor : g.op = .or := by
    rcases hop with ha | ho | hz
    · exact (hnand (by simp [andAt, g, hidx, ha])).elim
    · exact ho
    · have e := hu ⟨w-n,hidx⟩ hz
      change w-n=t at e
      omega
  have read (x : Fin n → Bool) :
      value C x w = true ↔ ∃ v ∈ g.inputs, v < w ∧ value C x v = true := by
    rw [gate_value C x w hn hnw]
    change g.op.eval (g.inputs.map (fun v => if v<w then value C x v else false)) = true ↔ _
    simp [hor, GateOp.eval]
  have parentSub (v : ℕ) (_hv : v ∈ g.inputs) (hv' : v < w) : support (n:=n) C v ⊆ support C w := by
    intro p hp
    exact (mem_support C w p).mpr ((read _).mpr ⟨v,_hv,hv',(mem_support C v p).mp hp⟩)
  have parentCold (v : ℕ) (hv : v ∈ g.inputs) (hv' : v < w) :
      value C (fun a => decide (a ∈ y)) v = false := by
    apply Bool.eq_false_iff.mpr
    intro hot
    have won := (read _).mpr ⟨v,hv,hv',hot⟩
    rw [hcold] at won
    contradiction
  have parentCard (v : ℕ) (hv : v ∈ g.inputs) (hv' : v < w) :
      (support (n:=n) C v).card ≤ 1 := by
    by_contra! big
    have ass : v ∈ assigned C (S i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C v big), (parentSub v hv hv').trans hws, big⟩
    rw [hasg] at ass
    rcases (by simpa using ass : v=w ∨ v=o) with e | e <;> omega
  have parentExc (v : ℕ) (hv : v ∈ g.inputs) (hv' : v < w) (hnv : n ≤ v) : v ∈ F := by
    by_contra hf
    have ha : v ∉ A := by
      intro ha
      have e := hA v ha
      rw [parentCold v hv hv'] at e
      contradiction
    have hc := parentCard v hv hv'
    have hz : v ≠ n+t := by
      intro eq
      have ht : 3 ≤ n := by simpa [hT] using (Finset.card_le_univ (S i))
      have hcu : (support (n:=n) C v).card = n := by
        rw [eq, Finset.eq_univ_of_forall hsw]
        simp
      omega
    rcases roles v (Finset.mem_Ico.mpr ⟨hnv, by omega⟩) hz ha hf with ⟨a,has,_⟩ | ⟨a,ha',_,hsa,_⟩
    · have big := (Finset.mem_filter.mp has).2.2
      omega
    · have lt := (Finset.mem_filter.mp (Finset.mem_filter.mp ha').1).2
      have le := Finset.card_le_card hsa
      omega
  obtain ⟨q,hq⟩ := hout
  obtain ⟨u,hug,huw,huq⟩ := (read _).mp ((mem_support C w q).mp (Finset.mem_sdiff.mp hq).1)
  have hnu : n ≤ u := by
    by_contra! hun
    let raw : Fin n := ⟨u,hun⟩
    have eq : raw=q := by
      change value C (fun p => decide (p=q)) raw = true at huq
      simpa [input_value] using huq
    have up : value C (fun p => decide (p ∈ y ∨ p=q)) u = true := by
      change value C (fun p => decide (p ∈ y ∨ p=q)) raw = true
      simp [input_value,eq]
    have hin := hupper ((Heavy.mem_supp C y w q).mpr ((read _).mpr ⟨u,hug,huw,up⟩))
    exact (Finset.mem_sdiff.mp hq).2 hin
  have huF := parentExc u hug huw hnu
  have huSupp : support C u = {q} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr ((mem_support C u q).mpr huq))
    simpa using parentCard u hug huw
  have less : ({q} : Finset (Fin n)).card < (support (n:=n) C w).card := by simp; omega
  obtain ⟨r,hrw,hrq⟩ := Finset.exists_mem_notMem_of_card_lt_card less
  obtain ⟨v,hvg,hvw,hvr⟩ := (read _).mp ((mem_support C w r).mp hrw)
  have hvu : v ≠ u := by
    intro e
    exact hrq (huSupp ▸ (mem_support C u r).mpr (e ▸ hvr))
  have hrs : support C v = {r} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr ((mem_support C v r).mpr hvr))
    simpa using parentCard v hvg hvw
  have hpair : ∀ b ∈ g.inputs, b=u ∨ b=v := by
    intro b hb
    have sub : ({u,v,b} : Finset ℕ) ⊆ g.inputs.toFinset := by
      refine Finset.insert_subset (List.mem_toFinset.mpr hug)
        (Finset.insert_subset (List.mem_toFinset.mpr hvg)
          (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hb)))
    have cap := (Finset.card_le_card sub).trans ((List.toFinset_card_le g.inputs).trans hlen)
    by_contra! h
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] at cap
    · omega
    · simpa using Ne.symm h.2
    · simp [hvu.symm, h.1.symm]
  have eqHigh : Heavy.supp C y w = Heavy.supp C y u ∪ Heavy.supp C y v := by
    ext a
    rw [Heavy.mem_supp, read, Finset.mem_union, Heavy.mem_supp, Heavy.mem_supp]
    constructor
    · rintro ⟨b,hb,bl,hba⟩
      rcases hpair b hb with rfl | rfl
      · exact Or.inl hba
      · exact Or.inr hba
    · rintro (h | h)
      · exact ⟨u,hug,huw,h⟩
      · exact ⟨v,hvg,hvw,h⟩
  have loss : q ∉ Heavy.supp C y u := by
    intro hon
    have hon' : q ∈ Heavy.supp C y w := eqHigh.symm ▸ Finset.mem_union.mpr (Or.inl hon)
    exact (Finset.mem_sdiff.mp hq).2 (hupper hon')
  have coldv := parentCold v hvg hvw
  have hvF (empty : Heavy.supp C y u = ∅) : v ∈ F := by
    by_cases bg : n ≤ v
    · exact parentExc v hvg hvw bg
    have rawLt : v < n := by omega
    let raw : Fin n := ⟨v,rawLt⟩
    have notY : raw ∉ y := by
      intro hi
      change value C (fun a => decide (a ∈ y)) raw = false at coldv
      rw [input_value] at coldv
      simp [hi] at coldv
    have sig : Heavy.supp C y v = {raw} := by
      ext a
      rw [Heavy.mem_supp]
      change value C (fun p => decide (p ∈ y ∨ p=a)) raw = true ↔ _
      rw [input_value]
      simp [notY, eq_comm]
    rw [eqHigh,empty,Finset.empty_union,sig,Finset.card_singleton] at hhighCard
    omega
  refine ⟨u,v,q,r,huF,hvu.symm,by simpa [eq_comm] using hrq,huSupp,hrs,loss,parentCold u hug huw,coldv,?_,eqHigh,hvF⟩
  ext a
  rw [mem_support, read]
  constructor
  · rintro ⟨b,hb,bl,hba⟩
    rcases hpair b hb with e | e
    · subst b
      have h : a ∈ support C u := (mem_support C u a).mpr hba
      rw [huSupp] at h
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))
    · subst b
      have h : a ∈ support C v := (mem_support C v a).mpr hba
      rw [hrs] at h
      exact Finset.mem_insert_of_mem h
  · intro h
    rcases Finset.mem_insert.mp h with eq | hr
    · subst a
      exact ⟨u,hug,huw,huq⟩
    · simp only [Finset.mem_singleton] at hr
      subst a
      exact ⟨v,hvg,hvw,hvr⟩


end L_meta_997.Small


namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

lemma crossing_output_roles {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (i : Fin m) (y : Finset (Fin n)) (t w o : ℕ) (A F : Finset ℕ) (p r : Fin n)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hlin : rowLinearity S)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ q ∈ S i, x q = true))
    (htouch : ¬Disjoint (S i) y) (hthree : (S i).card = 3)
    (hw_before : n+t < w ∧ w < o)
    (hassigned : assigned C (S i) = {w,o})
    (hsw : support C w = {p,r}) (hpr : p ≠ r)
    (hw_cold : value C (fun q => decide (q ∈ y)) w = false)
    (hz_cold : value C (fun q => decide (q ∈ y)) (n+t) = false)
    (hz_full : ∀ q : Fin n, q ∈ support C (n+t))
    (hA : ∀ v ∈ A, support (n:=n) C v = ∅)
    (hroles : ∀ v ∈ Finset.Ico n (n+C.size), v ≠ n+t → v ∉ A → v ∉ F →
      (∃ j, v ∈ assigned C (S j) ∧ (j ∈ underDisjoint C S y → andAt C n v)) ∨
      (∃ j ∈ underDisjoint C S y, ¬andAt C n v ∧ S j ⊆ support C v ∧ Heavy.supp C y v = S j)) :
    (∃ a ∈ F, ∃ b ∈ F, a ≠ b ∧ value C (fun q => decide (q ∈ y)) a = true ∧
      value C (fun q => decide (q ∈ y)) b = true ∧ S i = support C a ∩ support C b) ∨
    (∃ s ∈ S i, s ≠ p ∧ (s ∈ y ∨ ∃ v ∈ F, support C v = {s} ∧
      value C (fun q => decide (q ∈ y)) v = true)) := by
  classical
  have hso : support C o = S i := by ext q; rw [mem_support,hout]; simp
  have hww : w ∈ assigned C (S i) := hassigned.symm ▸ Finset.mem_insert_self _ _
  have hws : support C w ⊆ S i := (Finset.mem_filter.mp hww).2.1
  have hp : p ∈ S i := hws (hsw.symm ▸ Finset.mem_insert_self _ _)
  have hr : r ∈ S i := hws (hsw.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨q,hqi,hqy⟩ := Finset.not_disjoint_iff.mp htouch
  let χ : Fin n → Bool := fun q => decide (q ∈ y)
  have hot : value C χ o = true := by
    rw [hout]; exact decide_eq_true ⟨q,hqi,decide_eq_true hqy⟩
  obtain ⟨hon,horange⟩ := support_gate C o (by rw [hso,hthree]; decide)
  have hidx : o-n < C.gates.length := by change o<n+C.gates.length at horange; omega
  let g := C.gates[o-n]
  obtain ⟨hop,hlen⟩ := hg g (List.getElem_mem _)
  let read (x : Fin n → Bool) (v : ℕ) := if v < o then value C x v else false
  have eqv (x : Fin n → Bool) : value C x o = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x o hon horange
  have to_w (v : ℕ) (less : v < o) (sub : support C v ⊆ S i)
      (large : 2 ≤ (support (n:=n) C v).card) : v = w := by
    have ass : v ∈ assigned C (S i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C v large),sub,large⟩
    rw [hassigned] at ass
    simpa [show v ≠ o by omega] using ass
  have terminal_cold (v : ℕ) (j : Fin m) (hj : j ∈ underDisjoint C S y)
      (signature : Heavy.supp C y v = S j) : value C χ v ≠ true := by
    intro hv
    have hd : Disjoint (S j) y := (Finset.mem_filter.mp hj).2
    have e : (fun z : Fin n => decide (z ∈ y ∨ z = q)) = χ := by
      funext z
      by_cases hz : z = q
      · subst z; simp [χ,hqy]
      · simp [χ,hz]
    exact (Finset.disjoint_left.mp hd) (signature ▸ (Heavy.mem_supp C y v q).mpr (e.symm ▸ hv)) hqy
  rcases hop with hand | hor | hnot
  · have hall (x : Fin n → Bool) : value C x o = true ↔ ∀ v ∈ g.inputs, read x v = true := by
      rw [eqv x,hand]; simp [GateOp.eval]
    have hzero : value C (fun _ : Fin n => false) o = false := by rw [hout]; simp
    have hex : g.inputs ≠ [] := by
      intro hnil
      rw [eqv _, hnil, hand] at hzero
      simp [GateOp.eval] at hzero
    have gates_in_F (v : ℕ) (hv : v ∈ g.inputs) :
        v ∈ F ∧ v < o ∧ value C χ v = true ∧ S i ⊆ support C v := by
      have vhot := (hall χ).mp hot v hv
      have vlt : v < o := by by_contra h; simp [read,h] at vhot
      have vhot' : value C χ v = true := by simpa [read,vlt] using vhot
      have vsub : S i ⊆ support C v := by
        intro a ha
        apply (mem_support _ _ _).mpr
        have good := (mem_support C o a).mp (hso.symm ▸ ha)
        simpa [read,vlt] using (hall _).mp good v hv
      refine ⟨?_,vlt,vhot',vsub⟩
      by_contra vF
      have vl := Finset.card_le_card vsub
      have vlarge : 2 ≤ (support (n:=n) C v).card := by omega
      have vrange := Finset.mem_Ico.mpr (support_gate C v vlarge)
      have vne : v ≠ n+t := by
        intro e; exact Bool.noConfusion (hz_cold.symm.trans (e ▸ vhot'))
      have vA : v ∉ A := by
        intro h; rw [hA _ h] at vlarge; simp at vlarge
      rcases hroles v vrange vne vA vF with ⟨j,hj,_⟩ | ⟨j,hj,_,_,hsg⟩
      · have vsub' : support C v ⊆ S j := (Finset.mem_filter.mp hj).2.1
        have j_eq : i = j := by
          by_contra h
          have hinc : S i ⊆ S i ∩ S j :=
            fun a ha => Finset.mem_inter.mpr ⟨ha,vsub' (vsub ha)⟩
          have hcard := (Finset.card_le_card hinc).trans (hlin i j h)
          omega
        subst j
        have ve := to_w v vlt vsub' vlarge
        exact Bool.noConfusion (hw_cold.symm.trans (ve ▸ vhot'))
      · exact terminal_cold v j hj hsg vhot'
    left
    obtain ⟨a,ha⟩ := List.exists_mem_of_ne_nil _ hex
    obtain ⟨aF,ao,ahot,asub⟩ := gates_in_F a ha
    have hdist : ∃ b ∈ g.inputs, a ≠ b := by
      by_contra! hsame
      have eq : support C a = S i := by
        refine Finset.Subset.antisymm ?_ asub
        intro q hq
        rw [←hso,mem_support,hall]
        intro b hb
        have e := hsame b hb
        rw [←e]
        simpa [read,ao] using (mem_support C a q).mp hq
      have v := to_w a ao eq.le (by rw [eq,hthree]; decide)
      exact Bool.noConfusion (hw_cold.symm.trans (v ▸ ahot))
    obtain ⟨b,hb,hab⟩ := hdist
    obtain ⟨bF,bo,bhot,bsub⟩ := gates_in_F b hb
    let P := g.inputs.toFinset
    have Pbound : P.card ≤ 2 := (List.toFinset_card_le g.inputs).trans hlen
    have pair : P = {a,b} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl|rfl
        · simpa [P] using ha
        · simpa [P] using hb
      · simpa [Finset.card_pair hab] using Pbound
    refine ⟨a,aF,b,bF,hab,ahot,bhot,Finset.Subset.antisymm ?_ ?_⟩
    · intro q hq; exact Finset.mem_inter.mpr ⟨asub hq,bsub hq⟩
    · intro q hq
      obtain ⟨hqa,hqb⟩ := Finset.mem_inter.mp hq
      rw [←hso,mem_support,hall]
      intro v hv
      have vP : v ∈ P := by simpa [P] using hv
      rw [pair] at vP
      simp only [Finset.mem_insert,Finset.mem_singleton] at vP
      rcases vP with e|e
      · rw [e]; simpa [read,ao] using (mem_support C a q).mp hqa
      · rw [e]; simpa [read,bo] using (mem_support C b q).mp hqb
  · have hany (x : Fin n → Bool) : value C x o = true ↔ ∃ v ∈ g.inputs, read x v = true := by
      rw [eqv x,hor]; simp [GateOp.eval]
    let P := g.inputs.toFinset.filter (· < o)
    have Pbound : P.card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen)
    have Pmem {v} : v ∈ P ↔ v ∈ g.inputs ∧ v < o := by simp [P]
    have support_parent {v} (hv : v ∈ P) : support C v ⊆ S i := by
      intro a ha
      have data := Pmem.mp hv
      rw [←hso,mem_support,hany]
      exact ⟨v,data.1, by simpa [read,data.2] using (mem_support C v a).mp ha⟩
    have covered (a) (ha : a ∈ S i) : ∃ v ∈ P, a ∈ support C v := by
      obtain ⟨v,hv,honv⟩ := (hany _).mp ((mem_support C o a).mp (hso.symm ▸ ha))
      have vo : v<o := by by_contra h; simp [read,h] at honv
      exact ⟨v,Pmem.mpr ⟨hv,vo⟩,(mem_support _ _ _).mpr (by simpa [read,vo] using honv)⟩
    have sc : ({p,r} : Finset (Fin n)).card < (S i).card := by rw [Finset.card_pair hpr,hthree]; decide
    obtain ⟨s,hsi,hsout⟩ := Finset.exists_mem_notMem_of_card_lt_card sc
    have hsp : s ≠ p := fun e => hsout (e ▸ Finset.mem_insert_self _ _)
    have hsr : s ≠ r := fun e => hsout (e ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    obtain ⟨v,hv,hsv⟩ := covered s hsi
    have hvw : v ≠ w := by intro e; exact hsout (hsw ▸ e ▸ hsv)
    have vlt := (Pmem.mp hv).2
    have vsmall : (support (n:=n) C v).card ≤ 1 := by
      by_contra! big; exact hvw (to_w v vlt (support_parent hv) (by omega))
    have vne : v ≠ n+t := by
      intro e
      have inc : S i ⊆ support C v := fun a _ => e.symm ▸ hz_full a
      have := Finset.card_le_card inc
      omega
    have vA : v ∉ A := by intro h; rw [hA _ h] at hsv; simp at hsv
    have vraw : support C v = {s} :=
      Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hsv) (by simpa using vsmall) |>.symm
    obtain ⟨vp,hvp,hpvp⟩ := covered p hp
    obtain ⟨vr,hvr,hrvr⟩ := covered r hr
    have hpn : vp ≠ v := by
      intro e; rw [e,vraw] at hpvp
      exact hsp (Finset.mem_singleton.mp hpvp).symm
    have hrn : vr ≠ v := by
      intro e; rw [e,vraw] at hrvr
      exact hsr (Finset.mem_singleton.mp hrvr).symm
    have hvpr : vp = vr := by
      by_contra h
      have sub : ({vp,vr,v} : Finset ℕ) ⊆ P := by
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl|rfl
        exacts [hvp,hvr,hv]
      have hc := Finset.card_le_card sub
      rw [Finset.card_triple_eq_three_iff.mpr ⟨h,hpn,hrn⟩] at hc
      omega
    have hbig : 2 ≤ (support (n:=n) C vp).card := by
      have sub : ({p,r} : Finset (Fin n)) ⊆ support C vp := by
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl
        exacts [hpvp,hvpr.symm ▸ hrvr]
      simpa [Finset.card_pair hpr] using Finset.card_le_card sub
    have vpw := to_w vp (Pmem.mp hvp).2 (support_parent hvp) hbig
    have hwm : w ∈ P := vpw ▸ hvp
    have pair : P = {w,v} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl
        exacts [hwm,hv]
      · simpa [Finset.card_pair hvw.symm] using Pbound
    obtain ⟨a,ha,hya⟩ := (hany χ).mp hot
    have ha_lt : a < o := by by_contra h; simp [read,h] at hya
    have ha_support : a ∈ P := Pmem.mpr ⟨ha,ha_lt⟩
    rw [pair] at ha_support
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha_support
    have hya' : value C χ a = true := by simpa [read,ha_lt] using hya
    rcases ha_support with e|e
    · exact Bool.noConfusion (hw_cold.symm.trans (e ▸ hya'))
    · rw [e] at hya'
      right
      refine ⟨s,hsi,hsp,?_⟩
      by_cases hf : v ∈ F
      · exact Or.inr ⟨v,hf,vraw,hya'⟩
      · have vinput : v < n := by
          by_contra! hlo
          have vrange : v ∈ Finset.Ico n (n+C.size) :=
            Finset.mem_Ico.mpr ⟨hlo,vlt.trans horange⟩
          rcases hroles v vrange vne vA hf with ⟨j,hj,_⟩ | ⟨j,hj,_,hsub,_⟩
          · have big := (Finset.mem_filter.mp hj).2.2
            omega
          · have a := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
            have b := Finset.card_le_card hsub
            omega
        let a : Fin n := ⟨v,vinput⟩
        have on : value C (fun z : Fin n => decide (z = s)) a = true := (mem_support C v s).mp hsv
        rw [input_value] at on
        have vi : v = (s : ℕ) := congrArg Fin.val (of_decide_eq_true on)
        rw [vi,input_value] at hya'
        exact Or.inl (of_decide_eq_true hya')
  · have e := hu ⟨o-n,hidx⟩ hnot
    change o-n=t at e
    omega


end L_meta_997.Small



namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

def touchingCredit {n : ℕ} (C : Circuit) (t : ℕ) (y T : Finset (Fin n)) : ℕ :=
  if Disjoint T y then 0 else ((assigned C T).erase (n+t)).card+1-min y.card T.card

open Classical in
theorem combined_ordered_gate_reserve {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (bad : ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m))
    (A : Finset ℕ) (ar : A ⊆ Finset.Ico n (n+C.size)) (az : n+t ∉ A)
    (ap : ∀ w ∈ A, ∀ i, w ∈ assigned C (S i) → i ∈ underDisjoint C S y ∧ ¬andAt C n w)
    (af : ∀ w ∈ A, ∀ i ∈ underDisjoint C S y, ¬andAt C n w → S i ⊆ support C w →
        value C (fun p => decide (p ∉ S i)) w = false → w ≤ o i → Heavy.supp C y w ≠ S i) :
    (refunds S C y).card + (∑ i : Fin m, touchingCredit C t y (S i)) + A.card + 2 ≤
        ∑ i ∈ underDisjoint C S y, ((S i).card-(y.card+1)) := by
  classical
  have h := low_budget_with_ordered_gate_set C y t S o hk
    (Finset.card_pos.mp (by omega)) hg hu hl hy hlin ho (fun i => touchingCredit C t y (S i))
    (fun i hi => by simp [touchingCredit,hi])
    (fun i hi => by
      have c := card_light_erase_switch (S i) C (o i) t hk hg hu (ho i) hl
      simp only [touchingCredit,ite_eq_right hi]; omega)
    A ar az ap af (by
      intro i hi
      obtain ⟨hi',hd⟩ := Finset.mem_filter.mp hi
      have small := (Finset.mem_filter.mp hi').2
      obtain ⟨w,hr,op,l,sig,wz,cold,wo⟩ := terminal_or_ordered C y (S i) (o i) t (by omega) hd hg hu (ho i)
        (hl (fun _ => false) (by simpa using (show 0<y.card by omega))) hy
      exact ⟨w,hr,wz,op,l,sig,cold,wo⟩)
  omega

open Classical in
theorem combined_ordered_gate_roles {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (bad : ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m))
    :
    ∃ A F : Finset ℕ, y.card ≤ A.card+1 ∧ (refunds S C y).card + (∑ i : Fin m, touchingCredit C t y (S i)) + F.card + y.card + 1 ≤
        (∑ i ∈ underDisjoint C S y, ((S i).card-(y.card+1))) ∧ Disjoint A F ∧
      A ⊆ Finset.Ico n (n+t) ∧ (∀ w ∈ A, support (n:=n) C w=∅ ∧ value C (fun p => decide (p ∈ y)) w=true) ∧
      ∀ w ∈ Finset.Ico n (n+C.size), w ≠ n+t → w ∉ A → w ∉ F →
        (∃ i, w ∈ assigned C (S i) ∧ (i ∈ underDisjoint C S y → andAt C n w)) ∨
        (∃ i ∈ underDisjoint C S y, ¬andAt C n w ∧ S i ⊆ support C w ∧
          L_meta_997_aux.Heavy.supp C y w = S i ∧ value C (fun p => decide (p ∉ S i)) w = false ∧ w ≤ o i) := by
  classical
  obtain ⟨A,ac,ar,ad⟩ := guard_hot_gates C t y (by omega : 0<y.card) hg hu hl hy
  let role (w : ℕ) := (∃ i, w ∈ assigned C (S i) ∧ (i ∈ underDisjoint C S y → andAt C n w)) ∨
    ∃ i ∈ underDisjoint C S y, ¬andAt C n w ∧ S i ⊆ support C w ∧ Heavy.supp C y w=S i ∧
      value C (fun p => decide (p ∉ S i)) w = false ∧ w ≤ o i
  let F := (Finset.Ico n (n+C.size)).filter (fun w => w≠n+t ∧ w ∉ A ∧ ¬role w)
  have sep : Disjoint A F := Finset.disjoint_left.mpr (fun w wa wf => (Finset.mem_filter.mp wf).2.2.1 wa)
  have hz := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have zr : n+t<n+C.size := by
    by_contra! h
    exact Bool.noConfusion ((missing_value C (fun _ : Fin n => false) _ h).symm.trans hz)
  have cap := combined_ordered_gate_reserve S C o t y hk hlin hg hu ho hl hy bad (A ∪ F)
    (Finset.union_subset (fun w hw => Finset.mem_Ico.mpr
      ⟨(Finset.mem_Ico.mp (ar hw)).1,(Finset.mem_Ico.mp (ar hw)).2.trans zr⟩) (Finset.filter_subset _ _))
    (by intro h; rcases Finset.mem_union.mp h with h | h
        · exact Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar h)).2
        · exact (Finset.mem_filter.mp h).2.1 rfl)
    (by
      intro w hw i wi
      rcases Finset.mem_union.mp hw with wa | wf
      · have c := (Finset.mem_filter.mp wi).2.2
        rw [(ad w wa).1,Finset.card_empty] at c
        omega
      · by_contra h
        apply (Finset.mem_filter.mp wf).2.2.2
        exact Or.inl ⟨i,wi,fun hd => by by_contra hand; exact h ⟨hd,hand⟩⟩)
    (by
      intro w hw i hi op sub cold wo eq
      rcases Finset.mem_union.mp hw with wa | wf
      · have c := Finset.card_le_card sub
        rw [(ad w wa).1,Finset.card_empty] at c
        have sh := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
        omega
      · exact (Finset.mem_filter.mp wf).2.2.2 (Or.inr ⟨i,hi,op,sub,eq,cold,wo⟩))
  rw [Finset.card_union_of_disjoint sep] at cap
  refine ⟨A,F,by omega,by omega,sep,ar,ad,?_⟩
  intro w wr wz wa wf
  by_contra h
  exact wf (Finset.mem_filter.mpr ⟨wr,wz,wa,h⟩)


open Classical in
theorem combined_gate_roles {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (bad : ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m))
    :
    ∃ A F : Finset ℕ, y.card ≤ A.card+1 ∧ (refunds S C y).card + (∑ i : Fin m, touchingCredit C t y (S i)) + F.card + y.card + 1 ≤
        (∑ i ∈ underDisjoint C S y, ((S i).card-(y.card+1))) ∧ Disjoint A F ∧
      A ⊆ Finset.Ico n (n+t) ∧ (∀ w ∈ A, support (n:=n) C w=∅ ∧ value C (fun p => decide (p ∈ y)) w=true) ∧
      ∀ w ∈ Finset.Ico n (n+C.size), w ≠ n+t → w ∉ A → w ∉ F →
        (∃ i, w ∈ assigned C (S i) ∧ (i ∈ underDisjoint C S y → andAt C n w)) ∨
        (∃ i ∈ underDisjoint C S y, ¬andAt C n w ∧ S i ⊆ support C w ∧
          L_meta_997_aux.Heavy.supp C y w = S i) := by
  obtain ⟨A,F,ac,cap,sep,ar,ad,roles⟩ :=
    combined_ordered_gate_roles S C o t y hk hlin hg hu ho hl hy bad
  refine ⟨A,F,ac,cap,sep,ar,ad,?_⟩
  intro w wr wz wa wf
  rcases roles w wr wz wa wf with own | ⟨i,hi,op,sub,sig,_,_⟩
  · exact Or.inl own
  · exact Or.inr ⟨i,hi,op,sub,sig⟩

open Classical in
theorem regular_crossing_triples {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : y.card=3)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (bad : ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m))
    :
    ∃ E : Finset (Fin m), (refunds S C y).card+4 ≤ E.card + (∑ i : Fin m, touchingCredit C t y (S i)) ∧
      ∀ i ∈ E, ¬ Disjoint (S i) y ∧ (S i).card=3 ∧ ∃ w j,
        n+t<w ∧ w<o i ∧ assigned C (S i)={w,o i} ∧ Disjoint y (S j) ∧
        w ∈ highOrGates C y (S j) ∧ (support C w \ S j).Nonempty ∧
        (Heavy.supp C y w \ S i).Nonempty := by
  classical
  let X := Finset.univ.filter (crossingDeficit S C t y)
  let P (i : Fin m) := (assigned C (S i)).erase (n+t)
  let rare := X.filter (fun i => 3 ≤ (P i).card)
  let E := X \ rare
  let credit (i : Fin m) := touchingCredit C t y (S i)
  have xcount := three_crossing_rows S C o t y hk hlin hg hu ho hl hy bad
  change _ ≤ X.card at xcount
  have sum := Finset.sum_le_sum (s:=rare) (f:=fun _ => 1) (g:=credit) (by
    intro i hi
    have h := Finset.mem_filter.mp hi
    have c := (Finset.mem_filter.mp h.1).2.1
    simp only [credit,touchingCredit,ite_eq_right c]
    change 1 ≤ (P i).card + 1 - min y.card (S i).card
    omega)
  simp only [Finset.sum_const,smul_eq_mul,mul_one] at sum
  have hi := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ rare) (f:=credit) (by intros; omega)
  have eq := Finset.card_sdiff_add_card_eq_card (show rare ⊆ X from Finset.filter_subset _ _)
  change E.card+rare.card=X.card at eq
  refine ⟨E,?_,?_⟩
  · change (refunds S C y).card + 4 ≤ E.card + ∑ i, credit i
    omega
  intro i he
  obtain ⟨xi,nr⟩ := Finset.mem_sdiff.mp he
  have xd := (Finset.mem_filter.mp xi).2
  have small : (P i).card ≤ 2 := by by_contra! h; exact nr (Finset.mem_filter.mpr ⟨xi,h⟩)
  obtain ⟨large,non,forallCross⟩ := three_crossing_gate S C o t y hk hlin hg hu ho hl hy i xd
  obtain ⟨w,hw⟩ := non
  obtain ⟨after,j,dis,hj,lost,gained⟩ := forallCross w hw
  obtain ⟨p,hp⟩ := (show (Heavy.supp C y w \ S i).Nonempty from gained)
  have znot : n+t ∉ assigned C (S i) := by
    intro asg
    have sup : p ∈ support C (n+t) := by
      apply (mem_support _ _ _).mpr
      apply hl
      have e : Finset.univ.filter (fun q : Fin n => decide (q=p)=true)={p} := by ext; simp
      rw [e,Finset.card_singleton]; omega
    exact (Finset.mem_sdiff.mp hp).2 ((Finset.mem_filter.mp asg).2.1 sup)
  have same : P i=assigned C (S i) := Finset.erase_eq_of_notMem znot
  have paid := crossing_paid S C o t y (by omega) hg hu ho hl hy i xd
  rw [←same] at paid
  have three : (S i).card=3 := by omega
  have count : (P i).card=2 := by omega
  obtain ⟨ne,win⟩ := Finset.mem_erase.mp hw
  have ass := (Finset.mem_erase.mp win).2
  have before : w<o i := by
    by_contra! h
    have hr := Finset.mem_Ico.mp (Finset.mem_filter.mp ass).1
    have idx : w-n<C.gates.length := by have up := hr.2; change w<n+C.gates.length at up; omega
    have bound := before_output_charge C (S i) (o i) t w ⟨w-n,idx⟩ (by simp; omega)
      (lt_of_le_of_ne h ne.symm) after y.card hg hu (ho i) hl (by omega)
    have cut := Finset.ssubset_iff_of_subset (Finset.filter_subset (· < w) (P i)) |>.mpr
      ⟨w,win,fun hm => Nat.lt_irrefl _ (Finset.mem_filter.mp hm).2⟩
    have smaller := Finset.card_lt_card cut
    change min y.card (S i).card ≤ ((P i).filter (· < w)).card+1 at bound
    omega
  have oeq : support C (o i)=S i := by ext q; exact (mem_support C (o i) q).trans (L_meta_997_refund.output_singleton S C o ho i q)
  have op : o i ∈ assigned C (S i) := Finset.mem_filter.mpr
    ⟨Finset.mem_Ico.mpr (support_gate C (o i) (by rw [oeq,three]; decide)),oeq ▸ Finset.Subset.rfl,by rw [oeq,three]; decide⟩
  have all : assigned C (S i) = {w,o i} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.insert_subset ass (Finset.singleton_subset_iff.mpr op))
    rw [←same,count]
    simp [ne]
  exact ⟨xd.1,three,w,j,after,before,all,dis,hj,lost,gained⟩

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

lemma crossing_parents_general {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o t w : ℕ) (y : Finset (Fin n)) (i j : Fin m) (A F : Finset ℕ)
    (hT : (S i).card = 3)
    (hA : ∀ r ∈ A, value C (fun p => decide (p ∈ y)) r = true)
    (roles : ∀ r ∈ Finset.Ico n (n+C.size), r ≠ n+t → r ∉ A → r ∉ F →
        (∃ a, r ∈ assigned C (S a) ∧ (a ∈ underDisjoint C S y → andAt C n r)) ∨
        (∃ a ∈ underDisjoint C S y, ¬andAt C n r ∧ S a ⊆ support C r ∧ Heavy.supp C y r = S a))
    (hg : hasAllowedGates C)
    (hu : ∀ a : Fin C.gates.length, (C.gates.get a).op = .not → (a : ℕ) = t)
    (hsw : ∀ p : Fin n, p ∈ support C (n+t))
    (hwa : n+t < w) (hwo : w < o) (hasg : assigned C (S i) = {w,o})
    (hw : w ∈ highOrGates C y (S j)) (hout : (support C w \ S j).Nonempty) :
    ∃ (u : ℕ) (p r : Fin n), u ∈ F ∧ p ≠ r ∧ support C u = {p} ∧
      value C (fun a => decide (a ∈ y)) u = false ∧ support C w = {p,r} := by
  obtain ⟨u,_,p,r,uf,_,pr,su,_,_,uc,_,sw,_,_⟩ :=
    crossing_parent_signatures S C o t w y i j A F hT hA roles hg hu hsw hwa hwo hasg hw hout
  exact ⟨u,p,r,uf,pr,su,uc,sw⟩

end L_meta_997.Small


namespace L_meta_997.Small

lemma dependent_certificate_packing {n m : ℕ} (S : Fin m → Finset (Fin n)) (E : Finset (Fin m))
    (P : Finset (Fin n)) (Y : Fin n → Finset (Fin n)) (b : ℕ) (hY : ∀ p ∈ P, (Y p).card ≤ b) (H : Finset ℕ) (W : Finset ℕ → Finset (Fin n))
    (hlin : L_meta_997.Light.rowLinearity S)
    (roles : ∀ i ∈ E,
      (∃ K ∈ H.powersetCard 2, 2 ≤ (W K).card ∧ W K ⊆ S i) ∨
      ∃ p ∈ P, ∃ s ∈ Y p, s ≠ p ∧ p ∈ S i ∧ s ∈ S i) :
    E.card ≤ H.card.choose 2 + P.card * b := by
  classical
  let A := E.filter (fun i => ∃ K ∈ H.powersetCard 2, 2 ≤ (W K).card ∧ W K ⊆ S i)
  let O := E \ A
  have acases (i : A) : ∃ K ∈ H.powersetCard 2, 2 ≤ (W K).card ∧ W K ⊆ S i.val :=
    (Finset.mem_filter.mp i.property).2
  choose a ah size sub using acases
  have ainj : Function.Injective a := by
    intro i j eq
    by_contra ne
    have both : W (a i) ⊆ S i.val ∩ S j.val := fun z hz =>
      Finset.mem_inter.mpr ⟨sub i hz,sub j (eq ▸ hz)⟩
    have cap := (Finset.card_le_card both).trans
      (hlin i.val j.val (fun h => ne (Subtype.ext h)))
    have := size i
    omega
  let af : A → H.powersetCard 2 := fun i => ⟨a i,ah i⟩
  have asz : A.card ≤ H.card.choose 2 := by
    have he : Function.Injective af := fun _ _ h => ainj (congrArg Subtype.val h)
    simpa using Fintype.card_le_of_injective af he
  have ocases (i : O) : ∃ p ∈ P, ∃ s ∈ Y p, s ≠ p ∧ p ∈ S i.val ∧ s ∈ S i.val := by
    have hi := Finset.mem_sdiff.mp i.property
    rcases roles i.val hi.1 with ar|orr
    · exact (hi.2 (Finset.mem_filter.mpr ⟨hi.1,ar⟩)).elim
    · exact orr
  choose p hp s hs hne hP hS using ocases
  let ofn : O → (Σ _ : Fin n, Fin n) := fun i => ⟨p i,s i⟩
  have oinj : Function.Injective ofn := by
    intro i j eq
    by_contra ne
    have ne' : i.val ≠ j.val := fun h => ne (Subtype.ext h)
    have h := hlin i.val j.val ne'
    have ep : p i = p j := congrArg (fun w : (Σ _ : Fin n, Fin n) => w.1) eq
    have es : s i = s j := congrArg (fun w : (Σ _ : Fin n, Fin n) => w.2) eq
    have sub : ({s i,p i} : Finset (Fin n)) ⊆ S i.val ∩ S j.val := by
      intro q hq
      simp only [Finset.mem_insert,Finset.mem_singleton] at hq
      rcases hq with rfl|rfl
      · exact Finset.mem_inter.mpr ⟨hS i,es.symm ▸ hS j⟩
      · exact Finset.mem_inter.mpr ⟨hP i,ep.symm ▸ hP j⟩
    have hc := Finset.card_le_card sub
    rw [Finset.card_pair (hne i)] at hc
    omega
  let f : O → P.sigma Y := fun i => ⟨ofn i,Finset.mem_sigma.mpr ⟨hp i,hs i⟩⟩
  have ocap : O.card ≤ (P.sigma Y).card := by
    have hinj : Function.Injective f := fun _ _ e => oinj (congrArg Subtype.val e)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  have osz : O.card ≤ P.card * b := by
    apply ocap.trans
    rw [Finset.card_sigma]
    simpa using Finset.sum_le_sum (s:=P) (g:=fun _ => b) hY
  have ecard := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ E :
    A ⊆ E)
  change O.card + A.card = E.card at ecard
  omega

lemma dependent_pair_packing {n m : ℕ} (S : Fin m → Finset (Fin n)) (E : Finset (Fin m))
    (P : Finset (Fin n)) (Y : Fin n → Finset (Fin n)) (b : ℕ) (hY : ∀ p ∈ P, (Y p).card ≤ b) (H : Finset ℕ) (σ : ℕ → Finset (Fin n))
    (hthree : ∀ i ∈ E, (S i).card = 3)
    (hlin : L_meta_997.Light.rowLinearity S)
    (roles : ∀ i ∈ E,
      (∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ S i = σ a ∩ σ b) ∨
      ∃ p ∈ P, ∃ s ∈ Y p, s ≠ p ∧ p ∈ S i ∧ s ∈ S i) :
    E.card ≤ H.card.choose 2 + P.card * b := by
  classical
  let W (K : Finset ℕ) := Finset.univ.filter (fun z : Fin n => ∀ a ∈ K, z ∈ σ a)
  apply dependent_certificate_packing S E P Y b hY H W hlin
  intro i hi
  rcases roles i hi with ⟨a,ha,c,hc,ne,eq⟩ | h
  · left
    have W_eq : W {a,c} = S i := by rw [eq]; ext z; simp [W]
    exact ⟨{a,c},Finset.mem_powersetCard.mpr ⟨Finset.insert_subset ha
      (Finset.singleton_subset_iff.mpr hc),Finset.card_pair ne⟩,
      by rw [W_eq,hthree i hi]; decide,by rw [W_eq]⟩
  · exact Or.inr h

noncomputable def singletonPoints {n : ℕ} (G : Finset ℕ) (σ : ℕ → Finset (Fin n)) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun p => ∃ v ∈ G, σ v = {p})

lemma singleton_points_card {n : ℕ} (G : Finset ℕ) (σ : ℕ → Finset (Fin n)) :
    (singletonPoints G σ).card ≤ G.card := by
  classical
  have w (p : singletonPoints G σ) : ∃ v ∈ G, σ v = {p.val} :=
    (Finset.mem_filter.mp p.property).2
  choose v hv hs using w
  let f : singletonPoints G σ → G := fun p => ⟨v p,hv p⟩
  have inj : Function.Injective f := by
    intro p q e
    apply Subtype.ext
    have eq : v p = v q := congrArg Subtype.val e
    have eq' : ({p.val} : Finset (Fin n)) = {q.val} :=
      (hs p).symm.trans ((congrArg σ eq).trans (hs q))
    simpa using eq'
  simpa using Fintype.card_le_of_injective f inj

lemma crossing_exception_packing {n m : ℕ} (S : Fin m → Finset (Fin n))
    (E : Finset (Fin m)) (y : Finset (Fin n)) (H G : Finset ℕ) (σ : ℕ → Finset (Fin n))
    (hthree : ∀ i ∈ E, (S i).card = 3)
    (hlin : L_meta_997.Light.rowLinearity S)
    (hroles : ∀ i ∈ E,
      ∃ u ∈ G, ∃ p : Fin n, σ u = {p} ∧ p ∈ S i ∧
        ((∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ S i = σ a ∩ σ b) ∨
          ∃ s ∈ S i, s ≠ p ∧ (s ∈ y ∨ ∃ v ∈ H, σ v = {s}))) :
    E.card ≤ H.card.choose 2 + G.card * (y.card + H.card) := by
  classical
  let P := singletonPoints G σ
  let Y := y ∪ singletonPoints H σ
  have packed := dependent_pair_packing S E P (fun _ => Y) Y.card (fun _ _ => le_rfl) H σ hthree hlin (by
    intro i hi
    obtain ⟨u,hu,p,hσ,hp,ars | ors⟩ := hroles i hi
    · exact Or.inl ars
    · right
      obtain ⟨s,hs,hneq,hy | ⟨v,hv,hvs⟩⟩ := ors
      · exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,hσ⟩,s,
          Finset.mem_union.mpr (Or.inl hy),hneq,hp,hs⟩
      · exact ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,hσ⟩,s,
          Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,hvs⟩)),hneq,hp,hs⟩)
  have cardY : Y.card ≤ y.card + H.card := (Finset.card_union_le _ _).trans
    (Nat.add_le_add_left (singleton_points_card H σ) y.card)
  exact packed.trans (Nat.add_le_add_left (Nat.mul_le_mul (singleton_points_card G σ) cardY) _)

end L_meta_997.Small

namespace L_meta_997.Small

lemma crossing_packing_cutoff {b δ r e w h c : ℕ}
    (hlarge : (3 ≤ b ∧ δ ≤ 6) ∨ (6 ≤ b ∧ δ ≤ 7))
    (refunds : b ≤ r)
    (ledger : r + h + c + 4 + w ≤ b + δ)
    (crossing : r + 4 ≤ e + w)
    (packing : e ≤ h.choose 2 + c*(3+h)) : False := by
  rcases hlarge with ⟨hb,hδ⟩ | ⟨hb,hδ⟩
  · have hc : c ≤ 2 := by omega
    have hh : h ≤ 2 := by omega
    interval_cases h <;> interval_cases c <;> norm_num [Nat.choose] at packing <;> omega
  · have hc : c ≤ 3 := by omega
    have hh : h ≤ 3 := by omega
    interval_cases h <;> interval_cases c <;> norm_num [Nat.choose] at packing <;> omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem three_window_packing_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : y.card = 3)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (hgap : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
      (3 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+6) ∨
      (6 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+7)) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m := by
  classical
  by_contra bad
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  obtain ⟨E,lower,triples⟩ := regular_crossing_triples S C o t y hk hlin hg hu ho hl hy bad
  obtain ⟨A,F,_,reserve,_,_,hA,roles⟩ :=
    combined_gate_roles S C o t y (by omega) hlin hg hu ho hl hy bad
  let χ : Fin n → Bool := fun p => decide (p ∈ y)
  let H := F.filter (fun w => value C χ w = true)
  let G := F.filter (fun w => ¬value C χ w = true)
  have splitF : H.card + G.card = F.card := Finset.card_filter_add_card_filter_not _
  have hz (p : Fin n) : p ∈ support C (n+t) := by
    apply (mem_support C (n+t) p).mpr
    apply hl
    have eq : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext q; simp
    rw [eq,Finset.card_singleton,hk]
    decide
  have packed := crossing_exception_packing S E y H G (support C)
    (fun i hi => (triples i hi).2.1) hlin (by
    intro i hi
    obtain ⟨meet,three,w,j,after,before,assignedEq,_,high,lowOutside,_⟩ := triples i hi
    obtain ⟨u,p,r,huF,hpr,hsu,huc,hsw⟩ :=
      crossing_parents_general S C (o i) t w y i j A F three (fun a ha => (hA a ha).2)
        roles hg hu hz after before assignedEq high lowOutside
    have hw : w ∈ assigned C (S i) := by simp [assignedEq]
    have hp : p ∈ S i := (Finset.mem_filter.mp hw).2.1 (hsw.symm ▸ Finset.mem_insert_self _ _)
    have cold := (Finset.mem_filter.mp (Finset.mem_filter.mp high).1).2.2.2
    refine ⟨u,Finset.mem_filter.mpr ⟨huF,by simp [χ,huc]⟩,p,hsu,hp,?_⟩
    rcases crossing_output_roles C S i y t w (o i) A F p r hg hu hlin (ho i) meet three ⟨after,before⟩
      assignedEq hsw hpr cold hy hz (fun a ha => (hA a ha).1) roles with andRole | orRole
    · obtain ⟨a,ha,b,hb,ne,hota,hotb,eq⟩ := andRole
      exact Or.inl ⟨a,Finset.mem_filter.mpr ⟨ha,hota⟩,b,Finset.mem_filter.mpr ⟨hb,hotb⟩,ne,eq⟩
    · obtain ⟨s,hs,hne,hs'⟩ := orRole
      exact Or.inr ⟨s,hs,hne,hs'.imp_right (fun ⟨v,hv,sv,hot⟩ =>
        ⟨v,Finset.mem_filter.mpr ⟨hv,hot⟩,sv⟩)⟩)
  rw [hk] at packed reserve
  let paid := fun i => (assigned C (S i)).card+1 < (S i).card
  have underEq : underDisjoint C S y = Finset.univ.filter (fun i => Disjoint (S i) y ∧ paid i) := by
    ext i
    simp [paid,underDisjoint,underpaid,and_comm]
  rw [underEq, Finset.sum_filter, excess_identity S y paid 3] at reserve
  change _ ≤ ∑ i ∈ B, ((S i).card-4) at reserve
  have mass := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl
    (g:=fun i => 4+((S i).card-4)) (fun i hi => by have h := (Finset.mem_filter.mp hi).2.2.2; omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at mass
  have ref := disjoint_outputs_refunded S C o y B hlin ho (fun i hi =>
    ⟨(Finset.mem_filter.mp hi).2.1,by have h := (Finset.mem_filter.mp hi).2.2.2; omega⟩)
  let δ := (∑ i ∈ B, (S i).card)-5*B.card
  have pos : 5*B.card ≤ ∑ i ∈ B, (S i).card := by
    have calcBound := Finset.sum_le_sum (s:=B) (f:=fun _ => 5) (g:=fun i => (S i).card)
      (fun i hi => (Finset.mem_filter.mp hi).2.2.2)
    rw [Finset.sum_const,smul_eq_mul,Nat.mul_comm] at calcBound
    exact calcBound
  change (3 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+6) ∨ (6 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+7) at hgap
  have large : (3 ≤ B.card ∧ δ ≤ 6) ∨ (6 ≤ B.card ∧ δ ≤ 7) := by
    dsimp [δ]
    rcases hgap with a | b
    · exact Or.inl ⟨a.1,by have := a.2; omega⟩
    · exact Or.inr ⟨b.1,by have := b.2; omega⟩
  have charge : (refunds S C y).card + H.card + G.card + 4 +
      (∑ i, touchingCredit C t y (S i)) ≤ B.card + δ := by
    dsimp [δ]
    omega
  exact crossing_packing_cutoff large ref charge lower packed

end L_meta_997.Small





namespace L_meta_997.Small

lemma crossing_partner_packing {n m : ℕ} (S : Fin m → Finset (Fin n))
    (E : Finset (Fin m)) (y : Finset (Fin n)) (K H G : Finset ℕ) (σ : ℕ → Finset (Fin n))
    (hthree : ∀ i ∈ E, (S i).card = 3)
    (htouch : ∀ i ∈ E, ¬Disjoint (S i) y)
    (hlin : L_meta_997.Light.rowLinearity S)
    (hroles : ∀ i ∈ E,
      ∃ u ∈ G, ∃ p : Fin n, σ u = {p} ∧ p ∈ S i ∧
        ((∃ a ∈ K, ∃ b ∈ K, a ≠ b ∧ S i = σ a ∩ σ b) ∨
          ∃ s ∈ S i, s ≠ p ∧ (s ∈ y ∨ ∃ v ∈ H, σ v = {s}))) :
    E.card ≤ K.card.choose 2 + G.card * (y.card + ((singletonPoints H σ).card-1)) := by
  classical
  let P := singletonPoints G σ
  let Y := y ∪ singletonPoints H σ
  let Q (p : Fin n) := if p ∈ y then Y.erase p else y
  have qcard (p : Fin n) (_ : p ∈ P) : (Q p).card ≤ y.card + ((singletonPoints H σ).card-1) := by
    by_cases py : p ∈ y
    · have pY : p ∈ Y := Finset.mem_union.mpr (Or.inl py)
      have c := Finset.card_erase_add_one pY
      have le := Finset.card_union_le y (singletonPoints H σ)
      rw [show Q p=Y.erase p by simp [Q,py]]
      change Y.card ≤ y.card+(singletonPoints H σ).card at le
      omega
    · simp [Q,py]
  have packed := dependent_pair_packing S E P Q (y.card+((singletonPoints H σ).card-1)) qcard K σ hthree hlin (by
    intro i hi
    obtain ⟨u,hu,p,hσ,hp,ars | ors⟩ := hroles i hi
    · exact Or.inl ars
    · right
      have pP : p ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,hσ⟩
      by_cases py : p ∈ y
      · obtain ⟨s,hs,hneq,hy | ⟨v,hv,hvs⟩⟩ := ors
        · exact ⟨p,pP,s,by simpa [Q,py,Y,hy] using hneq,hneq,hp,hs⟩
        · have sH : s ∈ singletonPoints H σ := Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,hv,hvs⟩
          exact ⟨p,pP,s,by simpa [Q,py,Y,sH] using hneq,hneq,hp,hs⟩
      · obtain ⟨s,hs,sy⟩ := Finset.not_disjoint_iff.mp (htouch i hi)
        exact ⟨p,pP,s,by simp [Q,py,sy],fun eq => py (eq ▸ sy),hp,hs⟩)
  exact packed.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (singleton_points_card G σ)) _)

lemma crossing_packing_touching {n m : ℕ} (S : Fin m → Finset (Fin n))
    (E : Finset (Fin m)) (y : Finset (Fin n)) (H G : Finset ℕ) (σ : ℕ → Finset (Fin n))
    (hthree : ∀ i ∈ E, (S i).card = 3)
    (htouch : ∀ i ∈ E, ¬Disjoint (S i) y)
    (hlin : L_meta_997.Light.rowLinearity S)
    (hroles : ∀ i ∈ E,
      ∃ u ∈ G, ∃ p : Fin n, σ u = {p} ∧ p ∈ S i ∧
        ((∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ S i = σ a ∩ σ b) ∨
          ∃ s ∈ S i, s ≠ p ∧ (s ∈ y ∨ ∃ v ∈ H, σ v = {s}))) :
    E.card ≤ H.card.choose 2 + G.card * (y.card + (H.card-1)) := by
  have base := crossing_partner_packing S E y H H G σ hthree htouch hlin hroles
  exact base.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.add_le_add_left (Nat.sub_le_sub_right (singleton_points_card H σ) _) _)) _)

end L_meta_997.Small


namespace L_meta_997.Small

lemma crossing_packing_small_surplus {b δ r e w h c : ℕ}
    (range : (4 ≤ b ∧ δ ≤ 7) ∨ (7 ≤ b ∧ δ ≤ 8))
    (refunds : b ≤ r) (ledger : r + h + c + 4 + w ≤ b+δ)
    (crossing : r + 4 ≤ e + w)
    (packing : e ≤ h.choose 2 + c*(3+(h-1))) :
    r=b ∧ h=0 ∧ 3 ≤ c ∧ c ≤ 4 ∧ w=0 ∧ 3*c ≤ e+1 := by
  have wide : δ ≤ 8 := by omega
  have hc : c ≤ 4 := by omega
  have hh : h ≤ 4 := by omega
  rcases range with ⟨hb,hd⟩ | ⟨hb,hd⟩
  <;> interval_cases h <;> interval_cases c <;> norm_num [Nat.choose] at packing <;> omega
end L_meta_997.Small




namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

def mixedSignature {n : ℕ} (C : Circuit) (y : Finset (Fin n)) (v : ℕ) : Prop :=
  (support C v \ Heavy.supp C y v).Nonempty ∧ (Heavy.supp C y v).Nonempty

theorem sound_prefix_small {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (y : Finset (Fin n)) (t v : ℕ) (A F : Finset ℕ)
    (hg : hasAllowedGates C)
    (hu : ∀ a : Fin C.gates.length, (C.gates.get a).op = .not → (a : ℕ) = t)
    (hz : Heavy.supp C y (n+t) = ∅)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (hyPos : y.Nonempty)
    (hlin : rowLinearity S)
    (hbefore : ∀ a < v, ¬mixedSignature C y a)
    (hF : ∀ a ∈ F, mixedSignature C y a)
    (hA : ∀ a ∈ A, value C (fun p => decide (p ∈ y)) a = true)
    (hroles : ∀ a ∈ Finset.Ico n (n+C.size), a ≠ n+t → a ∉ A → a ∉ F →
      (∃ j, a ∈ assigned C (S j) ∧ (j ∈ underDisjoint C S y → andAt C n a)) ∨
      (∃ j ∈ underDisjoint C S y, ¬andAt C n a ∧ S j ⊆ support C a ∧
        Heavy.supp C y a = S j ∧ value C (fun p => decide (p ∉ S j)) a = false))
    (i : Fin m) (hi : i ∈ underDisjoint C S y)
    (noTerminal : ∀ a < v, ¬(S i ⊆ support C a ∧ Heavy.supp C y a = S i) ∨
        andAt C n a) :
    ∀ a < v, value C (fun p => decide (p ∉ S i)) a = false →
        (Heavy.supp C y a).card ≤ 1 := by
  classical
  have hydis := (Finset.mem_filter.mp hi).2
  obtain ⟨D,_,mon,hagree⟩ := Heavy.heavy_model C y t hg hu hy
  intro a
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    intro av off
    by_contra! big
    have subHi : Heavy.supp C y a ⊆ S i := by
      intro p hp
      by_contra hpn
      have src : ∀ q ∈ y, (fun p' => decide (p' ∈ y ∨ p'=p)) q = true :=
        fun q hq => by simp [hq]
      have dst : ∀ q ∈ y, (fun p' => decide (p' ∉ S i)) q = true :=
        fun q hq => decide_eq_true (fun hq' => Finset.disjoint_left.mp hydis hq' hq)
      have le : ∀ q : Fin n, (fun p' => decide (p' ∈ y ∨ p'=p)) q = true →
          (fun p' => decide (p' ∉ S i)) q = true := by
        intro q hq
        rcases of_decide_eq_true hq with h | rfl
        · exact dst _ h
        · simp [hpn]
      have pOn := (Heavy.mem_supp C y a p).mp hp
      rw [←hagree _ src a] at pOn
      have e := value_mono D mon _ _ le a pOn
      rw [hagree _ dst a,off] at e
      contradiction
    have highPos : (Heavy.supp C y a).Nonempty := Finset.card_pos.mp (by omega)
    have lowSub : support C a ⊆ Heavy.supp C y a := by
      by_contra he
      exact hbefore a av ⟨Finset.sdiff_nonempty.mpr he,highPos⟩
    have nle : n ≤ a := by
      by_contra! small
      let p : Fin n := ⟨a,small⟩
      have hp : p ∈ S i := by
        change value C (fun q => decide (q ∉ S i)) p = false at off
        simpa [input_value] using off
      have hy' : p ∉ y := fun pY => Finset.disjoint_left.mp hydis hp pY
      have eq : Heavy.supp C y a = {p} := by
        ext q
        rw [Heavy.mem_supp]
        change value C (fun r => decide (r ∈ y ∨ r=q)) p = true ↔ _
        rw [input_value]
        simp [hy',eq_comm]
      rw [eq,Finset.card_singleton] at big
      omega
    have aup : a<n+C.size := by
      by_contra! e
      obtain ⟨p,hp⟩ := highPos
      have q := (Heavy.mem_supp C y a p).mp hp
      rw [missing_value C _ a e] at q
      contradiction
    have az : a ≠ n+t := by
      intro eq
      rw [eq,hz,Finset.card_empty] at big
      omega
    have notF : a ∉ F := fun af => hbefore a av (hF a af)
    have notA : a ∉ A := by
      intro aa
      obtain ⟨p,hp⟩ := hyPos
      have e : (fun q : Fin n => decide (q ∈ y ∨ q=p)) = (fun q => decide (q∈y)) := by
        ext q
        by_cases eq : q=p
        · subst q; simp [hp]
        · simp [eq]
      have vOn : p ∈ Heavy.supp C y a := (Heavy.mem_supp C y a p).mpr (by rw [e]; exact hA a aa)
      exact Finset.disjoint_left.mp hydis (subHi vOn) hp
    have andA : andAt C n a := by
      rcases hroles a (Finset.mem_Ico.mpr ⟨nle,aup⟩) az notA notF with ⟨j,hj,hjAnd⟩ | ⟨j,hj,hnAnd,hsub,hsig,_⟩
      · have lowSize := (Finset.mem_filter.mp hj).2.2
        have lowRow := (Finset.mem_filter.mp hj).2.1
        have eq : j=i := by
          by_contra jn
          have hS : support C a ⊆ S j ∩ S i := fun p hp => Finset.mem_inter.mpr ⟨lowRow hp,subHi (lowSub hp)⟩
          have hcard := (Finset.card_le_card hS).trans (hlin _ _ jn)
          omega
        exact hjAnd (eq.symm ▸ hi)
      · have inc : S j ⊆ S i := hsub.trans (lowSub.trans subHi)
        have rowcard := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2
        have eq : j=i := by
          by_contra jn
          have hS : S j ⊆ S j ∩ S i := fun p hp => Finset.mem_inter.mpr ⟨hp,inc hp⟩
          have hcard := (Finset.card_le_card hS).trans (hlin _ _ jn)
          omega
        subst j
        exact ((noTerminal a av).resolve_left (fun f => f ⟨hsub,hsig⟩))
    have hidx : a-n<C.gates.length := by change a<n+C.gates.length at aup; omega
    let g := C.gates[a-n]
    have andOp : g.op = .and := by
      simpa [andAt,g,hidx] using andA
    have all (x : Fin n → Bool) :
        value C x a = true ↔ ∀ b ∈ g.inputs, b<a ∧ value C x b=true := by
      rw [gate_value C x a nle aup]
      change g.op.eval (g.inputs.map (fun b => if b<a then value C x b else false)) = true ↔ _
      simp [andOp,GateOp.eval]
    have neg : ¬∀ b ∈ g.inputs, b<a ∧ value C (fun p => decide (p ∉ S i)) b=true :=
      fun h => Bool.noConfusion (off.symm.trans ((all _).mpr h))
    push Not at neg
    obtain ⟨b,bg,bre⟩ := neg
    obtain ⟨p,pp⟩ := highPos
    have ba := ((all _).mp ((Heavy.mem_supp C y a p).mp pp) b bg).1
    have bOff : value C (fun p => decide (p ∉ S i)) b = false := by
      apply Bool.eq_false_iff.mpr
      exact bre ba
    have subset : Heavy.supp C y a ⊆ Heavy.supp C y b := fun p hp =>
      (Heavy.mem_supp C y b p).mpr (((all _).mp ((Heavy.mem_supp C y a p).mp hp)) b bg).2
    have le := (Finset.card_le_card subset).trans (ih b ba (ba.trans av) bOff)
    omega

end L_meta_997.Small


namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

theorem saturated_refund_is_output {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (y : Finset (Fin n)) (D : Finset (Fin m))
    (hpair : rowLinearity S)
    (hout : rowOutputs C S o)
    (hD : ∀ i ∈ D, Disjoint (S i) y ∧ 2 ≤ (S i).card)
    (sat : (refunds S C y).card ≤ D.card)
    (i : Fin m) (hi : i ∈ D) (w : ℕ) (low : support C w = S i) (high : Heavy.supp C y w = S i) :
    w = o i := by
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
  let I := D.attach.image f
  have ci : I.card=D.card := by simp [I,Finset.card_image_of_injective _ hinj]
  have sub : I ⊆ refunds S C y := by
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
      · exact fun hp => ⟨p,hp,by simp⟩
  have eq : I = refunds S C y := Finset.eq_of_subset_of_card_le sub (by rwa [ci])
  obtain ⟨lo,hiw⟩ := support_gate C w (by rw [low]; exact (hD i hi).2)
  let gw : Fin C.gates.length := ⟨w-n,by change w < n+C.gates.length at hiw; omega⟩
  have gval : n+gw.val=w := by dsimp [gw]; omega
  have gwR : gw ∈ refunds S C y := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨i,?_⟩,i,(hD i hi).1,?_⟩
    · intro p; rw [gval,←mem_support,low]
    · intro p _; rw [gval,←Heavy.mem_supp,high]
  have gwI := eq.symm ▸ gwR
  obtain ⟨j,_,ej⟩ := Finset.mem_image.mp gwI
  have oj : o j.val=w := (hw j).symm.trans ((congrArg (fun g : Fin C.gates.length => n+g.val) ej).trans gval)
  have se : S j.val = S i := by rw [←hs j.val,oj,low]
  have ji : j.val=i := by
    by_contra h
    have lin := hpair j.val i h
    rw [se,Finset.inter_self] at lin
    have := (hD i hi).2
    omega
  rw [←ji]
  exact oj.symm

end L_meta_997.Light


namespace L_meta_997.Small

lemma role_pair_cover_packing {n m : ℕ} (S : Fin m → Finset (Fin n)) (E : Finset (Fin m))
    (P Y : Finset (Fin n)) (H : Finset ℕ) (σ : ℕ → Finset (Fin n))
    (hlin : L_meta_997.Light.rowLinearity S)
    (roles : ∀ i ∈ E,
      (∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ (σ a ∪ σ b).card ≥ 2 ∧ σ a ∪ σ b ⊆ S i) ∨
      ∃ p ∈ P, ∃ s ∈ Y, s ≠ p ∧ p ∈ S i ∧ s ∈ S i) :
    E.card ≤ H.card.choose 2 + P.card * Y.card := by
  classical
  let W (K : Finset ℕ) := K.biUnion σ
  apply dependent_certificate_packing S E P (fun _ => Y) Y.card (fun _ _ => le_rfl) H W hlin
  intro i hi
  rcases roles i hi with ⟨a,ha,c,hc,ne,hcard,hsub⟩ | h
  · left
    have eq : W {a,c} = σ a ∪ σ c := by simp [W]
    exact ⟨{a,c},Finset.mem_powersetCard.mpr ⟨Finset.insert_subset ha
      (Finset.singleton_subset_iff.mpr hc),Finset.card_pair ne⟩,
      by simpa only [eq] using hcard,by simpa only [eq] using hsub⟩
  · exact Or.inr h

lemma crossing_mixed_anchors_saturate {n m : ℕ} (S : Fin m → Finset (Fin n))
    (E : Finset (Fin m)) (y : Finset (Fin n)) (M F : Finset ℕ) (σ : ℕ → Finset (Fin n))
    (hF : F.card ≤ 6) (hM : M ⊆ F) (hy : y.card=3) (hE : 3*F.card ≤ E.card+1)
    (hlin : L_meta_997.Light.rowLinearity S)
    (hroles : ∀ i ∈ E,
       (∃ u ∈ M, ∃ p : Fin n, σ u = {p} ∧ p ∈ S i ∧ ∃ s ∈ y, s ≠ p ∧ s ∈ S i) ∨
       (∃ u ∈ F \ M, ∃ v ∈ F \ M, u ≠ v ∧ 2 ≤ (σ u ∪ σ v).card ∧ σ u ∪ σ v ⊆ S i)) :
    M = F := by
  classical
  let P := singletonPoints M σ
  let H := F \ M
  have b := role_pair_cover_packing S E P y H σ hlin (by
    intro i hi
    rcases hroles i hi with ⟨u,hu,p,hs,hp,s,hsY,hsne,hsi⟩ | pair
    · exact Or.inr ⟨p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,u,hu,hs⟩,s,hsY,hsne,hp,hsi⟩
    · exact Or.inl pair)
  have p := Nat.mul_le_mul_right y.card (singleton_points_card M σ)
  change P.card*y.card ≤ M.card*y.card at p
  have c := Finset.card_sdiff_add_card_eq_card hM
  change H.card+M.card=F.card at c
  rw [hy] at b p
  have hc : H.card ≤ 6 := by omega
  have mc : F.card ≤ M.card := by
    interval_cases h : H.card <;> norm_num [Nat.choose] at b <;> omega
  exact Finset.eq_of_subset_of_card_le hM mc

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

theorem crossing_forces_mixed_exceptions {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (y : Finset (Fin n)) (t : ℕ) (o : Fin m → ℕ) (A F : Finset ℕ) (E : Finset (Fin m))
    (hycard : y.card=3) (hFcard : F.card ≤ 6) (enough : 3*F.card ≤ E.card+1)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hz_cold : value C (fun q => decide (q ∈ y)) (n+t) = false)
    (hz_full : ∀ p : Fin n, p ∈ support C (n+t))
    (hA : ∀ v ∈ A, support (n:=n) C v = ∅ ∧ value C (fun q => decide (q ∈ y)) v = true)
    (hF : ∀ v ∈ F, value C (fun q => decide (q ∈ y)) v = false)
    (roles : ∀ v ∈ Finset.Ico n (n+C.size), v ≠ n+t → v ∉ A → v ∉ F →
      (∃ j, v ∈ assigned C (S j) ∧ (j ∈ underDisjoint C S y → andAt C n v)) ∨
      (∃ j ∈ underDisjoint C S y, ¬andAt C n v ∧ S j ⊆ support C v ∧ Heavy.supp C y v = S j))
    (triples : ∀ i ∈ E, ¬ Disjoint (S i) y ∧ (S i).card=3 ∧ ∃ w j,
       n+t<w ∧ w<o i ∧ assigned C (S i)={w,o i} ∧ Disjoint y (S j) ∧
       w ∈ highOrGates C y (S j) ∧ (support C w \ S j).Nonempty ∧
       (Heavy.supp C y w \ S i).Nonempty) :
    ∀ v ∈ F, mixedSignature C y v ∧ (support (n:=n) C v).card=1 := by
  classical
  let M := F.filter (fun v => mixedSignature C y v ∧ (support (n:=n) C v).card=1)
  have sat : M = F := crossing_mixed_anchors_saturate S E y M F (support C)
    hFcard (Finset.filter_subset _ _) hycard enough hlin (by
    intro i hi
    obtain ⟨meet,three,w,j,after,before,assignedEq,_,high,lowOutside,_⟩ := triples i hi
    obtain ⟨u,v,p,r,huF,uv,pr,su,sv,missing,_,_,hw,union,conditional⟩ :=
      crossing_parent_signatures S C (o i) t w y i j A F three (fun a ha => (hA a ha).2)
        roles hg hu hz_full after before assignedEq high lowOutside
    have hw_ass : w ∈ assigned C (S i) := by simp [assignedEq]
    have hw_sub : support C w ⊆ S i := (Finset.mem_filter.mp hw_ass).2.1
    have hp : p ∈ S i := hw_sub (hw.symm ▸ Finset.mem_insert_self _ _)
    have hr : r ∈ S i := hw_sub (hw.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have cold := (Finset.mem_filter.mp (Finset.mem_filter.mp high).1).2.2.2
    have anchor_point (a b : Fin n) (ab : a ≠ b) (signature : support C w = {a,b}) :
        ∃ s ∈ y, s ≠ a ∧ s ∈ S i := by
      rcases crossing_output_roles C S i y t w (o i) A F a b hg hu hlin (ho i) meet three
        ⟨after,before⟩ assignedEq signature ab cold hz_cold hz_full (fun v hv => (hA v hv).1)
        roles with andRole | orRole
      · obtain ⟨v,hv,_,_,_,hot,_,_⟩ := andRole
        rw [hF v hv] at hot
        contradiction
      · obtain ⟨s,hs,neq,hsy | ⟨v,hv,_,hot⟩⟩ := orRole
        · exact ⟨s,hsy,neq,hs⟩
        · rw [hF v hv] at hot
          contradiction
    by_cases he : (Heavy.supp C y u).Nonempty
    · have mixed : mixedSignature C y u :=
        ⟨⟨p,Finset.mem_sdiff.mpr ⟨su.symm ▸ Finset.mem_singleton_self _,missing⟩⟩,he⟩
      exact Or.inl ⟨u,Finset.mem_filter.mpr ⟨huF,mixed,by simp [su]⟩,p,su,hp,anchor_point p r pr hw⟩
    · have he' := Finset.not_nonempty_iff_eq_empty.mp he
      have hvF := conditional he'
      by_cases mixv : mixedSignature C y v
      · exact Or.inl ⟨v,Finset.mem_filter.mpr ⟨hvF,mixv,by simp [sv]⟩,r,sv,hr,
          anchor_point r p pr.symm (by rw [Finset.pair_comm]; exact hw)⟩
      · have nu : u ∉ M := fun h => he (Finset.mem_filter.mp h).2.1.2
        have nv : v ∉ M := fun h => mixv (Finset.mem_filter.mp h).2.1
        have two : support C u ∪ support C v = {p,r} := by rw [su,sv]; simp
        exact Or.inr ⟨u,Finset.mem_sdiff.mpr ⟨huF,nu⟩,v,Finset.mem_sdiff.mpr ⟨hvF,nv⟩,uv,
          by rw [two,Finset.card_pair pr], by rw [two,←hw]; exact hw_sub⟩)
  intro v hv
  have hm : v ∈ M := sat.symm ▸ hv
  have h := Finset.mem_filter.mp hm
  exact h.2

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem tight_crossing_configuration {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : y.card = 3)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (bad : ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m))
    (profile : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
      (4 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+7) ∨
      (7 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+8)) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
    (refunds S C y).card = B.card ∧
      (∀ i, Disjoint (S i) y → 2 ≤ (S i).card → i ∈ B) ∧
      (∀ i, ¬Disjoint (S i) y → ((assigned C (S i)).erase (n+t)).card ≤ 2) ∧
      ∃ A F : Finset ℕ, F.Nonempty ∧ (∀ v ∈ F, mixedSignature C y v ∧ (support (n:=n) C v).card=1) ∧
        (∀ v ∈ A, support (n:=n) C v=∅ ∧ value C (fun p => decide (p ∈ y)) v=true) ∧
        ∀ v ∈ Finset.Ico n (n+C.size), v ≠ n+t → v ∉ A → v ∉ F →
          (∃ i, v ∈ assigned C (S i) ∧ (i ∈ underDisjoint C S y → andAt C n v)) ∨
          ∃ i ∈ underDisjoint C S y, ¬andAt C n v ∧ S i ⊆ support C v ∧
            Heavy.supp C y v = S i ∧ value C (fun p => decide (p ∉ S i)) v = false ∧ v ≤ o i := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  change (4 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+7) ∨
    (7 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+8) at profile
  obtain ⟨E,lower,triples⟩ := regular_crossing_triples S C o t y hk hlin hg hu ho hl hy bad
  obtain ⟨A,F,_,reserve,_,_,hA,ordered⟩ :=
    combined_ordered_gate_roles S C o t y (by omega) hlin hg hu ho hl hy bad
  have roles (v) (hv : v ∈ Finset.Ico n (n+C.size)) (hn : v ≠ n+t) (ha : v ∉ A) (hf : v ∉ F) :
      (∃ i, v ∈ assigned C (S i) ∧ (i ∈ underDisjoint C S y → andAt C n v)) ∨
      ∃ i ∈ underDisjoint C S y, ¬andAt C n v ∧ S i ⊆ support C v ∧ Heavy.supp C y v = S i := by
    rcases ordered v hv hn ha hf with own | ⟨i,hi,op,sub,sg,_,_⟩
    · exact Or.inl own
    · exact Or.inr ⟨i,hi,op,sub,sg⟩
  let χ : Fin n → Bool := fun p => decide (p ∈ y)
  let H := F.filter (fun w => value C χ w = true)
  let G := F.filter (fun w => ¬value C χ w = true)
  have splitF : H.card + G.card = F.card := Finset.card_filter_add_card_filter_not _
  have hz (p : Fin n) : p ∈ support C (n+t) := by
    apply (mem_support C (n+t) p).mpr
    apply hl
    have eq : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext q; simp
    rw [eq,Finset.card_singleton,hk]
    decide
  have packedRoles (i : Fin m) (hi : i ∈ E) :
      ∃ u ∈ G, ∃ p : Fin n, support C u = {p} ∧ p ∈ S i ∧
        ((∃ a ∈ H, ∃ b ∈ H, a ≠ b ∧ S i = support C a ∩ support C b) ∨
          ∃ s ∈ S i, s ≠ p ∧ (s ∈ y ∨ ∃ v ∈ H, support C v = {s})) := by
    obtain ⟨meet,three,w,j,after,before,assignedEq,_,high,lowOutside,_⟩ := triples i hi
    obtain ⟨u,p,r,huF,hpr,hsu,huc,hsw⟩ :=
      crossing_parents_general S C (o i) t w y i j A F three (fun a ha => (hA a ha).2)
        roles hg hu hz after before assignedEq high lowOutside
    have hw : w ∈ assigned C (S i) := by simp [assignedEq]
    have hp : p ∈ S i := (Finset.mem_filter.mp hw).2.1 (hsw.symm ▸ Finset.mem_insert_self _ _)
    have cold := (Finset.mem_filter.mp (Finset.mem_filter.mp high).1).2.2.2
    refine ⟨u,Finset.mem_filter.mpr ⟨huF,by simp [χ,huc]⟩,p,hsu,hp,?_⟩
    rcases crossing_output_roles C S i y t w (o i) A F p r hg hu hlin (ho i) meet three ⟨after,before⟩
      assignedEq hsw hpr cold hy hz (fun a ha => (hA a ha).1) roles with andRole | orRole
    · obtain ⟨a,ha,b,hb,ne,hota,hotb,eq⟩ := andRole
      exact Or.inl ⟨a,Finset.mem_filter.mpr ⟨ha,hota⟩,b,Finset.mem_filter.mpr ⟨hb,hotb⟩,ne,eq⟩
    · obtain ⟨s,hs,hne,hs'⟩ := orRole
      exact Or.inr ⟨s,hs,hne,hs'.imp_right (fun ⟨v,hv,sv,hot⟩ =>
        ⟨v,Finset.mem_filter.mpr ⟨hv,hot⟩,sv⟩)⟩
  have packed := crossing_packing_touching S E y H G (support C)
    (fun i hi => (triples i hi).2.1) (fun i hi => (triples i hi).1) hlin packedRoles
  rw [hk] at packed reserve
  let paid := fun i => (assigned C (S i)).card+1 < (S i).card
  have underEq : underDisjoint C S y = Finset.univ.filter (fun i => Disjoint (S i) y ∧ paid i) := by
    ext i
    simp [paid,underDisjoint,underpaid,and_comm]
  rw [underEq,Finset.sum_filter,excess_identity S y paid 3] at reserve
  change _ ≤ ∑ i ∈ B, ((S i).card-4) at reserve
  have sum_switch := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl
    (g:=fun i => 4+((S i).card-4)) (fun i hi => by have h := (Finset.mem_filter.mp hi).2.2.2; omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at sum_switch
  have hD (i) (hi : i ∈ B) : Disjoint (S i) y ∧ 2 ≤ (S i).card := by
    obtain ⟨dis,_,big⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨dis,by omega⟩
  have ref := disjoint_outputs_refunded S C o y B hlin ho hD
  let δ := (∑ i ∈ B, (S i).card) - 5*B.card
  have pos : 5*B.card ≤ ∑ i ∈ B, (S i).card := by
    have h := Finset.sum_le_sum (s:=B) (f:=fun _ => 5) (g:=fun i => (S i).card)
      (fun i hi => (Finset.mem_filter.mp hi).2.2.2)
    simpa [Finset.sum_const,smul_eq_mul,Nat.mul_comm] using h
  have small : (4 ≤ B.card ∧ δ ≤ 7) ∨ (7 ≤ B.card ∧ δ ≤ 8) := by
    dsimp [δ]
    rcases profile with h | h
    · exact Or.inl ⟨h.1,by have := h.2; omega⟩
    · exact Or.inr ⟨h.1,by have := h.2; omega⟩
  have charge : (refunds S C y).card + H.card + G.card + 4 +
      (∑ i, touchingCredit C t y (S i)) ≤ B.card+δ := by
    dsimp [δ]
    omega
  obtain ⟨refEq,hotZero,gmin,gmax,creditZero,lowerStrong⟩ :=
    crossing_packing_small_surplus small ref charge lower packed
  have hF (v) (hv : v ∈ F) : value C χ v = false := by
    apply Bool.eq_false_iff.mpr
    intro hot
    have hn : H.Nonempty := ⟨v,Finset.mem_filter.mpr ⟨hv,hot⟩⟩
    have := Finset.card_pos.mpr hn
    omega
  have fMixed := crossing_forces_mixed_exceptions C S y t o A F E hk
    (by omega : F.card≤6) (by omega : 3*F.card≤E.card+1)
    hlin hg hu ho hy hz hA hF roles triples
  refine ⟨refEq,?_,?_,A,F,Finset.card_pos.mp (by omega),fMixed,hA,ordered⟩
  · intro i dis big
    by_contra h
    let X := insert i B
    have dx (j) (hj : j ∈ X) : Disjoint (S j) y ∧ 2 ≤ (S j).card := by
      rcases Finset.mem_insert.mp hj with rfl | hb
      · exact ⟨dis,big⟩
      · exact hD j hb
    have p := disjoint_outputs_refunded S C o y X hlin ho dx
    change (insert i B).card ≤ _ at p
    rw [Finset.card_insert_of_notMem h,refEq] at p
    change B.card+1 ≤ B.card at p
    omega
  · intro i touch
    have c := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j : Fin m => touchingCredit C t y (S j))
      (fun (j : Fin m) _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [creditZero] at c
    simp only [touchingCredit,ite_eq_right touch,hk] at c
    omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

theorem no_first_mixed_signature {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (y : Finset (Fin n)) (t : ℕ) (o : Fin m → ℕ) (A F : Finset ℕ) (B : Finset (Fin m))
    (hn : 2 ≤ n) (hyPos : y.Nonempty) (proper : ∀ i, S i ≠ Finset.univ)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hy : value C (fun q => decide (q ∈ y)) (n+t) = false)
    (hz_high : Heavy.supp C y (n+t) = ∅) (hz_full : ∀ q : Fin n, q ∈ support C (n+t))
    (hA : ∀ v ∈ A, support (n:=n) C v = ∅ ∧ value C (fun q => decide (q ∈ y)) v = true)
    (hF : ∀ v ∈ F, mixedSignature C y v ∧ (support (n:=n) C v).card=1)
    (sat : (refunds S C y).card ≤ B.card)
    (hB : ∀ i ∈ B, Disjoint (S i) y ∧ 2 ≤ (S i).card)
    (hDB : ∀ i, Disjoint (S i) y → 2 ≤ (S i).card → i ∈ B)
    (hBU : ∀ i ∈ B, i ∈ underDisjoint C S y)
    (credited : ∀ i, ¬Disjoint (S i) y → ((assigned C (S i)).erase (n+t)).card ≤ 2)
    (roles : ∀ v ∈ Finset.Ico n (n+C.size), v ≠ n+t → v ∉ A → v ∉ F →
      (∃ j, v ∈ assigned C (S j) ∧ (j ∈ underDisjoint C S y → andAt C n v)) ∨
      (∃ j ∈ underDisjoint C S y, ¬andAt C n v ∧ S j ⊆ support C v ∧
        Heavy.supp C y v = S j ∧ value C (fun p => decide (p ∉ S j)) v = false ∧ v ≤ o j)) :
    ∀ w, ¬mixedSignature C y w := by
  classical
  by_contra! ex
  let w := Nat.find ex
  have mixed : mixedSignature C y w := Nat.find_spec ex
  have earlier (v) (hv : v<w) : ¬mixedSignature C y v := Nat.find_min ex hv
  obtain ⟨⟨p,ps⟩,q,hq⟩ := mixed
  obtain ⟨plow,phigh⟩ := Finset.mem_sdiff.mp ps
  let unit (p q : Fin n) := decide (q=p)
  let test (p q : Fin n) := decide (q∈y ∨ q=p)
  have rawNo (a : ℕ) (ha : a<n) : support C a ⊆ Heavy.supp C y a := by
    intro s hs
    let b : Fin n := ⟨a,ha⟩
    have l : value C (unit s) b = true := (mem_support C a s).mp hs
    rw [input_value] at l
    apply (Heavy.mem_supp C y a s).mpr
    change value C (test s) b = true
    rw [input_value]
    exact decide_eq_true (Or.inr (of_decide_eq_true l))
  have nle : n ≤ w := by by_contra! h; exact phigh (rawNo w h plow)
  have up : w < n+C.size := by
    by_contra! h
    have z := (mem_support C w p).mp plow
    rw [missing_value C _ w h] at z
    contradiction
  have nz : w ≠ n+t := by
    intro e
    rw [e,hz_high] at hq
    simp at hq
  have notA : w ∉ A := by intro h; rw [(hA w h).1] at plow; simp at plow
  have wx : w-n<C.gates.length := by change w<n+C.gates.length at up; omega
  let g := C.gates[w-n]
  let read (x : Fin n → Bool) (a : ℕ) := if a<w then value C x a else false
  have ev (x : Fin n → Bool) : value C x w=g.op.eval (g.inputs.map (read x)) := gate_value C x w nle up
  have lost : value C (test p) w ≠ true := fun h => phigh ((Heavy.mem_supp C y w p).mpr h)
  have hqtrue : value C (test q) w=true := (Heavy.mem_supp C y w q).mp hq
  obtain ⟨op,len⟩ := hg g (List.getElem_mem _)
  have hor : g.op = .or := by
    rcases op with a | a | a
    · apply False.elim
      have all (x : Fin n → Bool) :
          value C x w=true ↔ ∀ v ∈ g.inputs, read x v=true := by rw [ev,a]; simp [GateOp.eval]
      have nt : ¬∀ v ∈ g.inputs, read (test p) v=true := fun h => lost ((all _).mpr h)
      push Not at nt
      obtain ⟨v,hi,off⟩ := nt
      have qOn := (all _).mp hqtrue v hi
      have vl : v<w := by by_contra h; simp [read,h] at qOn
      have qV : q ∈ Heavy.supp C y v := (Heavy.mem_supp C y v q).mpr (by simpa [read,vl,test] using qOn)
      have pLow : p ∈ support C v := (mem_support C v p).mpr (by
        simpa [read,vl,test] using (all _).mp ((mem_support C w p).mp plow) v hi)
      have pHi : p ∉ Heavy.supp C y v := by
        intro hon
        exact off (by simpa [read,vl,test] using (Heavy.mem_supp C y v p).mp hon)
      exact earlier v vl ⟨⟨p,Finset.mem_sdiff.mpr ⟨pLow,pHi⟩⟩,q,qV⟩
    · exact a
    · have h := hu ⟨w-n,wx⟩ a
      change w-n=t at h
      exact (nz (by omega)).elim
  have any (x : Fin n → Bool) :
      value C x w=true ↔ ∃ v ∈ g.inputs, read x v=true := by rw [ev,hor]; simp [GateOp.eval]
  obtain ⟨u,um,ut⟩ := (any _).mp ((mem_support C w p).mp plow)
  have uw : u<w := by by_contra h; simp [read,h] at ut
  have pu : p ∈ support C u := (mem_support C u p).mpr (by simpa [read,uw,test] using ut)
  have no_p : p ∉ Heavy.supp C y u := by
    intro h
    exact lost ((any _).mpr ⟨u,um,by simpa [read,uw,test] using (Heavy.mem_supp C y u p).mp h⟩)
  have uhigh : Heavy.supp C y u = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    intro h
    exact earlier u uw ⟨⟨p,Finset.mem_sdiff.mpr ⟨pu,no_p⟩⟩,h⟩
  have usub : support C u ⊆ support C w := fun a ha =>
    (mem_support C w a).mpr ((any _).mpr ⟨u,um,by simpa [read,uw,test] using (mem_support C u a).mp ha⟩)
  have ularge : u=n+t ∨ (2 ≤ (support (n:=n) C u).card) := by
    by_cases uz : u=n+t
    · exact Or.inl uz
    right
    have ulo : n ≤ u := by by_contra! h; exact no_p (rawNo u h pu)
    have uA : u ∉ A := by intro h; rw [(hA u h).1] at pu; simp at pu
    have uF : u ∉ F := fun h => earlier u uw (hF u h).1
    rcases roles u (Finset.mem_Ico.mpr ⟨ulo,uw.trans up⟩) uz uA uF with o | term
    · obtain ⟨i,hi,_⟩ := o
      exact (Finset.mem_filter.mp hi).2.2
    · obtain ⟨i,hi,_,sub,_,_,_⟩ := term
      have a := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
      have b := Finset.card_le_card sub
      omega
  have wF : w ∉ F := by
    intro h
    have card := (hF w h).2
    rcases ularge with he | uc
    · have sub : (Finset.univ : Finset (Fin n)) ⊆ support C w := fun a _ => usub (he.symm ▸ hz_full a)
      have cnt := Finset.card_le_card sub
      simp only [Finset.card_univ,Fintype.card_fin] at cnt
      omega
    · have cnt := Finset.card_le_card usub
      omega
  obtain ⟨i,hi,hAnd,lowR,highR,soundR,rankR⟩ :=
    (roles w (Finset.mem_Ico.mpr ⟨nle,up⟩) nz notA wF).resolve_left (by
      rintro ⟨i,hi,hrole⟩
      obtain ⟨_,sub,large⟩ := Finset.mem_filter.mp hi
      have touched : ¬Disjoint (S i) y := by
        intro hd
        have two := large.trans (Finset.card_le_card sub)
        have andw := hrole (hBU i (hDB i hd two))
        simp [andAt,g,wx,hor] at andw
      obtain ⟨uNz,usmall⟩ : u ≠ n+t ∧ 2 ≤ (support (n:=n) C u).card := by
        rcases ularge with e | uc
        · exact (proper i (Finset.eq_univ_of_forall (fun a => sub (usub (e.symm ▸ hz_full a))))).elim
        · refine ⟨?_,uc⟩
          intro e
          exact proper i (Finset.eq_univ_of_forall (fun a => sub (usub (e.symm ▸ hz_full a))))
      have uass : u ∈ assigned C (S i) := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr (support_gate C u usmall),usub.trans sub,usmall⟩
      have osig : support C (o i) = S i := by
        ext a; rw [mem_support,ho]; simp
      have orng := support_gate C (o i) (by rw [osig]; exact large.trans (Finset.card_le_card sub))
      have oass : o i ∈ assigned C (S i) := Finset.mem_filter.mpr
        ⟨Finset.mem_Ico.mpr orng,by rw [osig],by rw [osig]; exact large.trans (Finset.card_le_card sub)⟩
      have onotZ : o i ≠ n+t := by
        intro e
        exact proper i (Finset.eq_univ_of_forall (fun a => osig ▸ e.symm ▸ hz_full a))
      have wnO : w ≠ o i := by
        intro e
        have ps : p ∈ S i := sub plow
        exact phigh ((Heavy.mem_supp C y w p).mpr (by rw [e,ho]; exact decide_eq_true ⟨p,ps,by simp⟩))
      have unO : u ≠ o i := by
        intro e
        have ps : p ∈ S i := sub (usub pu)
        have hp := (Heavy.mem_supp C y u p).mpr (by rw [e,ho]; exact decide_eq_true ⟨p,ps,by simp⟩)
        rw [uhigh] at hp
        simp at hp
      have incl : ({u,w,o i} : Finset ℕ) ⊆ (assigned C (S i)).erase (n+t) := by
        intro v hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        rcases hv with rfl|rfl|rfl
        · exact Finset.mem_erase.mpr ⟨uNz,uass⟩
        · exact Finset.mem_erase.mpr ⟨nz,hi⟩
        · exact Finset.mem_erase.mpr ⟨onotZ,oass⟩
      have bound := Finset.card_le_card incl
      rw [Finset.card_triple_eq_three_iff.mpr ⟨ne_of_lt uw,unO,wnO⟩] at bound
      have := credited i touched
      omega)
  obtain ⟨v,vm,vv⟩ := (any _).mp hqtrue
  have vw : v<w := by by_contra h; simp [read,h] at vv
  have vq : q ∈ Heavy.supp C y v := (Heavy.mem_supp C y v q).mpr (by simpa [read,vw,test] using vv)
  have uv : u ≠ v := by
    intro e; rw [←e,uhigh] at vq; simp at vq
  let P := g.inputs.toFinset
  have hp : P.card ≤ 2 := (List.toFinset_card_le g.inputs).trans len
  have pair : P = {u,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl
      · simpa [P] using um
      · simpa [P] using vm
    · simpa [Finset.card_pair uv] using hp
  have highV : S i ⊆ Heavy.supp C y v := by
    intro a ha
    have aw : a ∈ Heavy.supp C y w := highR.symm ▸ ha
    obtain ⟨b,bm,bon⟩ := (any _).mp ((Heavy.mem_supp C y w a).mp aw)
    have bmem : b ∈ P := by simpa [P] using bm
    rw [pair] at bmem
    simp only [Finset.mem_insert,Finset.mem_singleton] at bmem
    rcases bmem with eq | eq
    · have au := (Heavy.mem_supp C y u a).mpr (by simpa [eq,read,uw] using bon)
      rw [uhigh] at au
      simp at au
    · exact (Heavy.mem_supp C y v a).mpr (by simpa [eq,read,vw] using bon)
  have soundV : value C (fun p => decide (p ∉ S i)) v=false := by
    apply Bool.eq_false_iff.mpr
    intro e
    have h := (any (fun p => decide (p ∉ S i))).mpr ⟨v,vm,by simpa only [read,ite_eq_left vw] using e⟩
    rw [soundR] at h
    contradiction
  have hci := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2
  have two : 2 ≤ (S i).card := by omega
  have hdi := (Finset.mem_filter.mp hi).2
  have pos : (S i).Nonempty := Finset.card_pos.mp (by omega)
  have beforeNo (a) (av : a<w) : ¬(S i ⊆ support C a ∧ Heavy.supp C y a = S i) ∨ andAt C n a := by
    left
    rintro ⟨lo,hs⟩
    have ls : support C a ⊆ S i := by
      by_contra he
      apply earlier a av
      exact ⟨Finset.sdiff_nonempty.mpr (by rwa [hs]),hs.symm ▸ pos⟩
    have eq : a=o i := saturated_refund_is_output S C o y B hlin ho hB sat i (hDB i hdi two) a
      (Finset.Subset.antisymm ls lo) hs
    omega
  have unordered (a) (ar : a ∈ Finset.Ico n (n+C.size)) (ane : a ≠ n+t) (aA : a ∉ A) (aF : a ∉ F) :
      (∃ j, a ∈ assigned C (S j) ∧ (j ∈ underDisjoint C S y → andAt C n a)) ∨
      (∃ j ∈ underDisjoint C S y, ¬andAt C n a ∧ S j ⊆ support C a ∧
        Heavy.supp C y a = S j ∧ value C (fun p => decide (p ∉ S j)) a = false) := by
    rcases roles a ar ane aA aF with own | ⟨j,hj,op,sub,sig,off,_⟩
    · exact Or.inl own
    · exact Or.inr ⟨j,hj,op,sub,sig,off⟩
  have small := sound_prefix_small C S y t w A F hg hu hz_high hy hyPos hlin earlier
    (fun a ha => (hF a ha).1) (fun a ha => (hA a ha).2) unordered i hi beforeNo v vw soundV
  have bound := Finset.card_le_card highV
  omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem tight_crossing_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : y.card = 3)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (profile : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
      (4 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+7) ∨
      (7 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+8)) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m := by
  classical
  by_contra bad
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  have bc : 4 ≤ B.card := by
    change (4 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+7) ∨
      (7 ≤ B.card ∧ (∑ i ∈ B, (S i).card) ≤ 5*B.card+8) at profile
    rcases profile with h | h <;> omega
  obtain ⟨sat,hDB,credit,A,F,Fpos,hF,hA,roles⟩ :=
    tight_crossing_configuration S C o t y hk hlin hg hu ho hl hy bad profile
  have hB (i) (hi : i ∈ B) : Disjoint (S i) y ∧ 2 ≤ (S i).card := by
    obtain ⟨dis,_,big⟩ := (Finset.mem_filter.mp hi).2
    exact ⟨dis,by omega⟩
  have hBU (i) (hi : i ∈ B) : i ∈ underDisjoint C S y := by
    obtain ⟨dis,under,_⟩ := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,under⟩,dis⟩
  have proper (i) : S i ≠ Finset.univ := by
    intro e
    obtain ⟨j,hj,ne⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show ({i} : Finset (Fin m)).card < B.card by rw [Finset.card_singleton]; omega)
    have h := hlin j i (fun eq => ne (Finset.mem_singleton.mpr eq))
    rw [e,Finset.inter_univ] at h
    exact Nat.not_succ_le_self _ ((hB j hj).2.trans h)
  have hfull (p : Fin n) : p ∈ support C (n+t) := by
    apply (mem_support _ _ _).mpr
    apply hl
    have h : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext q; simp
    rw [h,Finset.card_singleton,hk]
    decide
  have zero := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have hz := (terminal_switch_closed C y t hg hu zero hy).2
  have nsmall : 2 ≤ n := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<B.card by omega)
    exact (hB i hi).2.trans (by simpa using Finset.card_le_univ (S i))
  have none := no_first_mixed_signature C S y t o A F B nsmall (Finset.card_pos.mp (by omega))
    proper hlin hg hu ho hy hz hfull hA hF (by exact sat.le) hB hDB hBU credit roles
  obtain ⟨v,hv⟩ := Fpos
  exact none v (hF v hv).1

end L_meta_997.Small















namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem bounded_fold_crossing_lower {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C D : Circuit) (o : Fin m → ℕ) (t v : ℕ) (y : Finset (Fin n)) (B : Finset (Fin m)) (A Q : Finset ℕ)
    (hk : y.card=3) (hs : ∀ i ∈ B, Disjoint (S i) y)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (sz : D.size=C.size) (after : n+t<v) (deadSupport : support (n:=n) D v=∅)
    (readerRole : andAt C n v ∨ ∀ i, v∉assigned C (S i))
    (readerNotOut : ∀ i, ¬Disjoint (S i) y → o i≠v)
    (sameSupport : ∀ w, w≠v → support (n:=n) D w = support C w)
    (sameOp : ∀ w, n≤w → w≠v → w≠n+t → (andAt D n w ↔ andAt C n w))
    (hotA : ∀ w ∈ A, value C (fun p => decide (p ∈ y)) w=true)
    (low : ∀ w ∈ Finset.Ico n (n+D.size), w ∉ A → w≠v → w≠n+t → ¬andAt D n w → w ∈ B.biUnion (fun j => highOrGates C y (S j)) →
      w ∈ Q ∨ ∃ i, ¬Disjoint (S i) y ∧ (assigned D (S i)).card+1≤min y.card (S i).card ∧ w ∈ assigned D (S i)) :
    ∃ E : Finset (Fin m), (∑ i ∈ B, ((S i).card-1)) ≤ E.card+Q.card+1 ∧
      ∀ i ∈ E, ¬ Disjoint (S i) y ∧ (S i).card=3 ∧ ∃ w j,
        n+t<w ∧ w<o i ∧ assigned C (S i)={w,o i} ∧ Disjoint y (S j) ∧
        w ∈ highOrGates C y (S j) ∧ (support C w \ S j).Nonempty ∧ (Heavy.supp C y w \ S i).Nonempty := by
  classical
  let H := B.biUnion (fun j => highOrGates C y (S j))
  let W := H \ insert v Q
  let χ : Fin n → Bool := fun p => decide (p ∈ y)
  have oldHigh : ∀ w ∈ H, ¬andAt C n w ∧ w < n+C.size ∧ n ≤ w ∧ value C χ w=false := by
    intro w hw
    obtain ⟨j,hj,hj'⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hf,hA⟩ := Finset.mem_filter.mp hj'
    obtain ⟨wr,_,_,off⟩ := Finset.mem_filter.mp hf
    exact ⟨hA,(Finset.mem_Ico.mp wr).2,(Finset.mem_Ico.mp wr).1,off⟩
  have h0 := hl (fun _ => false) (by simpa using (show 0<y.card by omega))
  have swHigh := (terminal_switch_closed C y t hg hu h0 hy).2
  have exclusions (w) (hw : w∈H) : w≠n+t ∧ w ∉ A := by
    refine ⟨?_,?_⟩
    · intro eq
      obtain ⟨j,hj,hj'⟩ := Finset.mem_biUnion.mp hw
      have c := (Finset.mem_filter.mp (Finset.mem_filter.mp hj').1).2.2.1
      rw [eq,swHigh,Finset.card_empty] at c
      omega
    · intro ha
      exact Bool.noConfusion ((hotA w ha).symm.trans (oldHigh w hw).2.2.2)
  have rank : (∑ i ∈ B, ((S i).card-1)) ≤ H.card := by
    have pair : (B : Set (Fin m)).PairwiseDisjoint (fun i => highOrGates C y (S i)) := by
      intro i _ j _ ne
      exact (Heavy.heavy_disjoint C y (S i) (S j) (hlin i j ne)).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    rw [show H.card=∑ i ∈ B, (highOrGates C y (S i)).card from Finset.card_biUnion pair]
    exact Finset.sum_le_sum (fun i hi => by
      have h := high_or_count C y (S i) (o i) t (hs i hi).symm hg hu (ho i) h0 hy
      omega)
  have ow (w) (hw : w∈W) : ∃ i, ¬Disjoint (S i) y ∧ (assigned D (S i)).card+1≤min y.card (S i).card ∧ w ∈ assigned D (S i) := by
    obtain ⟨wh,wq⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hz,ha⟩ := exclusions w wh
    have hv : w≠v := fun e => wq (Finset.mem_insert.mpr (Or.inl e))
    obtain ⟨hop,up,lo,_⟩ := oldHigh w wh
    have wi : w∈Finset.Ico n (n+D.size) := Finset.mem_Ico.mpr ⟨lo,sz.symm ▸ up⟩
    exact (low w wi ha hv hz (fun ha => hop ((sameOp w lo hv hz).mp ha)) wh).resolve_left (fun h => wq (Finset.mem_insert_of_mem h))
  have coldout (i) (hi : ¬Disjoint (S i) y) : value C χ (o i) = true := by
    obtain ⟨p,hp,py⟩ := Finset.not_disjoint_iff.mp hi
    rw [ho]
    exact decide_eq_true ⟨p,hp,decide_eq_true py⟩
  have neqv (i) (hi : ¬Disjoint (S i) y) : o i≠v := by
    exact readerNotOut i hi
  have modelOutput (i) (hi : ¬Disjoint (S i) y) : support D (o i) = S i := by
    rw [sameSupport _ (neqv i hi)]
    ext p
    rw [mem_support,ho]
    simp
  have modelOwn (i) (hi : ¬Disjoint (S i) y) (big : 2 ≤ (S i).card) : o i ∈ assigned D (S i) := by
    have hbig : 2 ≤ (support (n:=n) D (o i)).card := by rwa [modelOutput i hi]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate D _ hbig),by rw [modelOutput i hi],hbig⟩
  have owUnique (i) (hi : ¬Disjoint (S i) y) (small : (assigned D (S i)).card+1≤min y.card (S i).card) (w w') (hw : w∈W) (hw' : w'∈W)
      (asw : w∈assigned D (S i)) (asw' : w'∈assigned D (S i)) : w=w' := by
    by_contra ne
    have nw : w≠o i := by intro e; exact Bool.noConfusion ((oldHigh w (Finset.mem_sdiff.mp hw).1).2.2.2.symm.trans (e.symm ▸ coldout i hi))
    have nw' : w'≠o i := by intro e; exact Bool.noConfusion ((oldHigh w' (Finset.mem_sdiff.mp hw').1).2.2.2.symm.trans (e.symm ▸ coldout i hi))
    have big := (Finset.mem_filter.mp asw).2.2.trans (Finset.card_le_card (Finset.mem_filter.mp asw).2.1)
    have sub : ({w,w',o i}:Finset ℕ) ⊆ assigned D (S i) :=
      Finset.insert_subset asw (Finset.insert_subset asw' (Finset.singleton_subset_iff.mpr (modelOwn i hi big)))
    have count := Finset.card_le_card sub
    rw [Finset.card_triple_eq_three_iff.mpr ⟨ne,nw,nw'⟩] at count
    omega
  let I := Finset.univ.filter (fun i => ¬Disjoint (S i) y ∧ (assigned D (S i)).card+1≤min y.card (S i).card ∧ ∃ w∈W, w∈assigned D (S i))
  let E := I.filter (fun i => v∉assigned C (S i))
  let J := I \ E
  have subOwner (w : W) := ow w.val w.property
  choose owner hOwner using subOwner
  have inj : Function.Injective owner := by
    intro w w' eq
    apply Subtype.ext
    have e := hOwner w
    exact owUnique (owner w) e.1 e.2.1 w.val w'.val w.property w'.property e.2.2
      (by simpa only [←eq] using (hOwner w').2.2)
  have countI : W.card≤I.card := by
    have cap := Finset.card_le_card_of_injOn owner (s:=(Finset.univ : Finset W)) (t:=I)
      (fun w _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hOwner w).1,(hOwner w).2.1,w.val,w.property,(hOwner w).2.2⟩) inj.injOn
    simpa using cap
  have jLe : J.card≤1 := by
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    by_contra neq
    have vi : v ∈ assigned C (S i) := by
      obtain ⟨a,b⟩ := Finset.mem_sdiff.mp hi
      by_contra h
      exact b (Finset.mem_filter.mpr ⟨a,h⟩)
    have vj : v ∈ assigned C (S j) := by
      obtain ⟨a,b⟩ := Finset.mem_sdiff.mp hj
      by_contra h
      exact b (Finset.mem_filter.mpr ⟨a,h⟩)
    have sub : support C v ⊆ S i ∩ S j := fun p hp =>
      Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp vi).2.1 hp,(Finset.mem_filter.mp vj).2.1 hp⟩
    have cap := (Finset.card_le_card sub).trans (hlin i j neq)
    have big := (Finset.mem_filter.mp vi).2.2
    omega
  have split := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ I :
    E⊆I)
  change J.card+E.card=I.card at split
  have loss : (H ∩ insert v Q).card + J.card ≤ Q.card+1 := by
    rcases readerRole with hand | noAssigned
    · have inc : H ∩ insert v Q ⊆ Q := by
        intro w hw
        obtain ⟨wH,wQ⟩ := Finset.mem_inter.mp hw
        rcases Finset.mem_insert.mp wQ with eq | h
        · exact ((oldHigh w wH).1 (eq.symm ▸ hand)).elim
        · exact h
      have le := Finset.card_le_card inc
      omega
    · have jEmpty : J.card=0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        obtain ⟨ii,ni⟩ := Finset.mem_sdiff.mp hi
        exact ni (Finset.mem_filter.mpr ⟨ii,noAssigned i⟩)
      have le := (Finset.card_le_card (Finset.inter_subset_right (s₁:=H) (s₂:=insert v Q))).trans
        (Finset.card_insert_le _ _)
      omega
  have splitH := Finset.card_sdiff_add_card_inter H (insert v Q)
  change W.card + (H ∩ insert v Q).card = H.card at splitH
  refine ⟨E,by omega,?_⟩

  intro i hi
  obtain ⟨hi,unfolded⟩ := Finset.mem_filter.mp hi
  obtain ⟨met,lim,w,hw,own⟩ := (Finset.mem_filter.mp hi).2
  have wh := (Finset.mem_sdiff.mp hw).1
  obtain ⟨j,hj,hhigh⟩ := Finset.mem_biUnion.mp wh
  have dis := hs j hj
  have wnez := (exclusions w wh).1
  have wnev : w≠v := fun e => (Finset.mem_sdiff.mp hw).2 (Finset.mem_insert.mpr (Or.inl e))
  have modelEq : assigned C (S i) = assigned D (S i) := by
    ext q
    by_cases e : q=v
    · subst q
      have vnot : v ∉ assigned D (S i) := by simp [assigned,deadSupport]
      simp [unfolded,vnot]
    · rw [assigned,assigned,Finset.mem_filter,Finset.mem_filter,sameSupport q e,sz]
  have bigD := (Finset.mem_filter.mp own).2.2.trans (Finset.card_le_card (Finset.mem_filter.mp own).2.1)
  have wno : w≠o i := by intro e; exact Bool.noConfusion ((oldHigh w wh).2.2.2.symm.trans (e.symm ▸ coldout i met))
  have pick : ({w,o i}:Finset ℕ) ⊆ assigned D (S i) :=
    Finset.insert_subset own (Finset.singleton_subset_iff.mpr (modelOwn i met bigD))
  have pickc := Finset.card_le_card pick
  rw [Finset.card_pair wno] at pickc
  have exactD : assigned D (S i)={w,o i} := (Finset.eq_of_subset_of_card_le pick (by rw [Finset.card_pair wno]; omega)).symm
  have exactC := modelEq.trans exactD
  have sizeAssign : (assigned C (S i)).card=2 := by rw [exactC,Finset.card_pair wno]
  have size : (S i).card=3 := by
    by_contra ne
    have gt : 3 < (S i).card := by omega
    have unders : (assigned C (S i)).card+1 < (S i).card := by
      rw [exactC,Finset.card_pair wno]
      omega
    have oc := low_many_private_ands C (S i) (o i) t (by omega : 2≤y.card) hg hu (ho i) hl unders
    have ownC := exactC.symm ▸ (Finset.mem_insert_self w ({o i}:Finset ℕ))
    have strict : ((assigned C (S i)).filter (andAt C n)).card < (assigned C (S i)).card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr
        ⟨w,ownC,fun h => (oldHigh w wh).1 (Finset.mem_filter.mp h).2⟩)
    rw [hk] at oc
    omega
  have cross := crossing_gate_in_suffix S C t y i j w hlin hg hu h0 hy met dis.symm
    (modelEq.symm ▸ own) (Finset.mem_filter.mp hhigh).1
  have late := cross.1
  have earlier : w<o i := by
    by_contra! h
    have hr := oldHigh w wh
    have idx : w-n<C.gates.length := by have up := hr.2.1; change w<n+C.gates.length at up; omega
    have bound := before_output_charge C (S i) (o i) t w ⟨w-n,idx⟩ (by simp; omega)
      (lt_of_le_of_ne h wno.symm) late y.card hg hu (ho i) hl (by omega)
    have contains : w ∈ (assigned C (S i)).erase (n+t) :=
      Finset.mem_erase.mpr ⟨wnez,by rw [exactC]; simp⟩
    have cut := Finset.ssubset_iff_of_subset (Finset.filter_subset (· < w) ((assigned C (S i)).erase (n+t))) |>.mpr
      ⟨w,contains,fun hm => Nat.lt_irrefl _ (Finset.mem_filter.mp hm).2⟩
    have smaller := Finset.card_lt_card cut
    have cap := Finset.card_erase_le (s:=assigned C (S i)) (a:=n+t)
    rw [hk,size] at bound
    omega
  exact ⟨met,size,w,j,late,earlier,exactC,dis.symm,hhigh,cross.2.1,cross.2.2⟩

end L_meta_997.Small





namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

lemma crossing_parent_signatures_from_support {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o t w : ℕ) (y : Finset (Fin n)) (i j : Fin m) (F : Finset ℕ)
    (roles : ∀ u ∈ Finset.Ico n (n+C.size), (support (n:=n) C u).card=1 → u∈F)
    (hg : hasAllowedGates C)
    (hu : ∀ a : Fin C.gates.length, (C.gates.get a).op = .not → (a : ℕ) = t)
    (hwa : n+t < w) (hwo : w < o) (hasg : assigned C (S i) = {w,o})
    (hw : w ∈ highOrGates C y (S j)) (hout : (support C w \ S j).Nonempty) :
    ∃ (u v : ℕ) (p r : Fin n), u ∈ F ∧ u ≠ v ∧ p ≠ r ∧
      support C u = {p} ∧ support C v = {r} ∧ p ∉ Heavy.supp C y u ∧
      value C (fun a => decide (a ∈ y)) u = false ∧
      value C (fun a => decide (a ∈ y)) v = false ∧
      support C w = {p,r} ∧ Heavy.supp C y w = Heavy.supp C y u ∪ Heavy.supp C y v ∧
      ((Heavy.supp C y u = ∅) → v ∈ F) := by
  classical
  have hwi : w ∈ assigned C (S i) := by simp [hasg]
  obtain ⟨_, hws, hwc⟩ := Finset.mem_filter.mp hwi
  obtain ⟨hhigh, hnand⟩ := Finset.mem_filter.mp hw
  obtain ⟨hrange,hupper,hhighCard,hcold⟩ := Finset.mem_filter.mp hhigh
  obtain ⟨hn,hnw⟩ := Finset.mem_Ico.mp hrange
  have hidx : w-n < C.gates.length := by change w<n+C.gates.length at hnw; omega
  let g := C.gates[w-n]
  obtain ⟨hop, hlen⟩ := hg g (List.getElem_mem _)
  have hor : g.op = .or := by
    rcases hop with ha | ho | hz
    · exact (hnand (by simp [andAt, g, hidx, ha])).elim
    · exact ho
    · have e := hu ⟨w-n,hidx⟩ hz
      change w-n=t at e
      omega
  have read (x : Fin n → Bool) :
      value C x w = true ↔ ∃ v ∈ g.inputs, v < w ∧ value C x v = true := by
    rw [gate_value C x w hn hnw]
    change g.op.eval (g.inputs.map (fun v => if v<w then value C x v else false)) = true ↔ _
    simp [hor, GateOp.eval]
  have parentSub (v : ℕ) (_hv : v ∈ g.inputs) (hv' : v < w) : support (n:=n) C v ⊆ support C w := by
    intro p hp
    exact (mem_support C w p).mpr ((read _).mpr ⟨v,_hv,hv',(mem_support C v p).mp hp⟩)
  have parentCold (v : ℕ) (hv : v ∈ g.inputs) (hv' : v < w) :
      value C (fun a => decide (a ∈ y)) v = false := by
    apply Bool.eq_false_iff.mpr
    intro hot
    have won := (read _).mpr ⟨v,hv,hv',hot⟩
    rw [hcold] at won
    contradiction
  have parentCard (v : ℕ) (hv : v ∈ g.inputs) (hv' : v < w) :
      (support (n:=n) C v).card ≤ 1 := by
    by_contra! big
    have ass : v ∈ assigned C (S i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C v big), (parentSub v hv hv').trans hws, big⟩
    rw [hasg] at ass
    rcases (by simpa using ass : v=w ∨ v=o) with e | e <;> omega
  have parentExc (v : ℕ) (hv : v ∈ g.inputs) (hv' : v < w) (hnv : n ≤ v)
      (nonempty : (support (n:=n) C v).Nonempty) : v ∈ F := by
    apply roles v (Finset.mem_Ico.mpr ⟨hnv,by omega⟩)
    have lo := Finset.card_pos.mpr nonempty
    have hi := parentCard v hv hv'
    omega
  obtain ⟨q,hq⟩ := hout
  obtain ⟨u,hug,huw,huq⟩ := (read _).mp ((mem_support C w q).mp (Finset.mem_sdiff.mp hq).1)
  have hnu : n ≤ u := by
    by_contra! hun
    let raw : Fin n := ⟨u,hun⟩
    have eq : raw=q := by
      change value C (fun p => decide (p=q)) raw = true at huq
      simpa [input_value] using huq
    have up : value C (fun p => decide (p ∈ y ∨ p=q)) u = true := by
      change value C (fun p => decide (p ∈ y ∨ p=q)) raw = true
      simp [input_value,eq]
    have hin := hupper ((Heavy.mem_supp C y w q).mpr ((read _).mpr ⟨u,hug,huw,up⟩))
    exact (Finset.mem_sdiff.mp hq).2 hin
  have huF := parentExc u hug huw hnu ⟨q,(mem_support C u q).mpr huq⟩
  have huSupp : support C u = {q} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr ((mem_support C u q).mpr huq))
    simpa using parentCard u hug huw
  have less : ({q} : Finset (Fin n)).card < (support (n:=n) C w).card := by simp; omega
  obtain ⟨r,hrw,hrq⟩ := Finset.exists_mem_notMem_of_card_lt_card less
  obtain ⟨v,hvg,hvw,hvr⟩ := (read _).mp ((mem_support C w r).mp hrw)
  have hvu : v ≠ u := by
    intro e
    exact hrq (huSupp ▸ (mem_support C u r).mpr (e ▸ hvr))
  have hrs : support C v = {r} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr ((mem_support C v r).mpr hvr))
    simpa using parentCard v hvg hvw
  have hpair : ∀ b ∈ g.inputs, b=u ∨ b=v := by
    intro b hb
    have sub : ({u,v,b} : Finset ℕ) ⊆ g.inputs.toFinset := by
      refine Finset.insert_subset (List.mem_toFinset.mpr hug)
        (Finset.insert_subset (List.mem_toFinset.mpr hvg)
          (Finset.singleton_subset_iff.mpr (List.mem_toFinset.mpr hb)))
    have cap := (Finset.card_le_card sub).trans ((List.toFinset_card_le g.inputs).trans hlen)
    by_contra! h
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton] at cap
    · omega
    · simpa using Ne.symm h.2
    · simp [hvu.symm, h.1.symm]
  have eqHigh : Heavy.supp C y w = Heavy.supp C y u ∪ Heavy.supp C y v := by
    ext a
    rw [Heavy.mem_supp, read, Finset.mem_union, Heavy.mem_supp, Heavy.mem_supp]
    constructor
    · rintro ⟨b,hb,bl,hba⟩
      rcases hpair b hb with rfl | rfl
      · exact Or.inl hba
      · exact Or.inr hba
    · rintro (h | h)
      · exact ⟨u,hug,huw,h⟩
      · exact ⟨v,hvg,hvw,h⟩
  have loss : q ∉ Heavy.supp C y u := by
    intro hon
    have hon' : q ∈ Heavy.supp C y w := eqHigh.symm ▸ Finset.mem_union.mpr (Or.inl hon)
    exact (Finset.mem_sdiff.mp hq).2 (hupper hon')
  have coldv := parentCold v hvg hvw
  have hvF (empty : Heavy.supp C y u = ∅) : v ∈ F := by
    by_cases bg : n ≤ v
    · exact parentExc v hvg hvw bg ⟨r,(mem_support C v r).mpr hvr⟩
    have rawLt : v < n := by omega
    let raw : Fin n := ⟨v,rawLt⟩
    have notY : raw ∉ y := by
      intro hi
      change value C (fun a => decide (a ∈ y)) raw = false at coldv
      rw [input_value] at coldv
      simp [hi] at coldv
    have sig : Heavy.supp C y v = {raw} := by
      ext a
      rw [Heavy.mem_supp]
      change value C (fun p => decide (p ∈ y ∨ p=a)) raw = true ↔ _
      rw [input_value]
      simp [notY, eq_comm]
    rw [eqHigh,empty,Finset.empty_union,sig,Finset.card_singleton] at hhighCard
    omega
  refine ⟨u,v,q,r,huF,hvu.symm,by simpa [eq_comm] using hrq,huSupp,hrs,loss,parentCold u hug huw,coldv,?_,eqHigh,hvF⟩
  ext a
  rw [mem_support, read]
  constructor
  · rintro ⟨b,hb,bl,hba⟩
    rcases hpair b hb with e | e
    · subst b
      have h : a ∈ support C u := (mem_support C u a).mpr hba
      rw [huSupp] at h
      exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))
    · subst b
      have h : a ∈ support C v := (mem_support C v a).mpr hba
      rw [hrs] at h
      exact Finset.mem_insert_of_mem h
  · intro h
    rcases Finset.mem_insert.mp h with eq | hr
    · subst a
      exact ⟨u,hug,huw,huq⟩
    · simp only [Finset.mem_singleton] at hr
      subst a
      exact ⟨v,hvg,hvw,hvr⟩

end L_meta_997.Small

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

-- A hot AND output with an exact two-gate singleton assignment would need
-- both parents to carry exterior points. Their union is a light false positive.
theorem two_assigned_hot_output_not_and {n : ℕ} (C D : Circuit) (f : ℕ → ℕ)
    (T : Finset (Fin n)) (w o : ℕ) (xY : Fin n → Bool) (large : 2≤T.card)
    (hg : hasAllowedGates C) (gd : good D)
    (agreement : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card≤2 →
      ∀ v, value D x (f v)=value C x v)
    (out : ∀ x : Fin n → Bool, value C x o=decide (∃ p ∈ T, x p=true))
    (assignment : assigned C T={w,o})
    (cold : value C xY w=false) (hot : value C xY o=true) :
    ¬andAt C n o := by
  classical
  intro andOp
  have os : support C o=T := by
    ext p
    rw [mem_support,out]
    simp
  have ran := support_gate C o (show 2≤(support (n:=n) C o).card by rw [os]; exact large)
  have idx : o-n<C.gates.length := by have h := ran.2; change o<n+C.gates.length at h; omega
  let g := C.gates[o-n]
  have isAnd : g.op=.and := by
    unfold andAt at andOp
    rw [List.getElem?_eq_getElem idx,Option.map_some] at andOp
    exact Option.some.inj andOp
  let rd (x : Fin n → Bool) (u : ℕ) := if u<o then value C x u else false
  have eval (x : Fin n → Bool) : value C x o=g.op.eval (g.inputs.map (rd x)) :=
    gate_value C x o ran.1 ran.2
  have all (x : Fin n → Bool) : value C x o=true ↔ ∀ u ∈ g.inputs, rd x u=true := by
    rw [eval,isAnd]
    simp [GateOp.eval]
  let U := g.inputs.toFinset
  have small : U.card≤2 := (List.toFinset_card_le g.inputs).trans (hg g (List.getElem_mem _)).2
  have older (u) (hu : u∈U) : u<o := by
    have h := (all xY).mp hot u (by simpa [U] using hu)
    by_cases lt : u<o
    · exact lt
    · simp [rd,lt] at h
  have exterior (u : U) : ∃ p ∈ support C u.val, p∉T := by
    have lt := older u.val u.property
    have um : u.val∈g.inputs := List.mem_toFinset.mp u.property
    have sub : T ⊆ support C u.val := by
      intro p hp
      apply (mem_support _ _ _).mpr
      have on := (mem_support C o p).mp (os.symm ▸ hp)
      simpa only [rd,ite_eq_left lt] using (all _).mp on u.val um
    by_contra! contained
    have sig : support C u.val=T := Finset.Subset.antisymm contained sub
    have big : 2≤(support (n:=n) C u.val).card := by rwa [sig]
    have ass : u.val∈assigned C T := Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr (support_gate C _ big),sig.le,big⟩
    have eq : u.val=w := by
      rw [assignment] at ass
      simpa [show u.val≠o from ne_of_lt lt] using ass
    have on := (all xY).mp hot u.val um
    rw [show rd xY u.val=value C xY u.val by simp [rd,lt],eq,cold] at on
    contradiction
  choose p picked outside using exterior
  let X := U.attach.image p
  have xsmall : X.card≤2 := (Finset.card_image_le.trans (by simpa using small))
  let x : Fin n → Bool := fun q => decide (q∈X)
  have smx : (Finset.univ.filter (fun q => x q=true)).card≤2 := by simpa [x] using xsmall
  have xnon : ∀ q ∈ T, x q=false := by
    intro q hq
    apply decide_eq_false
    intro qx
    obtain ⟨u,_,he⟩ := Finset.mem_image.mp qx
    exact outside u (he.symm ▸ hq)
  have on : value C x o=true := by
    apply (all x).mpr
    intro u hu
    have uU : u∈U := by simpa [U] using hu
    let a : U := ⟨u,uU⟩
    let xs : Fin n → Bool := fun q => decide (q=p a)
    have onSmall : value C xs u=true := (mem_support C u (p a)).mp (picked a)
    have smxs : (Finset.univ.filter (fun q => xs q=true)).card≤2 := by
      have eq : (Finset.univ.filter (fun q => xs q=true))={p a} := by ext q; simp [xs]
      rw [eq,Finset.card_singleton]
      decide
    have sub (q) (hq : xs q=true) : x q=true := by
      have e : q=p a := of_decide_eq_true hq
      apply decide_eq_true
      exact Finset.mem_image.mpr ⟨a,Finset.mem_attach U a,e.symm⟩
    have hon := value_mono D gd xs x sub (f u) ((agreement xs smxs u).trans onSmall)
    change (if u<o then value C x u else false)=true
    rw [ite_eq_left (older u uU),←agreement x smx u]
    exact hon
  rw [out] at on
  obtain ⟨q,hq,yes⟩ := of_decide_eq_true on
  exact Bool.noConfusion ((xnon q hq).symm.trans yes)

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

theorem regular_crossing_has_raw_partner {n : ℕ} (C : Circuit) (T y : Finset (Fin n))
    (t v w o : ℕ) (p r : Fin n) (pr : p≠r) (three : T.card=3)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t) (order : n+t<w ∧ w<o)
    (out : ∀ x : Fin n → Bool, value C x o=decide (∃ p ∈ T, x p=true))
    (assignedEq : assigned C T={w,o}) (ws : support C w={p,r})
    (wCold : value C (fun q => decide (q∈y)) w=false)
    (oHot : value C (fun q => decide (q∈y)) o=true)
    (vCold : value C (fun q => decide (q∈y)) v=false)
    (onlySingleton : ∀ u∈Finset.Ico n (n+C.size), (support (n:=n) C u).card=1 → u=v)
    (notAnd : ¬andAt C n o) :
    ∃ s∈T, s≠p ∧ s∈y := by
  classical
  have os : support C o=T := by ext q; rw [mem_support,out]; simp
  have big : 2≤(support (n:=n) C o).card := by rw [os,three]; decide
  obtain ⟨lo,up⟩ := support_gate C o big
  have idx : o-n<C.gates.length := by change o<n+C.gates.length at up; omega
  let g := C.gates[o-n]
  obtain ⟨op,arity⟩ := hg g (List.getElem_mem _)
  have isOR : g.op=.or := by
    rcases op with hand | hor | hn
    · apply False.elim
      apply notAnd
      unfold andAt
      rw [List.getElem?_eq_getElem idx,Option.map_some]
      exact congrArg some hand
    · exact hor
    · have eq := hu ⟨o-n,idx⟩ hn
      change o-n=t at eq
      omega
  let rd (x : Fin n → Bool) (u : ℕ) := if u<o then value C x u else false
  have eval (x : Fin n → Bool) : value C x o=g.op.eval (g.inputs.map (rd x)) :=
    gate_value C x o lo up
  have any (x : Fin n → Bool) : value C x o=true ↔ ∃ a∈g.inputs, a<o ∧ value C x a=true := by
    rw [eval,isOR]
    simp [GateOp.eval,rd]
  have parentSub (a) (ha : a∈g.inputs) (lt : a<o) : support C a⊆T := by
    intro q hq
    have on := (any _).mpr ⟨a,ha,lt,(mem_support _ _ _).mp hq⟩
    exact os ▸ (mem_support C o q).mpr on
  have earlier (a) (ha : a∈g.inputs) (lt : a<o) (sz : 2≤(support (n:=n) C a).card) :
      a=w := by
    have ass : a∈assigned C T := Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr (support_gate C a sz),parentSub a ha lt,sz⟩
    rw [assignedEq] at ass
    simpa [ne_of_lt lt] using ass
  have src (q) (hq : q∈T) : ∃ a∈g.inputs, a<o ∧ q∈support C a := by
    obtain ⟨a,ha,lt,on⟩ := (any _).mp ((mem_support C o q).mp (os.symm ▸ hq))
    exact ⟨a,ha,lt,(mem_support _ _ _).mpr on⟩
  have lt : ({p,r} : Finset (Fin n)).card<T.card := by rw [Finset.card_pair pr,three]; decide
  obtain ⟨s,st,sout⟩ := Finset.exists_mem_notMem_of_card_lt_card lt
  obtain ⟨u,ui,uo,su⟩ := src s st
  have uNotW : u≠w := fun eq => sout (ws ▸ eq ▸ su)
  have uSingle : support C u={s} := by
    have h : (support (n:=n) C u).card≤1 := by
      by_contra! big
      exact uNotW (earlier u ui uo (by omega))
    exact (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr su) (by simpa)).symm
  let X : Fin n → Bool := fun q => decide (q∈y)
  have uHot : value C X u=true := by
    by_contra h
    obtain ⟨a,ha,ao,on⟩ := (any X).mp oHot
    have ne : u≠a := fun eq => h (eq.symm ▸ on)
    have both (b) (hb : b∈g.inputs) : b=u ∨ b=a := by
      have hset : ({u,a} : Finset ℕ) = g.inputs.toFinset := by
        apply Finset.eq_of_subset_of_card_le
        · intro v hv
          simp only [Finset.mem_insert,Finset.mem_singleton] at hv
          rcases hv with rfl|rfl
          · exact List.mem_toFinset.mpr ui
          · exact List.mem_toFinset.mpr ha
        · rw [Finset.card_pair ne]
          exact (List.toFinset_card_le _).trans arity
      have h : b∈({u,a}:Finset ℕ) := hset.symm ▸ List.mem_toFinset.mpr hb
      simpa using h
    have supports (q) (hq : q ∈ ({p,r} : Finset (Fin n))) : q ∈ support C a := by
      have qT := parentSub u ui uo su
      have fw : w∈assigned C T := assignedEq.symm ▸ Finset.mem_insert_self _ _
      have xT := (Finset.mem_filter.mp fw).2.1 (ws.symm ▸ hq)
      obtain ⟨b,hb,_ ,sb⟩ := src q xT
      rcases both b hb with rfl | rfl
      · have eq := Finset.mem_singleton.mp (uSingle ▸ sb)
        exact (sout (eq ▸ hq)).elim
      · exact sb
    have c := Finset.card_le_card supports
    rw [Finset.card_pair pr] at c
    have e := earlier a ha ao c
    exact Bool.noConfusion (wCold.symm.trans (e ▸ on))
  have raw : u<n := by
    by_contra! h
    have eq := onlySingleton u (Finset.mem_Ico.mpr ⟨h,uo.trans up⟩)
      (by rw [uSingle,Finset.card_singleton])
    exact Bool.noConfusion (vCold.symm.trans (eq ▸ uHot))
  let a : Fin n := ⟨u,raw⟩
  have ea : a=s := by
    have p := (mem_support C u s).mp su
    change value C (fun q => decide (q=s)) a = true at p
    rw [input_value] at p
    exact of_decide_eq_true p
  change value C X a=true at uHot
  rw [input_value,ea] at uHot
  exact ⟨s,st,fun e => sout (e ▸ Finset.mem_insert_self _ _),of_decide_eq_true uHot⟩

end L_meta_997.Light

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

theorem crossing_triples_singleton_cap {n m : ℕ} (S : Fin m → Finset (Fin n)) (C D : Circuit)
    (f : ℕ → ℕ) (o : Fin m → ℕ) (t v : ℕ) (y : Finset (Fin n)) (E : Finset (Fin m))
    (hlin : rowLinearity S) (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (hout : rowOutputs C S o) (gd : good D)
    (agreement : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card≤2 →
      ∀ w, value D x (f w)=value C x w)
    (onlySingleton : ∀ u∈Finset.Ico n (n+C.size), (support (n:=n) C u).card=1 → u=v)
    (triples : ∀ i ∈ E, ¬ Disjoint (S i) y ∧ (S i).card=3 ∧ ∃ w j,
      n+t<w ∧ w<o i ∧ assigned C (S i)={w,o i} ∧ Disjoint y (S j) ∧
      w ∈ highOrGates C y (S j) ∧ (support C w \ S j).Nonempty) : E.card ≤ y.card := by
  classical
  have paired (i : E) : ∃ p∈S i.val, support C v={p} ∧ ∃ s∈S i.val, s≠p ∧ s∈y := by
    obtain ⟨met,three,w,j,after,earlier,paid,_,high,lost⟩ := triples i.val i.property
    obtain ⟨u,_,p,r,uf,_,distinct,sig,_,_,cold,_,row,_,_⟩ :=
      crossing_parent_signatures_from_support S C (o i.val) t w y i.val j {v}
        (fun a ha small => Finset.mem_singleton.mpr (onlySingleton a ha small))
        hg hu after earlier paid high lost
    have eq : u=v := Finset.mem_singleton.mp uf
    have wown : w ∈ assigned C (S i.val) := by simp [paid]
    have pi : p∈S i.val :=
      (Finset.mem_filter.mp wown).2.1 (row.symm ▸ Finset.mem_insert_self _ _)
    have hot : value C (fun q => decide (q∈y)) (o i.val)=true := by
      obtain ⟨q,qi,qy⟩ := Finset.not_disjoint_iff.mp met
      rw [hout]
      exact decide_eq_true ⟨q,qi,decide_eq_true qy⟩
    have no := two_assigned_hot_output_not_and C D f (S i.val) w (o i.val)
      (fun q => decide (q∈y)) (by rw [three]; decide) hg gd agreement (hout i.val) paid
      (Finset.mem_filter.mp (Finset.mem_filter.mp high).1).2.2.2 hot
    exact ⟨p,pi,eq ▸ sig,regular_crossing_has_raw_partner C (S i.val) y t v w (o i.val)
      p r distinct three hg hu ⟨after,earlier⟩ (hout i.val) paid row
      (Finset.mem_filter.mp (Finset.mem_filter.mp high).1).2.2.2 hot (eq ▸ cold) onlySingleton no⟩
  choose p pp sig s ss ne sy using paired
  let pack : E → y := fun i => ⟨s i,sy i⟩
  have packed : Function.Injective pack := by
    intro i j equal
    have ssame : s i=s j := congrArg Subtype.val equal
    have psame : p i=p j := by
      have e : ({p i} : Finset (Fin n)) = {p j} := (sig i).symm.trans (sig j)
      exact Finset.singleton_inj.mp e
    apply Subtype.ext
    by_contra different
    have subset : ({p i,s i} : Finset (Fin n)) ⊆ S i.val ∩ S j.val :=
      Finset.insert_subset (Finset.mem_inter.mpr ⟨pp i,psame.symm ▸ pp j⟩)
        (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mpr ⟨ss i,ssame.symm ▸ ss j⟩))
    have cnt := (Finset.card_le_card subset).trans (hlin i.val j.val different)
    rw [Finset.card_pair (ne i).symm] at cnt
    omega
  simpa using Fintype.card_le_of_injective pack packed

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

-- A tight folded projection leaves one possible singleton wire outside the
-- raw inputs. Erasing this reader can reduce the credit of at most one row.
open Classical in
theorem tight_projection_regular_crossings {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (d : Fin m) (hk : y.card=3)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card≤1)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t) (ho : computesRows C S o)
    (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p∈y)) (n+t)=false)
    (bad : ¬((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length+(refunds S C y).card+m)) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
    d∈B → (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+4 →
    ∃ (D : Circuit) (f : ℕ → ℕ) (v : ℕ) (E : Finset (Fin m)),
      good D ∧
      (∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card≤2 →
        ∀ w, value D x (f w)=value C x w) ∧
      (∀ w∈Finset.Ico n (n+C.size), (support (n:=n) C w).card=1 → w=v) ∧
      B.card+3≤E.card ∧
      ∀ i∈E, ¬Disjoint (S i) y ∧ (S i).card=3 ∧ ∃ w j,
        n+t<w ∧ w<o i ∧ assigned C (S i)={w,o i} ∧ Disjoint y (S j) ∧
        w∈highOrGates C y (S j) ∧ (support C w \ S j).Nonempty ∧
        (Heavy.supp C y w \ S i).Nonempty := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
  change d∈B → (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+4 → _
  intro hd hquota
  have dat (i) (hi : i∈B) := (Finset.mem_filter.mp hi).2
  have quote : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ y.card+2≤(S i).card)
    (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+1 := by
    rw [hk]
    change (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+3+1
    omega
  obtain ⟨a,ta,rd⟩ := switch_has_reader C (S d) (o d) t (by omega : 2≤y.card)
    hg hu (ho d) hl (dat d hd).2.1
  let v := n+a.val
  have av : n+t<v := by dsimp [v]; omega
  have ar : v<n+C.size := Nat.add_lt_add_left a.isLt n
  obtain ⟨D,f,gD,sameSize,dead,unchanged,agree,_,_⟩ := fold_one_reader_stable C t a ta rd hg hu hl
  obtain ⟨A,ac,range,aRoles⟩ := guard_hot_gates C t y (by omega : 0<y.card) hg hu hl hy
  have tproj := folded_model_tight S d C o t y (by omega) hlin hg hu ho hl (dat d hd).2.1 quote
    bad D f v gD sameSize av ar dead unchanged agree A ac range (fun w hw => (aRoles w hw).1)
  have sing (p : Fin n) :
      (Finset.univ.filter (fun q : Fin n => decide (q=p)=true)).card<y.card := by
    have e : (Finset.univ.filter (fun q : Fin n => decide (q=p)=true))={p} := by ext q; simp
    rw [e,Finset.card_singleton,hk]
    decide
  have same (w) (nw : w≠v) : support (n:=n) D w=support C w := by
    ext p
    rw [mem_support,mem_support,←unchanged w nw,agree _ (sing p) w,unchanged w nw]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,v,dead]
  have assigns (i) : (assigned C (S i)).erase v = assigned D (S i) := by
    ext w
    by_cases eq : w=v
    · subst w
      simp [assigned,empty]
    · rw [Finset.mem_erase,assigned,assigned,Finset.mem_filter,Finset.mem_filter,same w eq,sameSize]
      simp [eq]
  let J := Finset.univ.filter (fun i => v∈assigned C (S i))
  have once : J.card≤1 := by
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    by_contra ne
    obtain ⟨_,si,bi⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hi).2
    obtain ⟨_,sj,_⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hj).2
    have sub : support C v ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨si hp,sj hp⟩
    have cp := (Finset.card_le_card sub).trans (hlin i j ne)
    omega
  have extra (i) : touchingCredit C t y (S i) ≤ if i∈J then 1 else 0 := by
    by_cases met : Disjoint (S i) y
    · simp [touchingCredit,met]
    have ne : i≠d := fun e => met (e.symm ▸ (dat d hd).1)
    have assignedDown : (assigned D (S i)).card+1=min y.card (S i).card := by
      simpa [met] using tproj.2.2.2.2.1 i ne
    have le := Finset.card_erase_le (s:=assigned C (S i)) (a:=n+t)
    have cs : (assigned C (S i)).card ≤ (assigned D (S i)).card + (if i∈J then 1 else 0) := by
      by_cases h : v∈assigned C (S i)
      · have hJ : i∈J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
        have e := Finset.card_erase_add_one h
        rw [assigns i] at e
        simp only [if_pos hJ]
        omega
      · have hJ : i∉J := fun eq => h (Finset.mem_filter.mp eq).2
        have e := assigns i
        rw [Finset.erase_eq_of_notMem h] at e
        simp [hJ,e]
    simp only [touchingCredit,met,ite_false]
    omega
  have credits : (∑ i, touchingCredit C t y (S i))≤1 := by
    have r := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin m))) (fun i _ => extra i)
    simpa using r.trans (by simpa [Finset.sum_boole] using once)
  have n5 : 5≤n := ((dat d hd).2.2).trans (by simpa using Finset.card_le_univ (S d))
  have only (w) (wr : w∈Finset.Ico n (n+C.size)) (wc : (support (n:=n) C w).card=1) : w=v := by
    by_contra wn
    have na : w∉A := by
      intro wa
      simp [(aRoles w wa).1] at wc
    have nz : w≠n+t := by
      intro zw
      have h : support (n:=n) C w=Finset.univ := by
        apply Finset.eq_univ_of_forall
        intro p
        apply (mem_support _ _ _).mpr
        rw [zw]
        exact hl _ (sing p)
      simp [h] at wc
      omega
    have wrD : w∈Finset.Ico n (n+D.size) := by rwa [sameSize]
    rcases tproj.2.2.2.2.2 w wrD na wn nz with ⟨i,_,h⟩ | dorm
    · have b := (Finset.mem_filter.mp h).2.2
      rw [same w wn,wc] at b
      omega
    · have b := (Finset.mem_filter.mp dorm).2.2
      have cap := Finset.card_le_card (show support D w ∩ S d ⊆ support D w from Finset.inter_subset_left)
      rw [same w wn] at b
      rw [same w wn,wc] at cap
      omega
  have r := disjoint_outputs_refunded S C o y B hlin ho (fun i hi =>
    ⟨(dat i hi).1,by have b := (dat i hi).2.2; omega⟩)
  obtain ⟨E,lb,triples⟩ := regular_crossing_triples S C o t y hk hlin hg hu ho hl hy bad
  refine ⟨D,f,v,E,gD,fun x hx w => agree x (by omega) w,only,?_,triples⟩
  change B.card+3≤E.card
  omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

-- A one-fold projection at equality leaves only one possible singleton
-- gate. Each regular crossing needs that same point and a different
-- point of the witness set, so three witness points cannot pay the cut.
theorem three_tight_folded_projection {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (d : Fin m) (hk : y.card=3)
    (hlin : rowLinearity S) (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p∈y)) (n+t)=false)
    (hquota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
      d∈B ∧ (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+4) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length+(refunds S C y).card+m := by
  classical
  by_contra bad
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
  obtain ⟨hd,quota⟩ : d∈B ∧ (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+4 := hquota
  obtain ⟨D,f,v,E,gd,agree,singletons,lo,triples⟩ :=
    tight_projection_regular_crossings S C o t y d hk hlin hg hu ho hl hy bad hd quota
  have up := crossing_triples_singleton_cap S C D f o t v y E hlin hg hu ho gd agree singletons
    (fun i hi => by
      obtain ⟨meet,three,w,j,after,earlier,own,dis,high,loss,_⟩ := triples i hi
      exact ⟨meet,three,w,j,after,earlier,own,dis,high,loss⟩)
  have pos := Finset.card_pos.mpr ⟨d,hd⟩
  change B.card+3 ≤ E.card at lo
  omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem three_eight_profile {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hk : y.card=3) (hlin : rowLinearity S)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (profile : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
      B.card=3 ∧ (∀ i∈B, (S i).card=8) ∧
      ∀ i, i∉B → Disjoint (S i) y → (S i).card≤4) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  obtain ⟨bc,sizes,_⟩ : B.card=3 ∧ (∀ i∈B, (S i).card=8) ∧
      (∀ i, i∉B → Disjoint (S i) y → (S i).card≤4) := profile
  obtain ⟨d,hd⟩ := Finset.card_pos.mp (by omega : 0<B.card)
  apply three_tight_folded_projection S C o t y d hk hlin hg hu ho hl hy ⟨hd,?_⟩
  change (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+4
  rw [Finset.sum_congr rfl sizes,Finset.sum_const,smul_eq_mul,bc,sizes d hd]

end L_meta_997.Small

namespace L_meta_997.Small

lemma row_surplus_of_subsets {n m : ℕ} (S : Fin m → Finset (Fin n)) (B : Finset (Fin m))
    (r d : ℕ) (hr : d+1 ≤ r) (hb : r ≤ B.card) (hbig : ∀ i ∈ B, 5 ≤ (S i).card)
    (cap : ∀ I ⊆ B, I.card=r → (∑ i ∈ I, (S i).card) ≤ 5*r+d) :
    (∑ i ∈ B, (S i).card) ≤ B.card*5+d := by
  classical
  let E := B.filter (fun i => 6 ≤ (S i).card)
  have hEB : E ⊆ B := Finset.filter_subset _ _
  have he : E.card ≤ d := by
    by_contra! h
    obtain ⟨J,hJE,h5⟩ := Finset.exists_subset_card_eq (s:=E) (n:=d+1) (by omega)
    obtain ⟨I,hJI,hIB,hrI⟩ := Finset.exists_subsuperset_card_eq (hJE.trans hEB)
      (n:=r) (by omega) hb
    have hp := Finset.sum_le_sum (s:=I) (f:=fun i => 5+(if i ∈ J then 1 else 0))
      (g:=fun i => (S i).card) (fun i hi => by
        by_cases h : i ∈ J
        · simpa [h] using (Finset.mem_filter.mp (hJE h)).2
        · simpa [h] using hbig i (hIB hi))
    simp [Finset.sum_add_distrib,Finset.sum_boole,Finset.inter_eq_right.mpr hJI,
      Nat.mul_comm] at hp
    have up := cap I hIB hrI
    omega
  obtain ⟨I,hEI,hIB,hrI⟩ := Finset.exists_subsuperset_card_eq hEB (n:=r) (by omega) hb
  have outside (i) (hi : i ∈ B \ I) : (S i).card = 5 := by
    obtain ⟨hb, hn⟩ := Finset.mem_sdiff.mp hi
    have lo := hbig i hb
    have up : ¬6 ≤ (S i).card := fun h => hn (hEI (Finset.mem_filter.mpr ⟨hb,h⟩))
    omega
  have rest := Finset.sum_congr (s₁:=B \ I) rfl outside
  rw [Finset.sum_const,smul_eq_mul,Finset.card_sdiff_of_subset hIB,hrI] at rest
  have split := Finset.sum_sdiff hIB (f:=fun i => (S i).card)
  have up := cap I hIB hrI
  omega

lemma twenty_five_row_profiles {n m : ℕ} (S : Fin m → Finset (Fin n))
    (B : Finset (Fin m)) (V : Finset (Fin n))
    (hlin : L_meta_997.Light.rowLinearity S)
    (hsub : ∀ i ∈ B, S i ⊆ V) (hV : V.card ≤ 22)
    (hbig : ∀ i ∈ B, 5 ≤ (S i).card)
    (hstd : 5*B.card+5 ≤ ∑ i ∈ B, (S i).card)
    (hfold : ∀ i ∈ B, 4*B.card+(S i).card+3 < ∑ j ∈ B, (S j).card)
    (hcut : 4 ≤ B.card → 5*B.card+8 ≤ (∑ i ∈ B, (S i).card))
    (hcutLarge : 7 ≤ B.card → 5*B.card+9 ≤ (∑ i ∈ B, (S i).card)) :
    (B.card=3 ∧ (∑ i ∈ B, (S i).card)=24) ∨
    ((B.card=3 ∧ (∑ i ∈ B, (S i).card)=25 ∨
      B.card=4 ∧ (∑ i ∈ B, (S i).card)=28) ∧ B.biUnion S = V) := by
  classical
  have bSmall : B.card ≤ 8 := by
    by_contra! tooLarge
    have subMass (I : Finset (Fin m)) (hI : I ⊆ B) (hc : I.card=9) :
        (∑ i ∈ I, (S i).card) ≤ 5*9+6 := by
      have hp := pair_incidence S I V (fun i hi => hsub i (hI hi)) hlin
      rw [hc] at hp
      norm_num [Nat.choose] at hp ⊢
      omega
    have total := row_surplus_of_subsets S B 9 6 (by decide) tooLarge hbig subMass
    have lower := hcut (by omega)
    omega
  have nonempty : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hstd
    simp at hstd
  obtain ⟨d,hd,largest⟩ := B.exists_max_image (fun i => (S i).card) nonempty
  have fst := hfold d hd
  have mx := Finset.sum_le_sum (s:=B) largest
  simp only [Finset.sum_const,smul_eq_mul] at mx
  have all : B.biUnion S ⊆ V := by
    intro p hp
    obtain ⟨i,hi,hit⟩ := Finset.mem_biUnion.mp hp
    exact hsub i hi hit
  have ug := Finset.card_le_card all
  have un := line_union S hlin B
  have pair := pair_incidence S B V hsub hlin
  have pos := Finset.card_pos.mpr nonempty
  have profiles : (B.card=3 ∧ (∑ i ∈ B, (S i).card)=24) ∨
      ((B.card=3 ∧ (∑ i ∈ B, (S i).card)=25 ∨
        B.card=4 ∧ (∑ i ∈ B, (S i).card)=28) ∧ V.card ≤ (B.biUnion S).card) := by
    generalize heq : B.card = b at *
    interval_cases b <;> norm_num [Nat.choose] at * <;> omega
  exact profiles.imp_right fun ⟨h,cv⟩ => ⟨h,Finset.eq_of_subset_of_card_le all cv⟩

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

theorem twenty_five_residual : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 25 → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m) →
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
    y.card=3 ∧
    ((B.card=3 ∧ (∑ i ∈ B, (S i).card)=24) ∨
      ((B.card=3 ∧ (∑ i ∈ B, (S i).card)=25 ∨
        B.card=4 ∧ (∑ i ∈ B, (S i).card)=28) ∧ B.biUnion S = Finset.univ \ y)) := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy bad
  have hk : y.card=3 := by
    by_contra h
    exact bad (size_window_joint n m S C o t y (by omega) hlin hg hu ho hl hy)
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  let V := Finset.univ \ y
  have vc : V.card = n-3 := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y),hk]
  have uc : V.card ≤ 22 := by omega
  have sub (i) (hi : i ∈ B) : S i ⊆ V := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp (Finset.mem_filter.mp hi).2.1 hp⟩
  have big (i) (hi : i ∈ B) : 5 ≤ (S i).card := (Finset.mem_filter.mp hi).2.2.2
  have ordinary : 5*B.card+5 ≤ ∑ i ∈ B, (S i).card := by
    by_contra! h
    apply bad (three_window_bound n m S C o t y ⟨hk,?_⟩ hlin hg hu ho hl hy)
    unfold threeRowQuota
    rw [hk]
    change B.Nonempty → _
    exact fun ⟨d,hd⟩ => ⟨d,hd,Or.inr (by
      change (∑ i ∈ B, (S i).card) ≤ B.card*5+4
      omega)⟩
  have fold (d) (hd : d ∈ B) : 4*B.card+(S d).card+3 < ∑ i ∈ B, (S i).card := by
    by_contra! h
    apply bad (folded_projection S d C o t y (by omega) hlin hg hu ho hl hy (Finset.mem_filter.mp hd).2.2.1 ?_)
    rw [hk]
    change _ ≤ 4*B.card+(S d).card+3
    exact h
  have cut (b : 4 ≤ B.card) : 5*B.card+8 ≤ ∑ i ∈ B, (S i).card := by
    by_contra! h
    exact bad (tight_crossing_bound S C o t y hk hlin hg hu ho hl hy (Or.inl ⟨b,show (∑ i ∈ B, (S i).card) ≤ 5*B.card+7 by omega⟩))
  have cutLarge (b : 7 ≤ B.card) : 5*B.card+9 ≤ ∑ i ∈ B, (S i).card := by
    by_contra! h
    exact bad (tight_crossing_bound S C o t y hk hlin hg hu ho hl hy (Or.inr ⟨b,show (∑ i ∈ B, (S i).card) ≤ 5*B.card+8 by omega⟩))
  exact ⟨hk,twenty_five_row_profiles S B V hlin sub uc big ordinary fold cut cutLarge⟩

end L_meta_997.Small

namespace L_meta_997.Small

lemma three_eight_extra_shape {n m : ℕ} (S : Fin m → Finset (Fin n)) (B : Finset (Fin m))
    (V : Finset (Fin n)) (hV : V.card≤22) (bc : B.card=3) (mass : (∑ i ∈ B, (S i).card)=24)
    (lin : L_meta_997.Light.rowLinearity S)
    (sub : ∀ i∈B, S i ⊆ V) (top : ∀ i∈B, (S i).card≤8) :
    (∀ i∈B, (S i).card=8) ∧ (∀ i, i∉B → S i ⊆ V → (S i).card≤4) := by
  classical
  constructor
  · intro i hi
    have cap := Finset.sum_le_sum (s:=B.erase i) (g:=fun _ => 8)
      (fun j hj => top j (Finset.mem_of_mem_erase hj))
    rw [Finset.sum_const,smul_eq_mul,Finset.card_erase_of_mem hi,bc] at cap
    have split := Finset.sum_erase_add B (fun j => (S j).card) hi
    have := top i hi
    omega
  · intro i hi si
    let U := B.biUnion S
    have uV : U ⊆ V := by
      intro p hp
      obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
      exact sub j hj hpj
    have minU : 21 ≤ U.card := by
      have h := line_union S lin B
      rw [bc,mass] at h
      norm_num [Nat.choose] at h
      exact h
    have inc : (S i ∩ U) ⊆ B.biUnion (fun j => S i ∩ S j) := by
      intro p hp
      obtain ⟨j,hj,hp'⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hp).2
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hp).1,hp'⟩⟩
    have q := (Finset.card_le_card inc).trans (Finset.card_biUnion_le_card_mul B _ 1
      (fun j hj => lin i j (fun e => hi (e ▸ hj))))
    rw [bc,Nat.mul_one] at q
    have ssub : S i \ U ⊆ V \ U := 
      fun p hp => Finset.mem_sdiff.mpr ⟨si (Finset.mem_sdiff.mp hp).1,(Finset.mem_sdiff.mp hp).2⟩
    have s := Finset.card_le_card ssub
    rw [Finset.card_sdiff_of_subset uV] at s
    have part := Finset.card_sdiff_add_card_inter (S i) U
    omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

theorem twenty_five_mass_residual {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hn : n ≤ 25)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m)) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
    n=25 ∧ y.card=3 ∧ B.biUnion S = Finset.univ \ y ∧
    ((B.card=3 ∧ (∑ i ∈ B, (S i).card)=25) ∨
      (B.card=4 ∧ (∑ i ∈ B, (S i).card)=28)) := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  obtain ⟨hk,hsmall|⟨cases,cover⟩⟩ := twenty_five_residual n m S C o t y hn hlin hg hu ho hl hy bad
  · exfalso
    obtain ⟨bc,mass⟩ : B.card=3 ∧ (∑ i ∈ B, (S i).card)=24 := hsmall
    let V : Finset (Fin n) := Finset.univ \ y
    have count : V.card = n-3 := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y),hk]
    have vc : V.card ≤ 22 := by omega
    have ins (i) (di : Disjoint (S i) y) : S i ⊆ V := fun p hp =>
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp di hp⟩
    have top (i) (hi : i ∈ B) : (S i).card ≤ 8 := by
      by_contra! large
      apply bad (folded_projection S i C o t y (by omega) hlin hg hu ho hl hy
        (Finset.mem_filter.mp hi).2.2.1 ?_)
      rw [hk]
      change (∑ j ∈ B, (S j).card) ≤ 4*B.card+(S i).card+3
      omega
    obtain ⟨all8,rest⟩ := three_eight_extra_shape S B V vc bc mass hlin
      (fun i hi => ins i (Finset.mem_filter.mp hi).2.1) top
    exact bad (three_eight_profile S C o t y hk hlin hg hu ho hl hy
      ⟨bc,all8,fun i hi dis => rest i hi (ins i dis)⟩)
  · have outside : (Finset.univ \ y).card = n-3 := by
      simp [Finset.card_sdiff_of_subset (Finset.subset_univ y),hk]
    have lo := line_union S hlin B
    rw [cover,outside] at lo
    have n25 : n=25 := by
      rcases cases with ⟨bc,mass⟩|⟨bc,mass⟩ <;>
        rw [bc,mass] at lo <;> norm_num [Nat.choose] at lo <;> omega
    exact ⟨n25,hk,cover,cases⟩

end L_meta_997.Small
namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds L_meta_997_aux

theorem direct_reader_exclusions {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (a : Fin C.gates.length) (ta : t<a.val) (rd : n+t ∈ (C.gates.get a).inputs)
    (hk : 2 ≤ y.card) (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun q => decide (q∈y)) (n+t) = false)
    (proper : ∀ i, S i≠Finset.univ) :
    (∀ i, (S i).Nonempty → o i≠n+a.val) ∧
    (andAt C n (n+a.val) ∨ ∀ i, n+a.val ∉ assigned C (S i)) := by
  classical
  let v := n+a.val
  let z := n+t
  let g := C.gates.get a
  have zv : z<v := by dsimp [z,v]; omega
  have vl : n≤v := by dsimp [v]; omega
  have vu : v<n+C.size := Nat.add_lt_add_left a.isLt n
  have ev (x : Fin n → Bool) : value C x v = g.op.eval (g.inputs.map
      (fun u => if u<v then value C x u else false)) := by
    simpa only [v,g,Nat.add_sub_cancel_left,List.get_eq_getElem] using gate_value C x v vl vu
  have small (p : Fin n) :
      (Finset.univ.filter (fun q : Fin n => decide (q=p) = true)).card < y.card := by
    have eq : (Finset.univ.filter (fun q : Fin n => decide (q=p) = true)) = {p} := by ext q; simp
    rw [eq,Finset.card_singleton]
    omega
  have zero : (Finset.univ.filter (fun _ : Fin n => false = true)).card < y.card := by
    simpa using (show 0 < y.card by omega)
  have h0 : value C (fun _ : Fin n => false) z=true := hl (fun _ => false) zero
  have cerr := (terminal_switch_closed C y t hg hu h0 hy).2
  have highOff (p : Fin n) : value C (fun q => decide (q∈y ∨ q=p)) z=false := by
    apply Bool.eq_false_iff.mpr
    intro on
    have h := (Heavy.mem_supp C y z p).mpr on
    exact Finset.notMem_empty p (cerr ▸ h)
  have outputs (i) (x : Fin n → Bool) : value C x (o i)=decide (∃ p ∈ S i, x p=true) := ho i x
  have eop := (hg g (List.get_mem _ _)).1
  rcases eop with aop | oop | nop
  · refine ⟨?_,Or.inl ?_⟩
    · intro i ⟨p,pm⟩ reader
      let x : Fin n → Bool := fun q => decide (q∈y ∨ q=p)
      have on : value C x v=true := by
        change o i=v at reader
        rw [←reader,outputs]
        exact decide_eq_true ⟨p,pm,by simp [x]⟩
      rw [ev x,aop,GateOp.eval] at on
      have all := List.all_eq_true.mp on _ (List.mem_map.mpr ⟨z,rd,rfl⟩)
      have forced : value C x z=true := by simpa only [id_eq,ite_eq_left zv] using all
      exact Bool.noConfusion ((highOff p).symm.trans forced)
    · unfold andAt
      rw [Nat.add_sub_cancel_left,List.getElem?_eq_getElem a.isLt]
      simpa only [Option.map_some,List.get_eq_getElem,g] using congrArg some aop
  · have turnOn (x : Fin n → Bool) (on : value C x z = true) : value C x v=true := by
      rw [ev x,oop,GateOp.eval,List.any_eq_true]
      exact ⟨true,List.mem_map.mpr ⟨z,rd,by simpa only [ite_eq_left zv] using on⟩,rfl⟩
    refine ⟨?_,Or.inr ?_⟩
    · intro i _ e
      have on := turnOn _ h0
      change o i=v at e
      rw [←e,outputs] at on
      simp at on
    · intro i hi
      have sub := (Finset.mem_filter.mp hi).2.1
      apply proper i (Finset.eq_univ_of_forall (fun p => sub ?_))
      exact (mem_support C v p).mpr (turnOn _ (hl _ (small p)))
  · have eq := hu a nop
    omega

end L_meta_997.Light




namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem three_mass25_full_cover_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (d : Fin m) (hk : y.card=3)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t)=false)
    (profile : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
      B.card=3 ∧ (∑ i ∈ B, (S i).card)=25 ∧ d∈B ∧ (S d).card=9 ∧
        B.biUnion S = Finset.univ \ y) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  obtain ⟨bc,mass,hd,nine,_⟩ : B.card=3 ∧ (∑ i ∈ B, (S i).card)=25 ∧
      d∈B ∧ (S d).card=9 ∧ B.biUnion S=Finset.univ \ y := profile
  apply three_tight_folded_projection S C o t y d hk hlin hg hu ho hl hy ⟨hd,?_⟩
  change (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+4
  rw [mass,bc,nine]

end L_meta_997.Small

namespace L_meta_997.Small

lemma three_mass_twenty_five_sizes {n m : ℕ} (S : Fin m → Finset (Fin n)) (B : Finset (Fin m))
    (bc : B.card=3) (mass : (∑ i ∈ B, (S i).card)=25)
    (top : ∀ i∈B, (S i).card≤9) :
    (∃ d∈B, (S d).card=9) ∧ (∀ i∈B, 7≤(S i).card) := by
  classical
  constructor
  · by_contra! h
    have cap := Finset.sum_le_sum (s:=B) (f:=fun i => (S i).card) (g:=fun _=>8) (fun i hi => by
      have := top i hi
      have := h i hi
      omega)
    rw [Finset.sum_const,smul_eq_mul,bc,mass] at cap
    omega
  · intro i hi
    have cap := Finset.sum_le_sum (s:=B.erase i) (g:=fun _=>9)
      (fun j hj => top j (Finset.mem_of_mem_erase hj))
    rw [Finset.sum_const,smul_eq_mul,Finset.card_erase_of_mem hi,bc] at cap
    have split := Finset.sum_erase_add B (fun j => (S j).card) hi
    omega

end L_meta_997.Small

namespace L_meta_997.Small

theorem card_inter_biUnion_linear {α β : Type*} [DecidableEq β]
    (B : Finset α) (S : α → Finset β) (T : Finset β)
    (linear : ∀ i ∈ B, (T ∩ S i).card ≤ 1) :
    (T ∩ B.biUnion S).card ≤ B.card := by
  classical
  have eq : T ∩ B.biUnion S = B.biUnion (fun i => T ∩ S i) := by
    ext p
    simp only [Finset.mem_inter,Finset.mem_biUnion]
    exact ⟨fun ⟨pT,j,jB,pS⟩ => ⟨j,jB,pT,pS⟩,fun ⟨j,jB,pT,pS⟩ => ⟨pT,j,jB,pS⟩⟩
  rw [eq]
  simpa only [Nat.mul_one] using Finset.card_biUnion_le_card_mul B (fun i => T ∩ S i) 1 linear

theorem outside_coverage_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (y : Finset (Fin n)) (B : Finset (Fin m))
    (linear : L_meta_997.Light.rowLinearity S)
    {i : Fin m} (out : i ∉ B) :
    (S i \ y).card ≤ B.card + ((Finset.univ \ y) \ B.biUnion S).card := by
  classical
  have hit := card_inter_biUnion_linear B S (S i \ y) (fun j hj =>
    (Finset.card_le_card (show (S i \ y) ∩ S j ⊆ S i ∩ S j from by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_inter.mp hp).2⟩)).trans (linear i j (fun e => out (e.symm ▸ hj))))
  have miss : (S i \ y) \ B.biUnion S ⊆ (Finset.univ \ y) \ B.biUnion S := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hp).1).2⟩,(Finset.mem_sdiff.mp hp).2⟩
  have parts := Finset.card_sdiff_add_card_inter (S i \ y) (B.biUnion S)
  have mc := Finset.card_le_card miss
  omega

end L_meta_997.Small

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem projection_gate_count_one_slack {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (z : ℕ) (A : Finset ℕ) (hD : 2 ≤ (S d).card)
    (hpair : rowLinearity S)
    (hzrange : z ∈ Finset.Ico n (n+C.size)) (htz : value C (fun _ : Fin n => false) z=true)
    (hzs : ∀ p : Fin n, p ∈ support C z)
    (hAi : A ⊆ Finset.Ico n (n+C.size)) (hAz : z ∉ A) (hAs : ∀ w ∈ A, support (n:=n) C w=∅)
    (q : ℕ) (hdweight : q ≤ (dormant C (S d)).card+1)
    (f : Fin m → ℕ)
    (hweight : ∀ i, i ≠ d → f i ≤ (assigned C (S i)).card+1)
    (near : C.gates.length + m ≤ q + (∑ i ∈ Finset.univ.erase d, f i) + A.card+2) :
    ∃ Q : Finset ℕ, ∃ J : Finset (Fin m), Q.card+J.card≤q ∧ J.card≤1 ∧
      (∀ i, i≠d → (assigned C (S i)).card+1=f i+(if i∈J then 1 else 0)) ∧
      (∀ w ∈ Finset.Ico n (n+C.size), w ∉ A → w≠z →
        (∃ i, i≠d ∧ w ∈ assigned C (S i)) ∨ w∈Q) := by
  classical
  by_cases e : ∃ i, i≠d ∧ f i < (assigned C (S i)).card+1
  · obtain ⟨i,ne,lt⟩ := e
    let f' := fun j => f j + (if j=i then 1 else 0)
    have greater (j) (nd : j≠d) : f' j ≤ (assigned C (S j)).card+1 := by
      by_cases eq : j=i
      · subst j
        simp [f']
        omega
      · simpa [f',eq] using hweight j nd
    have sum : (∑ j ∈ Finset.univ.erase d, f' j) = (∑ j ∈ Finset.univ.erase d, f j)+1 := by
      have h : i∈Finset.univ.erase d := Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩
      simp only [f',Finset.sum_add_distrib,Finset.sum_ite_eq',h,ite_true]
    have tight : C.gates.length + m ≤ q + (∑ j ∈ Finset.univ.erase d, f' j) + A.card+1 := by
      rw [sum]
      omega
    obtain ⟨count,weights,cover⟩ := projection_gate_count_tight S d C z A hD hpair hzrange htz
      hzs hAi hAz hAs q hdweight f' greater tight
    refine ⟨dormant C (S d),{i},by rw [Finset.card_singleton,count],by simp,?_,cover⟩
    intro j neq
    simpa [f'] using weights j neq
  push Not at e
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
  let W := insert z (U ∪ G)
  have disA : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro w wa ww
    rcases Finset.mem_insert.mp ww with hz | h
    · exact hAz (hz ▸ wa)
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i,_,hw⟩ := Finset.mem_biUnion.mp h
        have hc := (Finset.mem_filter.mp hw).2.2
        rw [hAs w wa] at hc
        simp at hc
      · have hc := (Finset.mem_filter.mp h).2.2
        rw [hAs w wa] at hc
        simp at hc
  have sub : A ∪ W ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with ha | hw
    · exact hAi ha
    · rcases Finset.mem_insert.mp hw with h | hw
      · exact h ▸ hzrange
      · rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
          exact (Finset.mem_filter.mp hi).1
        · exact (Finset.mem_filter.mp hw).1
  have Wcard : (A ∪ W).card = A.card + (U.card + G.card + 1) := by
    rw [Finset.card_union_of_disjoint disA]
    simp only [W,Finset.card_insert_of_notMem hnotin,Finset.card_union_of_disjoint dis]
  have hgate := Finset.card_le_card sub
  rw [Wcard] at hgate
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left,Circuit.size] at hgate
  have hcard := Finset.card_erase_add_one (Finset.mem_univ d)
  change I.card + 1 = _ at hcard
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  have hgeneral := sum_row_weights S I C f hpair (fun i hi => hweight i (Finset.mem_erase.mp hi).1)
  change (∑ i ∈ I, f i) ≤ U.card + I.card at hgeneral
  let R := (Finset.Ico n (n+C.size)) \ (A ∪ W)
  have partition := Finset.card_sdiff_add_card_eq_card sub
  change R.card+(A∪W).card=(Finset.Ico n (n+C.size)).card at partition
  rw [Wcard,Nat.card_Ico,Nat.add_sub_cancel_left] at partition
  change R.card+(A.card+(U.card+G.card+1))=C.gates.length at partition
  have qBound : (G∪R).card ≤ q := by
    have c := Finset.card_union_le G R
    change C.gates.length+m ≤ q+(∑ i ∈ I, f i)+A.card+2 at near
    omega
  refine ⟨G∪R,∅,by simpa using qBound,by simp,?_,?_⟩
  · intro i ne
    have lo := hweight i ne
    have hi := e i ne
    simp only [Finset.notMem_empty,ite_false,Nat.add_zero]
    omega
  · intro w wr wa wz
    by_cases covered : w∈A∪W
    · have hw : w∈U∪G := (Finset.mem_insert.mp ((Finset.mem_union.mp covered).resolve_left wa)).resolve_left wz
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i,hi,wi⟩ := Finset.mem_biUnion.mp hw
        exact Or.inl ⟨i,(Finset.mem_erase.mp hi).1,wi⟩
      · exact Or.inr (Finset.mem_union.mpr (Or.inl hw))
    · exact Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨wr,covered⟩)))

end L_meta_997.Light

namespace L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem folded_model_one_slack {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hs : (assigned C (S d)).card+1 < (S d).card)
    (large : ∀ i, Disjoint (S i) y → y.card+2≤(S i).card →
       (assigned C (S i)).card+1<(S i).card)
    (quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
       (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+2)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m))
    (D : Circuit) (f : ℕ → ℕ) (v : ℕ) (goodD : good D) (sz : D.size=C.size)
    (after : n+t<v) (vr : v<n+C.size) (dead : ∀ x : Fin n → Bool, value D x v=false)
    (unchanged : ∀ w, w≠v → f w=w)
    (agree : ∀ (x : Fin n → Bool), (Finset.univ.filter (fun p => x p=true)).card<y.card →
      ∀ w, value D x (f w)=value C x w)
    (A : Finset ℕ) (ac : y.card ≤ A.card+1) (ar : A ⊆ Finset.Ico n (n+t))
    (ae : ∀ w ∈ A, support (n:=n) C w=∅) :
    ∃ Q : Finset ℕ, ∃ J : Finset (Fin m),
      Q.card+J.card≤(S d).card+y.card-1 ∧ J.card≤1 ∧
      (∀ i, Disjoint (S i) y → 2≤(S i).card → y.card<(S i).card ∨ i∈J) ∧
      (∀ i, i≠d → (assigned D (S i)).card+1 ≤ min y.card (S i).card + (if i∈J then 1 else 0)) ∧
      (∀ w ∈ Finset.Ico n (n+D.size), w ∉ A → w≠v → w≠n+t →
        (∃ i, i≠d ∧ w ∈ assigned D (S i)) ∨ w ∈ Q) := by
  classical
  let k := y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ k+2 ≤ (S i).card)
  let R := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  have hk' : 2 ≤ k := hk
  have hbig : k < (S d).card := by have := card_light (S d) C (o d) t hg hu (out d) hl; change min k (S d).card ≤ _ at this; omega
  have zero : (Finset.univ.filter (fun _ : Fin n => false = true)).card < y.card := by simpa using (show 0<y.card by omega)
  have sing (p : Fin n) : (Finset.univ.filter (fun q : Fin n => decide (q=p) = true)).card < y.card := by
    have e : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [e,Finset.card_singleton]; omega
  have same (w : ℕ) (ne : w≠v) : support (n:=n) D w=support C w := by
    ext p; rw [mem_support,mem_support]
    rw [← unchanged w ne,agree _ (sing p) w,unchanged w ne]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,dead]
  have contain (i) : assigned D (S i) ⊆ assigned C (S i) := by
    intro w hw
    obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
    have ne : w≠v := by rintro rfl; rw [empty,Finset.card_empty] at hc; omega
    rw [same w ne] at hsub hc
    exact Finset.mem_filter.mpr ⟨sz ▸ hr,hsub,hc⟩
  have output (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) :
      value D x (f (o i))=decide (∃ p ∈ S i, x p=true) := (agree x hx _).trans (out i x)
  have singleton (i) (p : Fin n) : value D (fun q => decide (q=p)) (f (o i))=true ↔ p ∈ S i := by
    rw [output i _ (sing p)]; simp
  have sparse (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k)
      (off : ∀ p ∈ S i, x p=false) : value D x (f (o i))=false := by
    rw [output i x hx]; exact decide_eq_false (fun ⟨p,hp,on⟩ => Bool.noConfusion ((off p hp).symm.trans on))
  have mincount (i) : min k (S i).card ≤ (assigned D (S i)).card+1 := by
    by_cases e : (S i).card=0
    · simp [e]
    have cnt := card_assigned (k:=k-1) (c:=min k (S i).card-1) D (S i) (f (o i)) goodD (singleton i)
      (fun x hx => sparse i x (by omega)) (by omega) (by omega)
    omega
  have extra := (sharp_private_or_extra D (S d) (f (o d)) goodD
    (by rw [output d _ zero]; simp) (by ext p; exact (mem_support _ _ _).trans (singleton d p)) (sparse d)).resolve_left
    (by have h := Finset.card_le_card (contain d); omega)
  let weight (i : Fin m) := min k (S i).card
  have fund (i) : weight i ≤ (assigned D (S i)).card+1 := mincount i
  let z := n+t
  have zlt : z<v := after
  have za : z ∉ A := fun ha => Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar ha)).2
  have va : v ∉ A := fun ha => Nat.lt_asymm after (Finset.mem_Ico.mp (ar ha)).2
  have zOn (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) : value D x z=true := by
    have eq := agree x hx z
    rw [unchanged z (ne_of_lt zlt)] at eq
    exact eq.trans (hl x hx)
  have computed := projection_gate_count S d D z (insert v A) (by omega) hpair
    (Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩) (zOn _ zero)
    (fun p => (mem_support _ _ _).mpr (zOn _ (sing p)))
    (Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by rw [sz]; have h := (Finset.mem_Ico.mp (ar hw)).2; omega⟩))
    (by simpa [ne_of_lt zlt] using za)
    (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact empty
      · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw))
    ((S d).card+k-1) (by omega) weight (fun i _ => fund i)
  have calcD := computed
  rw [Finset.card_insert_of_notMem va] at calcD
  have hlen : D.gates.length=C.gates.length := sz
  rw [hlen] at calcD
  have wd : weight d=k := by simp [weight,Nat.not_le.mpr hs,min_eq_left (by omega : k≤(S d).card)]
  have cut := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) weight (Finset.mem_univ d)
  rw [wd] at cut
  let L := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2≤(S i).card ∧ (S i).card≤k)
  have per (i) : (if Disjoint (S i) y then (S i).card else min k (S i).card) +
      (if i∈L then 1 else 0) ≤
      weight i + (if i∈R then 1 else 0) + (if i∈B then (S i).card-(k+1) else 0) := by
    by_cases hd : Disjoint (S i) y
    swap
    · simp [weight,B,R,L,hd]
    by_cases hs : (S i).card≤k
    · have nb : ¬ k+2 ≤ (S i).card := by omega
      simp [weight,B,R,L,hd,hs,nb,min_eq_right hs]
    · have hl : k<(S i).card := by omega
      by_cases big : k+2≤(S i).card
      · have under := large i hd big
        simp [weight,B,R,L,hd,hs,big,under,min_eq_left hl.le,
          show 2≤(S i).card by omega]
        omega
      · simp [weight,B,R,L,hd,hs,big,min_eq_left hl.le,
          show 2≤(S i).card by omega]
        omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simp only [Finset.sum_add_distrib,Fintype.sum_ite_mem,Finset.sum_const,smul_eq_mul,mul_one] at total
  have split := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl
    (g:=fun i => (k+1)+((S i).card-(k+1))) (fun i hi => by
      have h := (Finset.mem_filter.mp hi).2.2.2
      omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_comm B.card (k+1)] at split
  change (∑ i ∈ B, (S i).card) ≤ (k+1)*B.card+(S d).card+k+2 at quota
  have ref := disjoint_outputs_refunded S C o y R hpair out (fun i hi => (Finset.mem_filter.mp hi).2)
  change ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤ _) at bad
  change k ≤ A.card+1 at ac
  let coldSet := insert v A
  have coldSize : coldSet.card=A.card+1 := Finset.card_insert_of_notMem va
  have cycle : D.gates.length+m+L.card ≤ (S d).card+k-1 +
      (∑ i ∈ Finset.univ.erase d, weight i)+coldSet.card+2 := by
    rw [hlen,coldSize]
    omega
  have cv : coldSet ⊆ Finset.Ico n (n+D.size) :=
    Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by
        rw [sz]
        have h := (Finset.mem_Ico.mp (ar hw)).2
        omega⟩)
  have zrange : z∈Finset.Ico n (n+D.size) :=
    Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩
  have znot : z∉coldSet := by simpa [coldSet,ne_of_lt zlt] using za
  have sign (w) (hw : w∈coldSet) : support (n:=n) D w=∅ := by
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact empty
    · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw)
  have lsmall : L.card≤1 := by rw [coldSize,hlen] at cycle; omega
  have zsupport (p : Fin n) : p∈support D z := (mem_support _ _ _).mpr (zOn _ (sing p))
  by_cases lpos : L.Nonempty
  · have lsize : L.card=1 := by have := Finset.card_pos.mpr lpos; omega
    have tight : D.gates.length+m ≤ (S d).card+k-1 +
        (∑ i ∈ Finset.univ.erase d, weight i)+coldSet.card+1 := by omega
    obtain ⟨count,weights,role⟩ := projection_gate_count_tight S d D z coldSet (by omega)
      hpair zrange (zOn _ zero) zsupport cv znot sign ((S d).card+k-1) (by omega)
        weight (fun i _ => fund i) tight
    refine ⟨dormant D (S d),L,by omega,lsmall,?_,?_,?_⟩
    · intro i dis big
      by_cases small : (S i).card≤k
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis,big,small⟩)
      · exact Or.inl (by omega)
    · intro i ne
      rw [weights i ne]
      simp only [weight]
      omega
    · intro w wr wa wv wz
      exact role w wr (by simp [coldSet,wa,wv]) wz
  · have lempty := Finset.not_nonempty_iff_eq_empty.mp lpos
    obtain ⟨Q,J,num,jc,weights,role⟩ := projection_gate_count_one_slack S d D z coldSet (by omega)
      hpair zrange (zOn _ zero) zsupport cv znot sign ((S d).card+k-1) (by omega)
        weight (fun i _ => fund i) (by omega)
    refine ⟨Q,J,num,jc,?_,fun i ne => (weights i ne).le,?_⟩
    · intro i dis big
      left
      by_contra! smaller
      have ine : i∈L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis,big,smaller⟩
      simpa [lempty] using ine
    · intro w wr wa wv wz
      exact role w wr (by simp [coldSet,wa,wv]) wz

end L_meta_997.Light

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem crossing_cap_under_eight_slack {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : y.card = 3)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (ho : rowOutputs C S o)
    (hl : lightOnSparse (n:=n) C t y.card)
    (hy : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (E : Finset (Fin m))
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m))
    (hgap : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
      (∑ i ∈ B, (S i).card) ≤ 5*B.card+8)
    (triples : ∀ i ∈ E, ¬ Disjoint (S i) y ∧ (S i).card=3 ∧ ∃ w j,
      n+t<w ∧ w<o i ∧ assigned C (S i)={w,o i} ∧ Disjoint y (S j) ∧
      w ∈ highOrGates C y (S j) ∧ (support C w \ S j).Nonempty ∧
      (Heavy.supp C y w \ S i).Nonempty) : E.card≤12 := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  obtain ⟨A,F,_,reserve,_,_,hA,roles⟩ :=
    combined_gate_roles S C o t y (by omega) hlin hg hu ho hl hy bad
  let χ : Fin n → Bool := fun p => decide (p ∈ y)
  let H := F.filter (fun w => value C χ w = true)
  let G := F.filter (fun w => ¬value C χ w = true)
  have splitF : H.card + G.card = F.card := Finset.card_filter_add_card_filter_not _
  have hz (p : Fin n) : p ∈ support C (n+t) := by
    apply (mem_support C (n+t) p).mpr
    apply hl
    have eq : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext q; simp
    rw [eq,Finset.card_singleton,hk]
    decide
  have packed := crossing_exception_packing S E y H G (support C)
    (fun i hi => (triples i hi).2.1) hlin (by
    intro i hi
    obtain ⟨meet,three,w,j,after,before,assignedEq,_,high,lowOutside,_⟩ := triples i hi
    obtain ⟨u,p,r,huF,hpr,hsu,huc,hsw⟩ :=
      crossing_parents_general S C (o i) t w y i j A F three (fun a ha => (hA a ha).2)
        roles hg hu hz after before assignedEq high lowOutside
    have hw : w ∈ assigned C (S i) := by simp [assignedEq]
    have hp : p ∈ S i := (Finset.mem_filter.mp hw).2.1 (hsw.symm ▸ Finset.mem_insert_self _ _)
    have cold := (Finset.mem_filter.mp (Finset.mem_filter.mp high).1).2.2.2
    refine ⟨u,Finset.mem_filter.mpr ⟨huF,by simp [χ,huc]⟩,p,hsu,hp,?_⟩
    rcases crossing_output_roles C S i y t w (o i) A F p r hg hu hlin (ho i) meet three ⟨after,before⟩
      assignedEq hsw hpr cold hy hz (fun a ha => (hA a ha).1) roles with andRole | orRole
    · obtain ⟨a,ha,b,hb,ne,hota,hotb,eq⟩ := andRole
      exact Or.inl ⟨a,Finset.mem_filter.mpr ⟨ha,hota⟩,b,Finset.mem_filter.mpr ⟨hb,hotb⟩,ne,eq⟩
    · obtain ⟨s,hs,hne,hs'⟩ := orRole
      exact Or.inr ⟨s,hs,hne,hs'.imp_right (fun ⟨v,hv,sv,hot⟩ =>
        ⟨v,Finset.mem_filter.mpr ⟨hv,hot⟩,sv⟩)⟩)
  rw [hk] at packed reserve
  let paid := fun i => (assigned C (S i)).card+1 < (S i).card
  have underEq : underDisjoint C S y = Finset.univ.filter (fun i => Disjoint (S i) y ∧ paid i) := by
    ext i
    simp [paid,underDisjoint,underpaid,and_comm]
  rw [underEq, Finset.sum_filter, excess_identity S y paid 3] at reserve
  change _ ≤ ∑ i ∈ B, ((S i).card-4) at reserve
  have mass := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl
    (g:=fun i => 4+((S i).card-4)) (fun i hi => by have h := (Finset.mem_filter.mp hi).2.2.2; omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at mass
  have ref := disjoint_outputs_refunded S C o y B hlin ho (fun i hi =>
    ⟨(Finset.mem_filter.mp hi).2.1,by have h := (Finset.mem_filter.mp hi).2.2.2; omega⟩)
  change (∑ i ∈ B, (S i).card) ≤ 5*B.card+8 at hgap
  have cap : H.card+G.card≤4 := by omega
  have numeric (h c : ℕ) (hc : h+c≤4) : h.choose 2 + c*(3+h) ≤12 := by
    have hu : h≤4 := by omega
    have cv : c≤4 := by omega
    interval_cases h <;> interval_cases c <;> norm_num [Nat.choose] at * <;> omega
  exact packed.trans (numeric H.card G.card cap)

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

open Classical in
theorem four_rows_top_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (d : Fin m) (hk : y.card=3)
    (hlin : rowLinearity S)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t) (ho : computesRows C S o)
    (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p∈y)) (n+t)=false)
    (profile : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
      B.card=4 ∧ (∑ i ∈ B, (S i).card)=28 ∧
      B.biUnion S=Finset.univ \ y ∧ d∈B ∧ ((S d).card=7 ∨ (S d).card=8)) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length+(refunds S C y).card+m := by
  classical
  by_contra bad
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  obtain ⟨bc,mass,cover,hd,dsz⟩ : B.card=4 ∧ (∑ i ∈ B, (S i).card)=28 ∧
      B.biUnion S=Finset.univ \ y ∧ d∈B ∧ ((S d).card=7 ∨ (S d).card=8) := profile
  have exterior (i) (hi : i ∉ B) (dis : Disjoint (S i) y) : (S i).card≤4 := by
    have cs := outside_coverage_bound S y B hlin hi
    rw [Finset.sdiff_eq_self_of_disjoint dis,cover,Finset.sdiff_self,Finset.card_empty,bc] at cs
    omega
  have large (i) (di : Disjoint (S i) y) (big : y.card+2≤(S i).card) :
      (assigned C (S i)).card+1 < (S i).card := by
    have hi : i ∈ B := by
      by_contra hn
      have w := exterior i hn di
      omega
    exact (Finset.mem_filter.mp hi).2.2.1
  have short := (Finset.mem_filter.mp hd).2.2.1
  obtain ⟨a,ta,rd⟩ := switch_has_reader C (S d) (o d) t (by omega : 2≤y.card)
    hg hu (ho d) hl short
  have av : n+t<n+a.val := by omega
  have ar : n+a.val<n+C.size := Nat.add_lt_add_left a.isLt n
  have proper (i) : S i ≠ Finset.univ := by
    obtain ⟨j,hj,nj⟩ := Finset.exists_mem_notMem_of_card_lt_card (s:={i}) (t:=B)
      (by simp [bc])
    have neq : i≠j := by simpa [eq_comm] using nj
    have h := hlin i j neq
    intro eq
    rw [eq,Finset.univ_inter] at h
    have b := (Finset.mem_filter.mp hj).2.2.2
    omega
  obtain ⟨readerNotOut,readerRole⟩ := direct_reader_exclusions S C o t y a ta rd
    (by omega) hg hu ho hl hy proper
  obtain ⟨D,f,goodD,dlen,dead,unchanged,agree,opsD,_⟩ := fold_one_reader_stable C t a ta rd hg hu hl
  obtain ⟨A,ac,aRange,aRoles⟩ := guard_hot_gates C t y (by omega : 0<y.card) hg hu hl hy
  have combined : ∃ Q : Finset ℕ, ∃ J : Finset (Fin m),
      Q.card+J.card≤9 ∧ J.card≤1 ∧
      (∀ i, Disjoint (S i) y → 2≤(S i).card → y.card<(S i).card ∨ i∈J) ∧
      (∀ i, i≠d → (assigned D (S i)).card+1 ≤ min y.card (S i).card + (if i∈J then 1 else 0)) ∧
      (∀ w ∈ Finset.Ico n (n+D.size), w ∉ A → w≠n+a.val → w≠n+t →
        (∃ i, i≠d ∧ w ∈ assigned D (S i)) ∨ w ∈ Q) := by
    rcases dsz with seven | eight
    · have quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
          (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
        (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+2 := by
        rw [hk]
        change (∑ i∈B,(S i).card) ≤ (3+1)*B.card+(S d).card+3+2
        rw [mass,bc,seven]
      simpa only [seven,hk] using
        (folded_model_one_slack S d C o t y (by omega) hlin hg hu ho hl short large quota bad
          D f (n+a.val) goodD dlen av ar dead unchanged agree A ac aRange
            (fun w hw => (aRoles w hw).1))
    · have quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
          (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
        (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+1 := by
        rw [hk]
        change (∑ i∈B,(S i).card) ≤ (3+1)*B.card+(S d).card+3+1
        rw [mass,bc,eight]
      have tproj := folded_model_tight S d C o t y (by omega) hlin hg hu ho hl short quota bad
        D f (n+a.val) goodD dlen av ar dead unchanged agree A ac aRange
          (fun w hw => (aRoles w hw).1)
      have nQ := tproj.2.2.2.1
      rw [eight,hk] at nQ
      refine ⟨dormant D (S d),∅,by simp; omega,by simp,?_,?_,tproj.2.2.2.2.2⟩
      · exact fun i di big => Or.inl (tproj.2.1 i di big)
      · intro i ne
        have eq := tproj.2.2.2.2.1 i ne
        split at eq
        · rename_i paid
          have short4 : (S i).card≤4 := by
            by_contra! h
            exact Nat.not_lt_of_ge paid.2.2 (large i paid.1 (by omega))
          have h := paid.2.1
          simp [hk,min_eq_left (by omega : 3≤(S i).card)]
          omega
        · simpa using eq.le
  obtain ⟨Q,J,ledger,jOne,long,weights,classify⟩ := combined
  have sing (p : Fin n) :
      (Finset.univ.filter (fun q : Fin n => decide (q=p)=true)).card<y.card := by
    have e : Finset.univ.filter (fun q : Fin n => decide (q=p)=true)={p} := by ext; simp
    rw [e,Finset.card_singleton,hk]
    decide
  have modelOut (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<y.card) :
      value D x (f (o i))=decide (∃ p ∈ S i, x p=true) := (agree x hx _).trans (ho i x)
  have modelSup (i) : support D (f (o i))=S i := by
    ext p
    rw [mem_support,modelOut i _ (sing p)]
    simp
  have same (w) (nw : w≠n+a.val) : support (n:=n) D w=support C w := by
    ext p
    rw [mem_support,mem_support,←unchanged w nw,agree _ (sing p) w,unchanged w nw]
  have empty : support (n:=n) D (n+a.val)=∅ := by ext p; simp [mem_support,dead]
  let H := B.biUnion (fun j => highOrGates C y (S j))
  let K := J.erase d
  let P (i : Fin m) := (assigned D (S i)).filter (fun w => w∈H)
  let U := Q ∪ K.biUnion P
  have hOr (w : ℕ) (hw : w∈H) : ¬andAt C n w := by
    obtain ⟨j,hj,wj⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp wj).2
  have cout (i) (x : Fin n → Bool) : value C x (o i)=decide (∃ p ∈ S i, x p=true) := ho i x
  have outputSup (i) : support C (o i)=S i := by
    ext p
    rw [mem_support,cout]
    simp
  have outputHeavy (i) (di : Disjoint (S i) y) : Heavy.supp C y (o i)=S i := by
    ext p
    rw [Heavy.mem_supp,cout]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨q,hq,hqy | eq⟩
      · exact (Finset.disjoint_left.mp di hq hqy).elim
      · exact eq ▸ hq
    · exact fun hp => ⟨p,hp,Or.inr rfl⟩
  have outsideOutput (i) (notIn : i∉B ∨ ¬Disjoint (S i) y) (two : 2≤(S i).card) : o i∉H := by
    intro mem
    obtain ⟨j,hj,hw⟩ := Finset.mem_biUnion.mp mem
    have high := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
    by_cases di : Disjoint (S i) y
    · have nb := notIn.resolve_right (not_not_intro di)
      have hs : S i ⊆ S j := (outputHeavy i di) ▸ high.1
      have ne : i≠j := fun eq => nb (eq.symm ▸ hj)
      have cap := hlin i j ne
      rw [Finset.inter_eq_left.mpr hs] at cap
      omega
    · have ⟨p,hp,py⟩ := Finset.not_disjoint_iff.mp di
      have h := high.2.2
      rw [cout] at h
      exact (of_decide_eq_false h) ⟨p,hp,decide_eq_true py⟩
  have countAnd (i) (short : (assigned D (S i)).card+1<(S i).card) :
      2≤((assigned D (S i)).filter (andAt D n)).card := by
    have r := many_private_ands (k:=y.card) D (S i) (f (o i)) goodD
      (fun p => ((mem_support _ _ _).symm.trans (by rw [modelSup])))
      (fun x hx off => (modelOut i x hx).trans (decide_eq_false (fun ⟨p,hp,on⟩ =>
        Bool.noConfusion ((off p hp).symm.trans on)))) short
    rw [hk] at r
    omega
  have bonusCap (i) (hi : i∈K) : (P i).card≤2 := by
    obtain ⟨ne,ji⟩ := Finset.mem_erase.mp hi
    have w := weights i ne
    rw [if_pos ji,hk] at w
    have bound : (assigned D (S i)).card≤3 := by omega
    by_cases inB : i∈B
    · have big := (Finset.mem_filter.mp inB).2.2.2
      have low := countAnd i (by omega)
      have sub : P i ⊆ (assigned D (S i)).filter (fun w => ¬andAt D n w) := by
        intro w hw
        obtain ⟨ass,wh⟩ := Finset.mem_filter.mp hw
        refine Finset.mem_filter.mpr ⟨ass,?_⟩
        intro andD
        have wlo := (Finset.mem_Ico.mp (Finset.mem_filter.mp ass).1).1
        have nv : w≠n+a.val := by
          rintro rfl
          have x := (Finset.mem_filter.mp ass).2.2
          rw [empty,Finset.card_empty] at x
          omega
        have nz : w≠n+t := by
          intro e
          have h0 : value C (fun _ : Fin n => false) (n+t)=true :=
            hl (fun _ => false) (by simpa using (show 0<y.card by omega))
          have closed := (terminal_switch_closed C y t hg hu h0 hy).2
          obtain ⟨j,_,h⟩ := Finset.mem_biUnion.mp wh
          have sz := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.2.1
          rw [e,closed,Finset.card_empty] at sz
          omega
        exact hOr w wh ((opsD w wlo nv nz).mp andD)
      have c := Finset.card_le_card sub
      have split := Finset.card_filter_add_card_filter_not (s:=assigned D (S i)) (andAt D n)
      omega
    · by_cases small : (S i).card≤2
      · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by omega)
      have two : 2≤(S i).card := by omega
      have nonempty := Finset.card_pos.mp (by omega : 0<(S i).card)
      have sup : support D (o i)=S i := (same _ (readerNotOut i nonempty)).trans (outputSup i)
      have big : 2≤(support (n:=n) D (o i)).card := by rwa [sup]
      have own : o i∈assigned D (S i) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate D _ big),by rw [sup],big⟩
      have sub : P i ⊆ (assigned D (S i)).erase (o i) := by
        intro w hw
        obtain ⟨ass,wh⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_erase.mpr ⟨fun e => outsideOutput i (Or.inl inB) two (e ▸ wh),ass⟩
      have c := Finset.card_le_card sub
      rw [Finset.card_erase_of_mem own] at c
      omega
  have upperU : U.card≤10 := by
    have other := Finset.card_biUnion_le_card_mul K P 2 bonusCap
    have count := Finset.card_union_le Q (K.biUnion P)
    have kJ := Finset.card_le_card (Finset.erase_subset d J)
    change K.card≤J.card at kJ
    change (Q∪K.biUnion P).card≤10
    omega
  have role (w) (valid : w∈Finset.Ico n (n+D.size)) (away : w∉A) (nv : w≠n+a.val)
      (nz : w≠n+t) (notAnd : ¬andAt D n w) (wh : w∈H) :
      w ∈ U ∨ ∃ i, ¬Disjoint (S i) y ∧ (assigned D (S i)).card+1≤min y.card (S i).card ∧
        w∈assigned D (S i) := by
    rcases classify w valid away nv nz with ⟨i,ne,ass⟩ | q
    · by_cases ij : i∈J
      · exact Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_biUnion.mpr ⟨i,Finset.mem_erase.mpr ⟨ne,ij⟩,Finset.mem_filter.mpr ⟨ass,wh⟩⟩)))
      have pay := weights i ne
      rw [if_neg ij,Nat.add_zero] at pay
      refine Or.inr ⟨i,?_,pay,ass⟩
      intro dis
      have big := (Finset.mem_filter.mp ass).2.2.trans (Finset.card_le_card (Finset.mem_filter.mp ass).2.1)
      have longer := (long i dis big).resolve_right ij
      have paid := countAnd i (by omega)
      have strict := Finset.card_lt_card ((Finset.ssubset_iff_of_subset (Finset.filter_subset
        (andAt D n) (assigned D (S i)))).mpr ⟨w,ass,fun h => notAnd (Finset.mem_filter.mp h).2⟩)
      omega
    · exact Or.inl (Finset.mem_union.mpr (Or.inl q))
  obtain ⟨E,cnt,triples⟩ := bounded_fold_crossing_lower S C D o t (n+a.val) y B A U hk
    (fun i hi => (Finset.mem_filter.mp hi).2.1) hlin hg hu ho hl hy dlen av empty
    readerRole (fun i met => by
      obtain ⟨p,hp,_⟩ := Finset.not_disjoint_iff.mp met
      exact readerNotOut i ⟨p,hp⟩) same opsD (fun w hw => (aRoles w hw).2) role
  have rank := Finset.sum_congr (s₁:=B) rfl (f:=fun i => (S i).card)
    (g:=fun i => 1+((S i).card-1)) (fun i hi => by
      have b := (Finset.mem_filter.mp hi).2.2.2
      omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,bc,mass] at rank
  have hgap : (∑ i ∈ B, (S i).card) ≤ 5*B.card+8 := by rw [mass,bc]
  have cap := crossing_cap_under_eight_slack S C o t y hk hlin hg hu ho hl hy E bad hgap triples
  omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

theorem num_inputs_twenty_five : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 25 →
    (rowLinearity S) →
    hasAllowedGates C → onlyNegAt C t → computesRows C S o → switchLight (n:=n) C t y.card →
    value C (fun p => decide (p ∈ y)) (n+t) = false →
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy
  by_contra bad
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  obtain ⟨_,hk,cover,profiles⟩ :=
    twenty_five_mass_residual S C o t y hn hlin hg hu ho hl hy bad
  have cap (i) (hi : i ∈ B) : 4*B.card+(S i).card+3 < ∑ j ∈ B, (S j).card := by
    by_contra! h
    apply bad (folded_projection S i C o t y (by omega) hlin hg hu ho hl hy
      (Finset.mem_filter.mp hi).2.2.1 ?_)
    rw [hk]
    exact h
  have either : (B.card=3 ∧ (∑ i ∈ B, (S i).card)=25) ∨
      (B.card=4 ∧ (∑ i ∈ B, (S i).card)=28) := profiles
  rcases either with ⟨bc,mass⟩ | ⟨bc,mass⟩
  · have top (i) (hi : i∈B) : (S i).card≤9 := by
      have b := cap i hi
      omega
    obtain ⟨⟨d,hd,nine⟩,_⟩ := three_mass_twenty_five_sizes S B bc mass top
    exact bad (three_mass25_full_cover_bound S C o t y d hk hlin hg hu ho hl hy
      ⟨bc,mass,hd,nine,cover⟩)
  · have top (i) (hi : i∈B) : (S i).card≤8 := by
      have b := cap i hi
      omega
    obtain ⟨d,hd,largest⟩ := B.exists_max_image (fun i => (S i).card)
      (Finset.card_pos.mp (by omega : 0<B.card))
    have capMass := Finset.sum_le_sum (s:=B) largest
    rw [Finset.sum_const,smul_eq_mul,bc,mass] at capMass
    have range : (S d).card=7 ∨ (S d).card=8 := by have := top d hd; omega
    exact bad (four_rows_top_bound S C o t y d hk hlin hg hu ho hl hy
      ⟨bc,mass,cover,hd,range⟩)


theorem num_inputs_twenty_four : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 24 →
    (rowLinearity S) →
    hasAllowedGates C → onlyNegAt C t → computesRows C S o → switchLight (n:=n) C t y.card →
    (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n+t) false = false →
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m := by
  intro n m S C o t y hn
  exact num_inputs_twenty_five n m S C o t y (by omega)

theorem num_inputs_twenty_three : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 23 → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  intro n m S C o t y hn
  exact num_inputs_twenty_five n m S C o t y (by omega)


theorem num_inputs_twenty_two : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 22 → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  intro n m S C o t y hn
  exact num_inputs_twenty_five n m S C o t y (by omega)

theorem size_window_seven : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card ≤ 2 ∨ n ≤ 7*y.card+1) → (rowLinearity S) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m := by
  intro n m S C o t y hsize
  by_cases hn : n ≤ 22
  · exact num_inputs_twenty_two n m S C o t y hn
  · apply size_window_joint n m S C o t y
    omega

end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

lemma twenty_six_row_profiles {n m : ℕ} (S : Fin m → Finset (Fin n))
    (B : Finset (Fin m)) (V : Finset (Fin n))
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hsub : ∀ i ∈ B, S i ⊆ V) (hV : V.card ≤ 23)
    (hbig : ∀ i ∈ B, 5 ≤ (S i).card)
    (hstd : 5*B.card+5 ≤ ∑ i ∈ B, (S i).card)
    (hfold : ∀ i ∈ B, 4*B.card+(S i).card+3 < ∑ j ∈ B, (S j).card)
    (hcut : 4 ≤ B.card → 5*B.card+8 ≤ (∑ i ∈ B, (S i).card))
    (hcutLarge : 7 ≤ B.card → 5*B.card+9 ≤ (∑ i ∈ B, (S i).card)) :
    let M := ∑ i ∈ B, (S i).card
    ((B.card=2 ∧ M=24) ∨
       (B.card=3 ∧ 24≤M ∧ M≤26) ∨
       (B.card=4 ∧ 28≤M ∧ M≤29) ∨
       (B.card=5 ∧ M=33) ∨
       (B.card=6 ∧ M=38) ∨
       (B.card=7 ∧ M=44)) ∧
     (M=23+B.card.choose 2 → B.biUnion S=V) := by
  classical
  have bSmall : B.card ≤ 8 := by
    by_contra! tooLarge
    have subMass (I : Finset (Fin m)) (hI : I ⊆ B) (hc : I.card=9) :
        (∑ i ∈ I, (S i).card) ≤ 5*9+7 := by
      have hp := pair_incidence S I V (fun i hi => hsub i (hI hi)) hlin
      rw [hc] at hp
      norm_num [Nat.choose] at hp ⊢
      omega
    have total := row_surplus_of_subsets S B 9 7 (by decide) tooLarge hbig subMass
    have lower := hcut (by omega)
    omega
  have nonempty : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hstd
    simp at hstd
  obtain ⟨d,hd,largest⟩ := B.exists_max_image (fun i => (S i).card) nonempty
  have fst := hfold d hd
  have mx := Finset.sum_le_sum (s:=B) largest
  simp only [Finset.sum_const,smul_eq_mul] at mx
  have all : B.biUnion S ⊆ V := by
    intro p hp
    obtain ⟨i,hi,hit⟩ := Finset.mem_biUnion.mp hp
    exact hsub i hi hit
  have ug := Finset.card_le_card all
  have un := line_union S hlin B
  have pair := pair_incidence S B V hsub hlin
  have pos := Finset.card_pos.mpr nonempty
  let M := ∑ i ∈ B, (S i).card
  have profiles : (B.card=2 ∧ M=24) ∨
       (B.card=3 ∧ 24≤M ∧ M≤26) ∨
       (B.card=4 ∧ 28≤M ∧ M≤29) ∨
       (B.card=5 ∧ M=33) ∨
       (B.card=6 ∧ M=38) ∨
       (B.card=7 ∧ M=44) := by
    dsimp [M]
    generalize heq : B.card = b at *
    interval_cases b <;> norm_num [Nat.choose] at * <;> omega
  refine ⟨profiles,fun saturated => Finset.eq_of_subset_of_card_le all ?_⟩
  change M ≤ (B.biUnion S).card+B.card.choose 2 at un
  omega


theorem twenty_six_residual : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 26 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (hasAllowedGates C) → (onlyNegAt C t) → (computesRows C S o) → (switchLight (n:=n) C t y.card) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → ¬ ((∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (refunds S C y).card + m) →
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
    let M := ∑ i ∈ B, (S i).card
    n=26 ∧ y.card=3 ∧
    ((B.card=2 ∧ M=24) ∨
       (B.card=3 ∧ 24≤M ∧ M≤26) ∨
       (B.card=4 ∧ 28≤M ∧ M≤29) ∨
       (B.card=5 ∧ M=33) ∨
       (B.card=6 ∧ M=38) ∨
       (B.card=7 ∧ M=44)) ∧
    (M=23+B.card.choose 2 → B.biUnion S=Finset.univ \ y) := by
  classical
  intro n m S C o t y hn hlin hg hu ho hl hy bad
  have n26 : n=26 := by
    by_contra h
    exact bad (num_inputs_twenty_five n m S C o t y (by omega) hlin hg hu ho hl hy)
  have hk : y.card=3 := by
    by_contra h
    exact bad (size_window_seven n m S C o t y (by omega) hlin hg hu ho hl hy)
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  let V := Finset.univ \ y
  have uc : V.card ≤ 23 := by simp [V,Finset.card_sdiff_of_subset (Finset.subset_univ y),hk,n26]
  have sub (i) (hi : i ∈ B) : S i ⊆ V := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,Finset.disjoint_left.mp (Finset.mem_filter.mp hi).2.1 hp⟩
  have big (i) (hi : i ∈ B) : 5 ≤ (S i).card := (Finset.mem_filter.mp hi).2.2.2
  have ordinary : 5*B.card+5 ≤ ∑ i ∈ B, (S i).card := by
    by_contra! h
    apply bad (three_window_bound n m S C o t y ⟨hk,?_⟩ hlin hg hu ho hl hy)
    unfold threeRowQuota
    rw [hk]
    change B.Nonempty → _
    exact fun ⟨d,hd⟩ => ⟨d,hd,Or.inr (by
      change (∑ i ∈ B, (S i).card) ≤ B.card*5+4
      omega)⟩
  have fold (d) (hd : d ∈ B) : 4*B.card+(S d).card+3 < ∑ i ∈ B, (S i).card := by
    by_contra! h
    apply bad (folded_projection S d C o t y (by omega) hlin hg hu ho hl hy (Finset.mem_filter.mp hd).2.2.1 ?_)
    rw [hk]
    change _ ≤ 4*B.card+(S d).card+3
    exact h
  have cut (b : 4 ≤ B.card) : 5*B.card+8 ≤ ∑ i ∈ B, (S i).card := by
    by_contra! h
    exact bad (tight_crossing_bound S C o t y hk hlin hg hu ho hl hy (Or.inl ⟨b,show (∑ i ∈ B, (S i).card) ≤ 5*B.card+7 by omega⟩))
  have cutLarge (b : 7 ≤ B.card) : 5*B.card+9 ≤ ∑ i ∈ B, (S i).card := by
    by_contra! h
    exact bad (tight_crossing_bound S C o t y hk hlin hg hu ho hl hy (Or.inr ⟨b,show (∑ i ∈ B, (S i).card) ≤ 5*B.card+8 by omega⟩))
  exact ⟨n26,hk,twenty_six_row_profiles S B V hlin sub uc big ordinary fold cut cutLarge⟩


end L_meta_997.Small

namespace L_meta_997.Small
open PEqualNP.CircuitLowerBounds L_meta_997.Light L_meta_997_aux

theorem twenty_six_sharp_residual {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hn : n≤26)
    (hlin : rowLinearity S) (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p∈y)) (n+t)=false)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m)) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
    let M := ∑ i ∈ B, (S i).card
    n=26 ∧ y.card=3 ∧
    ((B.card=3 ∧ M=26) ∨ (B.card=4 ∧ 28≤M ∧ M≤29) ∨
      (B.card=5 ∧ M=33) ∨ (B.card=6 ∧ M=38) ∨ (B.card=7 ∧ M=44)) ∧
    (∀ i∈B, 4*B.card+(S i).card+4 < M) ∧
    (M=23+B.card.choose 2 → B.biUnion S=Finset.univ \ y) := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card+1 < (S i).card ∧ 5 ≤ (S i).card)
  let M := ∑ i ∈ B, (S i).card
  obtain ⟨n26,hk,cases,cover⟩ := twenty_six_residual n m S C o t y hn hlin hg hu ho hl hy bad
  have shape : (B.card=2 ∧ M=24) ∨ (B.card=3 ∧ 24≤M ∧ M≤26) ∨
      (B.card=4 ∧ 28≤M ∧ M≤29) ∨ (B.card=5 ∧ M=33) ∨
      (B.card=6 ∧ M=38) ∨ (B.card=7 ∧ M=44) := cases
  have sharp (i) (hi : i∈B) : 4*B.card+(S i).card+4 < M := by
    by_contra! b
    exact bad (three_tight_folded_projection S C o t y i hk hlin hg hu ho hl hy ⟨hi,b⟩)
  refine ⟨n26,hk,?_,sharp,cover⟩
  rcases shape with ⟨bc,mass⟩ | ⟨bc,lo,up⟩ | rest
  · exfalso
    have small (i) (hi : i∈B) : (S i).card≤11 := by have := sharp i hi; omega
    have sum := Finset.sum_le_sum (s:=B) small
    rw [Finset.sum_const,smul_eq_mul,bc] at sum
    change M ≤ _ at sum
    omega
  · left
    refine ⟨bc,?_⟩
    by_cases eq : M=26
    · exact eq
    exfalso
    have up' : M≤25 := by omega
    have small (i) (hi : i∈B) : (S i).card≤8 := by
      have count := sharp i hi
      rw [bc] at count
      omega
    have sum := Finset.sum_le_sum (s:=B) small
    rw [Finset.sum_const,smul_eq_mul,bc] at sum
    change M ≤ _ at sum
    by_cases em : M=24
    · have smaller (i) (hi : i∈B) : (S i).card≤7 := by have := sharp i hi; omega
      have sum' := Finset.sum_le_sum (s:=B) smaller
      rw [Finset.sum_const,smul_eq_mul,bc] at sum'
      change M ≤ _ at sum'
      omega
    · omega
  · exact Or.inr rest

end L_meta_997.Small

end PEqualNP.Outside
namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

private theorem dormant_singleton_filter_empty {n : ℕ} (C : Circuit) (T : Finset (Fin n)) :
    ((dormant C T).filter (fun w => (support (n:=n) C w).card=1))=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w h
  obtain ⟨hw,hc⟩ := Finset.mem_filter.mp h
  have big := (Finset.mem_filter.mp hw).2.2
  have le := Finset.card_le_card
    (show support C w ∩ T ⊆ support C w from Finset.inter_subset_left)
  omega

theorem projection_gate_count_one_slack_singletons {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (z : ℕ) (A : Finset ℕ) (hD : 2 ≤ (S d).card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hzrange : z ∈ Finset.Ico n (n+C.size)) (htz : value C (fun _ : Fin n => false) z=true)
    (hzs : ∀ p : Fin n, p ∈ support C z)
    (hAi : A ⊆ Finset.Ico n (n+C.size)) (hAz : z ∉ A) (hAs : ∀ w ∈ A, support (n:=n) C w=∅)
    (q : ℕ) (hdweight : q ≤ (dormant C (S d)).card+1)
    (f : Fin m → ℕ)
    (hweight : ∀ i, i ≠ d → f i ≤ (assigned C (S i)).card+1)
    (near : C.gates.length + m ≤ q + (∑ i ∈ Finset.univ.erase d, f i) + A.card+2) :
    ∃ Q : Finset ℕ, ∃ J : Finset (Fin m), Q.card+J.card≤q ∧ J.card≤1 ∧
      (∀ i, i≠d → (assigned C (S i)).card+1=f i+(if i∈J then 1 else 0)) ∧
      (∀ w ∈ Finset.Ico n (n+C.size), w ∉ A → w≠z →
        (∃ i, i≠d ∧ w ∈ assigned C (S i)) ∨ w∈Q) ∧
      (Q.filter (fun w => (support (n:=n) C w).card=1)).card+J.card≤1 := by
  classical
  by_cases e : ∃ i, i≠d ∧ f i < (assigned C (S i)).card+1
  · obtain ⟨i,ne,lt⟩ := e
    let f' := fun j => f j + (if j=i then 1 else 0)
    have greater (j) (nd : j≠d) : f' j ≤ (assigned C (S j)).card+1 := by
      by_cases eq : j=i
      · subst j
        simp [f']
        omega
      · simpa [f',eq] using hweight j nd
    have sum : (∑ j ∈ Finset.univ.erase d, f' j) = (∑ j ∈ Finset.univ.erase d, f j)+1 := by
      have h : i∈Finset.univ.erase d := Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩
      simp only [f',Finset.sum_add_distrib,Finset.sum_ite_eq',h,ite_true]
    have tight : C.gates.length + m ≤ q + (∑ j ∈ Finset.univ.erase d, f' j) + A.card+1 := by
      rw [sum]
      omega
    obtain ⟨count,weights,cover⟩ := projection_gate_count_tight S d C z A hD hpair hzrange htz
      hzs hAi hAz hAs q hdweight f' greater tight
    refine ⟨dormant C (S d),{i},by rw [Finset.card_singleton,count],by simp,?_,cover,?_⟩
    · intro j neq
      simpa [f'] using weights j neq
    · simp [dormant_singleton_filter_empty]
  push Not at e
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
  let W := insert z (U ∪ G)
  have disA : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro w wa ww
    rcases Finset.mem_insert.mp ww with hz | h
    · exact hAz (hz ▸ wa)
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨i,_,hw⟩ := Finset.mem_biUnion.mp h
        have hc := (Finset.mem_filter.mp hw).2.2
        rw [hAs w wa] at hc
        simp at hc
      · have hc := (Finset.mem_filter.mp h).2.2
        rw [hAs w wa] at hc
        simp at hc
  have sub : A ∪ W ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with ha | hw
    · exact hAi ha
    · rcases Finset.mem_insert.mp hw with h | hw
      · exact h ▸ hzrange
      · rcases Finset.mem_union.mp hw with hw | hw
        · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hw
          exact (Finset.mem_filter.mp hi).1
        · exact (Finset.mem_filter.mp hw).1
  have Wcard : (A ∪ W).card = A.card + (U.card + G.card + 1) := by
    rw [Finset.card_union_of_disjoint disA]
    simp only [W,Finset.card_insert_of_notMem hnotin,Finset.card_union_of_disjoint dis]
  have hgate := Finset.card_le_card sub
  rw [Wcard] at hgate
  simp only [Nat.card_Ico,Nat.add_sub_cancel_left,Circuit.size] at hgate
  have hcard := Finset.card_erase_add_one (Finset.mem_univ d)
  change I.card + 1 = _ at hcard
  simp only [Finset.card_univ,Fintype.card_fin] at hcard
  have hgeneral := sum_row_weights S I C f hpair (fun i hi => hweight i (Finset.mem_erase.mp hi).1)
  change (∑ i ∈ I, f i) ≤ U.card + I.card at hgeneral
  let R := (Finset.Ico n (n+C.size)) \ (A ∪ W)
  have partition := Finset.card_sdiff_add_card_eq_card sub
  change R.card+(A∪W).card=(Finset.Ico n (n+C.size)).card at partition
  rw [Wcard,Nat.card_Ico,Nat.add_sub_cancel_left] at partition
  change R.card+(A.card+(U.card+G.card+1))=C.gates.length at partition
  have qBound : (G∪R).card ≤ q := by
    have c := Finset.card_union_le G R
    change C.gates.length+m ≤ q+(∑ i ∈ I, f i)+A.card+2 at near
    omega
  have remaining : R.card≤1 := by
    change C.gates.length+m ≤ q+(∑ i ∈ I, f i)+A.card+2 at near
    change q≤G.card+1 at hdweight
    omega
  refine ⟨G∪R,∅,by simpa using qBound,by simp,?_,?_,?_⟩
  · intro i ne
    have lo := hweight i ne
    have hi := e i ne
    simp only [Finset.notMem_empty,ite_false,Nat.add_zero]
    omega
  · intro w wr wa wz
    by_cases covered : w∈A∪W
    · have hw : w∈U∪G := (Finset.mem_insert.mp ((Finset.mem_union.mp covered).resolve_left wa)).resolve_left wz
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨i,hi,wi⟩ := Finset.mem_biUnion.mp hw
        exact Or.inl ⟨i,(Finset.mem_erase.mp hi).1,wi⟩
      · exact Or.inr (Finset.mem_union.mpr (Or.inl hw))
    · exact Or.inr (Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨wr,covered⟩)))

  · have noSingleton :
        (G.filter (fun w => (support (n:=n) C w).card=1))=∅ :=
      dormant_singleton_filter_empty C (S d)
    rw [Finset.filter_union,noSingleton,Finset.empty_union,Finset.card_empty,Nat.add_zero]
    exact (Finset.card_filter_le _ _).trans remaining

end PEqualNP.Outside.L_meta_997.Light
namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem folded_model_one_slack_singletons {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i)=decide (∃ p ∈ S i, x p=true))
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card<y.card → value C x (n+t)=true)
    (hs : (assigned C (S d)).card+1 < (S d).card)
    (large : ∀ i, Disjoint (S i) y → y.card+2≤(S i).card →
       (assigned C (S i)).card+1<(S i).card)
    (quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
       (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+2)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m))
    (D : Circuit) (f : ℕ → ℕ) (v : ℕ) (goodD : good D) (sz : D.size=C.size)
    (after : n+t<v) (vr : v<n+C.size) (dead : ∀ x : Fin n → Bool, value D x v=false)
    (unchanged : ∀ w, w≠v → f w=w)
    (agree : ∀ (x : Fin n → Bool), (Finset.univ.filter (fun p => x p=true)).card<y.card →
      ∀ w, value D x (f w)=value C x w)
    (A : Finset ℕ) (ac : y.card ≤ A.card+1) (ar : A ⊆ Finset.Ico n (n+t))
    (ae : ∀ w ∈ A, support (n:=n) C w=∅) :
    ∃ Q : Finset ℕ, ∃ J : Finset (Fin m),
      Q.card+J.card≤(S d).card+y.card-1 ∧ J.card≤1 ∧
      (∀ i, Disjoint (S i) y → 2≤(S i).card → y.card<(S i).card ∨ i∈J) ∧
      (∀ i, i≠d → (assigned D (S i)).card+1 ≤ min y.card (S i).card + (if i∈J then 1 else 0)) ∧
      (∀ w ∈ Finset.Ico n (n+D.size), w ∉ A → w≠v → w≠n+t →
        (∃ i, i≠d ∧ w ∈ assigned D (S i)) ∨ w ∈ Q) ∧
      (Q.filter (fun w => (support (n:=n) D w).card=1)).card+J.card≤1 := by
  classical
  let k := y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ k+2 ≤ (S i).card)
  let R := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  have hk' : 2 ≤ k := hk
  have hbig : k < (S d).card := by have := card_light (S d) C (o d) t hg hu (out d) hl; change min k (S d).card ≤ _ at this; omega
  have zero : (Finset.univ.filter (fun _ : Fin n => false = true)).card < y.card := by simpa using (show 0<y.card by omega)
  have sing (p : Fin n) : (Finset.univ.filter (fun q : Fin n => decide (q=p) = true)).card < y.card := by
    have e : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [e,Finset.card_singleton]; omega
  have same (w : ℕ) (ne : w≠v) : support (n:=n) D w=support C w := by
    ext p; rw [mem_support,mem_support]
    rw [← unchanged w ne,agree _ (sing p) w,unchanged w ne]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,dead]
  have contain (i) : assigned D (S i) ⊆ assigned C (S i) := by
    intro w hw
    obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
    have ne : w≠v := by rintro rfl; rw [empty,Finset.card_empty] at hc; omega
    rw [same w ne] at hsub hc
    exact Finset.mem_filter.mpr ⟨sz ▸ hr,hsub,hc⟩
  have output (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) :
      value D x (f (o i))=decide (∃ p ∈ S i, x p=true) := (agree x hx _).trans (out i x)
  have singleton (i) (p : Fin n) : value D (fun q => decide (q=p)) (f (o i))=true ↔ p ∈ S i := by
    rw [output i _ (sing p)]; simp
  have sparse (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k)
      (off : ∀ p ∈ S i, x p=false) : value D x (f (o i))=false := by
    rw [output i x hx]; exact decide_eq_false (fun ⟨p,hp,on⟩ => Bool.noConfusion ((off p hp).symm.trans on))
  have mincount (i) : min k (S i).card ≤ (assigned D (S i)).card+1 := by
    by_cases e : (S i).card=0
    · simp [e]
    have cnt := card_assigned (k:=k-1) (c:=min k (S i).card-1) D (S i) (f (o i)) goodD (singleton i)
      (fun x hx => sparse i x (by omega)) (by omega) (by omega)
    omega
  have extra := (sharp_private_or_extra D (S d) (f (o d)) goodD
    (by rw [output d _ zero]; simp) (by ext p; exact (mem_support _ _ _).trans (singleton d p)) (sparse d)).resolve_left
    (by have h := Finset.card_le_card (contain d); omega)
  let weight (i : Fin m) := min k (S i).card
  have fund (i) : weight i ≤ (assigned D (S i)).card+1 := mincount i
  let z := n+t
  have zlt : z<v := after
  have za : z ∉ A := fun ha => Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar ha)).2
  have va : v ∉ A := fun ha => Nat.lt_asymm after (Finset.mem_Ico.mp (ar ha)).2
  have zOn (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) : value D x z=true := by
    have eq := agree x hx z
    rw [unchanged z (ne_of_lt zlt)] at eq
    exact eq.trans (hl x hx)
  have computed := projection_gate_count S d D z (insert v A) (by omega) hpair
    (Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩) (zOn _ zero)
    (fun p => (mem_support _ _ _).mpr (zOn _ (sing p)))
    (Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by rw [sz]; have h := (Finset.mem_Ico.mp (ar hw)).2; omega⟩))
    (by simpa [ne_of_lt zlt] using za)
    (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact empty
      · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw))
    ((S d).card+k-1) (by omega) weight (fun i _ => fund i)
  have calcD := computed
  rw [Finset.card_insert_of_notMem va] at calcD
  have hlen : D.gates.length=C.gates.length := sz
  rw [hlen] at calcD
  have wd : weight d=k := by simp [weight,Nat.not_le.mpr hs,min_eq_left (by omega : k≤(S d).card)]
  have cut := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) weight (Finset.mem_univ d)
  rw [wd] at cut
  let L := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2≤(S i).card ∧ (S i).card≤k)
  have per (i) : (if Disjoint (S i) y then (S i).card else min k (S i).card) +
      (if i∈L then 1 else 0) ≤
      weight i + (if i∈R then 1 else 0) + (if i∈B then (S i).card-(k+1) else 0) := by
    by_cases hd : Disjoint (S i) y
    swap
    · simp [weight,B,R,L,hd]
    by_cases hs : (S i).card≤k
    · have nb : ¬ k+2 ≤ (S i).card := by omega
      simp [weight,B,R,L,hd,hs,nb,min_eq_right hs]
    · have hl : k<(S i).card := by omega
      by_cases big : k+2≤(S i).card
      · have under := large i hd big
        simp [weight,B,R,L,hd,hs,big,under,min_eq_left hl.le,
          show 2≤(S i).card by omega]
        omega
      · simp [weight,B,R,L,hd,hs,big,min_eq_left hl.le,
          show 2≤(S i).card by omega]
        omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simp only [Finset.sum_add_distrib,Fintype.sum_ite_mem,Finset.sum_const,smul_eq_mul,mul_one] at total
  have split := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl
    (g:=fun i => (k+1)+((S i).card-(k+1))) (fun i hi => by
      have h := (Finset.mem_filter.mp hi).2.2.2
      omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_comm B.card (k+1)] at split
  change (∑ i ∈ B, (S i).card) ≤ (k+1)*B.card+(S d).card+k+2 at quota
  have ref := disjoint_outputs_refunded S C o y R hpair out (fun i hi => (Finset.mem_filter.mp hi).2)
  change ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤ _) at bad
  change k ≤ A.card+1 at ac
  let coldSet := insert v A
  have coldSize : coldSet.card=A.card+1 := Finset.card_insert_of_notMem va
  have cycle : D.gates.length+m+L.card ≤ (S d).card+k-1 +
      (∑ i ∈ Finset.univ.erase d, weight i)+coldSet.card+2 := by
    rw [hlen,coldSize]
    omega
  have cv : coldSet ⊆ Finset.Ico n (n+D.size) :=
    Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by
        rw [sz]
        have h := (Finset.mem_Ico.mp (ar hw)).2
        omega⟩)
  have zrange : z∈Finset.Ico n (n+D.size) :=
    Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩
  have znot : z∉coldSet := by simpa [coldSet,ne_of_lt zlt] using za
  have sign (w) (hw : w∈coldSet) : support (n:=n) D w=∅ := by
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact empty
    · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw)
  have lsmall : L.card≤1 := by rw [coldSize,hlen] at cycle; omega
  have zsupport (p : Fin n) : p∈support D z := (mem_support _ _ _).mpr (zOn _ (sing p))
  by_cases lpos : L.Nonempty
  · have lsize : L.card=1 := by have := Finset.card_pos.mpr lpos; omega
    have tight : D.gates.length+m ≤ (S d).card+k-1 +
        (∑ i ∈ Finset.univ.erase d, weight i)+coldSet.card+1 := by omega
    obtain ⟨count,weights,role⟩ := projection_gate_count_tight S d D z coldSet (by omega)
      hpair zrange (zOn _ zero) zsupport cv znot sign ((S d).card+k-1) (by omega)
        weight (fun i _ => fund i) tight
    refine ⟨dormant D (S d),L,by omega,lsmall,?_,?_,?_,?_⟩
    · intro i dis big
      by_cases small : (S i).card≤k
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis,big,small⟩)
      · exact Or.inl (by omega)
    · intro i ne
      rw [weights i ne]
      simp only [weight]
      omega
    · intro w wr wa wv wz
      exact role w wr (by simp [coldSet,wa,wv]) wz
    · rw [dormant_singleton_filter_empty,Finset.card_empty,Nat.zero_add]
      exact lsmall
  · have lempty := Finset.not_nonempty_iff_eq_empty.mp lpos
    obtain ⟨Q,J,num,jc,weights,role,singletons⟩ := projection_gate_count_one_slack_singletons S d D z coldSet (by omega)
      hpair zrange (zOn _ zero) zsupport cv znot sign ((S d).card+k-1) (by omega)
        weight (fun i _ => fund i) (by omega)
    refine ⟨Q,J,num,jc,?_,fun i ne => (weights i ne).le,?_,singletons⟩
    · intro i dis big
      left
      by_contra! smaller
      have ine : i∈L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis,big,smaller⟩
      simpa [lempty] using ine
    · intro w wr wa wv wz
      exact role w wr (by simp [coldSet,wa,wv]) wz

end PEqualNP.Outside.L_meta_997.Light
namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem folded_model_one_slack_paid {n m : ℕ} (S : Fin m → Finset (Fin n)) (d : Fin m)
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hk : 2 ≤ y.card)
    (hpair : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (out : ∀ (i : Fin m) (x : Fin n → Bool), value C x (o i)=decide (∃ p ∈ S i, x p=true))
    (hl : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card<y.card → value C x (n+t)=true)
    (hs : (assigned C (S d)).card+1 < (S d).card)
    (quota : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ y.card+2 ≤ (S i).card)
       (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+2)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (refunds S C y).card + m))
    (D : Circuit) (f : ℕ → ℕ) (v : ℕ) (goodD : good D) (sz : D.size=C.size)
    (after : n+t<v) (vr : v<n+C.size) (dead : ∀ x : Fin n → Bool, value D x v=false)
    (unchanged : ∀ w, w≠v → f w=w)
    (agree : ∀ (x : Fin n → Bool), (Finset.univ.filter (fun p => x p=true)).card<y.card →
      ∀ w, value D x (f w)=value C x w)
    (A : Finset ℕ) (ac : y.card ≤ A.card+1) (ar : A ⊆ Finset.Ico n (n+t))
    (ae : ∀ w ∈ A, support (n:=n) C w=∅) :
    ∃ Q : Finset ℕ, ∃ J : Finset (Fin m),
      Q.card+J.card≤(S d).card+y.card-1 ∧ J.card≤1 ∧
      (∀ i, Disjoint (S i) y → 2≤(S i).card → y.card<(S i).card ∨ i∈J) ∧
      (∀ i, i≠d → ¬Disjoint (S i) y →
        (assigned D (S i)).card+1 ≤ min y.card (S i).card + (if i∈J then 1 else 0)) ∧
      (∀ w ∈ Finset.Ico n (n+D.size), w ∉ A → w≠v → w≠n+t →
        (∃ i, i≠d ∧ w ∈ assigned D (S i)) ∨ w ∈ Q) ∧
      (Q.filter (fun w => (support (n:=n) D w).card=1)).card+J.card≤1 := by
  classical
  let k := y.card
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
       (assigned C (S i)).card+1 < (S i).card ∧ k+2 ≤ (S i).card)
  let R := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  have hk' : 2 ≤ k := hk
  have hbig : k < (S d).card := by have := card_light (S d) C (o d) t hg hu (out d) hl; change min k (S d).card ≤ _ at this; omega
  have zero : (Finset.univ.filter (fun _ : Fin n => false = true)).card < y.card := by simpa using (show 0<y.card by omega)
  have sing (p : Fin n) : (Finset.univ.filter (fun q : Fin n => decide (q=p) = true)).card < y.card := by
    have e : Finset.univ.filter (fun q : Fin n => decide (q=p) = true) = {p} := by ext; simp
    rw [e,Finset.card_singleton]; omega
  have same (w : ℕ) (ne : w≠v) : support (n:=n) D w=support C w := by
    ext p; rw [mem_support,mem_support]
    rw [← unchanged w ne,agree _ (sing p) w,unchanged w ne]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,dead]
  have contain (i) : assigned D (S i) ⊆ assigned C (S i) := by
    intro w hw
    obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
    have ne : w≠v := by rintro rfl; rw [empty,Finset.card_empty] at hc; omega
    rw [same w ne] at hsub hc
    exact Finset.mem_filter.mpr ⟨sz ▸ hr,hsub,hc⟩
  have lose (i) : (assigned C (S i)).card ≤ (assigned D (S i)).card+1 := by
    have sub : assigned C (S i) ⊆ insert v (assigned D (S i)) := by
      intro w hw
      by_cases e : w=v
      · exact Finset.mem_insert.mpr (Or.inl e)
      obtain ⟨hr,hsub,hc⟩ := Finset.mem_filter.mp hw
      rw [←same w e] at hsub hc
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨sz.symm ▸ hr,hsub,hc⟩))
    exact (Finset.card_le_card sub).trans (Finset.card_insert_le ..)
  have output (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) :
      value D x (f (o i))=decide (∃ p ∈ S i, x p=true) := (agree x hx _).trans (out i x)
  have singleton (i) (p : Fin n) : value D (fun q => decide (q=p)) (f (o i))=true ↔ p ∈ S i := by
    rw [output i _ (sing p)]; simp
  have sparse (i) (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k)
      (off : ∀ p ∈ S i, x p=false) : value D x (f (o i))=false := by
    rw [output i x hx]; exact decide_eq_false (fun ⟨p,hp,on⟩ => Bool.noConfusion ((off p hp).symm.trans on))
  have mincount (i) : min k (S i).card ≤ (assigned D (S i)).card+1 := by
    by_cases e : (S i).card=0
    · simp [e]
    have cnt := card_assigned (k:=k-1) (c:=min k (S i).card-1) D (S i) (f (o i)) goodD (singleton i)
      (fun x hx => sparse i x (by omega)) (by omega) (by omega)
    omega
  have extra := (sharp_private_or_extra D (S d) (f (o d)) goodD
    (by rw [output d _ zero]; simp) (by ext p; exact (mem_support _ _ _).trans (singleton d p)) (sparse d)).resolve_left
    (by have h := Finset.card_le_card (contain d); omega)
  let weight (i : Fin m) := if Disjoint (S i) y ∧ k < (S i).card ∧ (S i).card ≤ (assigned C (S i)).card+1
    then (S i).card-1 else min k (S i).card
  have fund (i) : weight i ≤ (assigned D (S i)).card+1 := by
    dsimp [weight]; split
    · rename_i h; have := lose i; have := h.2.2; omega
    · exact mincount i
  let z := n+t
  have zlt : z<v := after
  have za : z ∉ A := fun ha => Nat.lt_irrefl _ (Finset.mem_Ico.mp (ar ha)).2
  have va : v ∉ A := fun ha => Nat.lt_asymm after (Finset.mem_Ico.mp (ar ha)).2
  have zOn (x : Fin n → Bool) (hx : (Finset.univ.filter (fun p => x p=true)).card<k) : value D x z=true := by
    have eq := agree x hx z
    rw [unchanged z (ne_of_lt zlt)] at eq
    exact eq.trans (hl x hx)
  have computed := projection_gate_count S d D z (insert v A) (by omega) hpair
    (Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩) (zOn _ zero)
    (fun p => (mem_support _ _ _).mpr (zOn _ (sing p)))
    (Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by rw [sz]; have h := (Finset.mem_Ico.mp (ar hw)).2; omega⟩))
    (by simpa [ne_of_lt zlt] using za)
    (fun w hw => by
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact empty
      · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw))
    ((S d).card+k-1) (by omega) weight (fun i _ => fund i)
  have calcD := computed
  rw [Finset.card_insert_of_notMem va] at calcD
  have hlen : D.gates.length=C.gates.length := sz
  rw [hlen] at calcD
  have wd : weight d=k := by simp [weight,Nat.not_le.mpr hs,min_eq_left (by omega : k≤(S d).card)]
  have cut := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) weight (Finset.mem_univ d)
  rw [wd] at cut
  let L := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2≤(S i).card ∧ (S i).card≤k)
  have per (i) : (if Disjoint (S i) y then (S i).card else min k (S i).card) +
      (if i∈L then 1 else 0) ≤
      weight i + (if i∈R then 1 else 0) + (if i∈B then (S i).card-(k+1) else 0) := by
    by_cases hd : Disjoint (S i) y
    swap
    · simp [weight,B,R,L,hd]
    by_cases hs : (S i).card≤k
    · have nb : ¬ k+2 ≤ (S i).card := by omega
      simp [weight,B,R,L,hd,hs,nb,Nat.not_lt.mpr hs,min_eq_right hs]
    · have hl : k<(S i).card := by omega
      have two : 2≤(S i).card := by omega
      by_cases paid : (S i).card≤(assigned C (S i)).card+1
      · simp [weight,B,R,L,hd,hs,hl,paid,two,Nat.not_lt.mpr paid]
        omega
      have under := Nat.lt_of_not_ge paid
      by_cases big : k+2≤(S i).card
      · simp [weight,B,R,L,hd,hs,hl,big,under,paid,min_eq_left hl.le,two]
        omega
      · simp [weight,B,R,L,hd,hs,hl,big,paid,min_eq_left hl.le,two]
        omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simp only [Finset.sum_add_distrib,Fintype.sum_ite_mem,Finset.sum_const,smul_eq_mul,mul_one] at total
  have split := Finset.sum_congr (s₁:=B) (f:=fun i => (S i).card) rfl
    (g:=fun i => (k+1)+((S i).card-(k+1))) (fun i hi => by
      have h := (Finset.mem_filter.mp hi).2.2.2
      omega)
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,Nat.mul_comm B.card (k+1)] at split
  change (∑ i ∈ B, (S i).card) ≤ (k+1)*B.card+(S d).card+k+2 at quota
  have ref := disjoint_outputs_refunded S C o y R hpair out (fun i hi => (Finset.mem_filter.mp hi).2)
  change ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤ _) at bad
  change k ≤ A.card+1 at ac
  let coldSet := insert v A
  have coldSize : coldSet.card=A.card+1 := Finset.card_insert_of_notMem va
  have cycle : D.gates.length+m+L.card ≤ (S d).card+k-1 +
      (∑ i ∈ Finset.univ.erase d, weight i)+coldSet.card+2 := by
    rw [hlen,coldSize]
    omega
  have cv : coldSet ⊆ Finset.Ico n (n+D.size) :=
    Finset.insert_subset (Finset.mem_Ico.mpr ⟨by omega,sz.symm ▸ vr⟩)
      (fun w hw => Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp (ar hw)).1,by
        rw [sz]
        have h := (Finset.mem_Ico.mp (ar hw)).2
        omega⟩)
  have zrange : z∈Finset.Ico n (n+D.size) :=
    Finset.mem_Ico.mpr ⟨by dsimp [z]; omega,by rw [sz]; omega⟩
  have znot : z∉coldSet := by simpa [coldSet,ne_of_lt zlt] using za
  have sign (w) (hw : w∈coldSet) : support (n:=n) D w=∅ := by
    rcases Finset.mem_insert.mp hw with rfl|hw
    · exact empty
    · exact (same w (fun e => va (e ▸ hw))).trans (ae w hw)
  have lsmall : L.card≤1 := by rw [coldSize,hlen] at cycle; omega
  have zsupport (p : Fin n) : p∈support D z := (mem_support _ _ _).mpr (zOn _ (sing p))
  by_cases lpos : L.Nonempty
  · have lsize : L.card=1 := by have := Finset.card_pos.mpr lpos; omega
    have tight : D.gates.length+m ≤ (S d).card+k-1 +
        (∑ i ∈ Finset.univ.erase d, weight i)+coldSet.card+1 := by omega
    obtain ⟨count,weights,role⟩ := projection_gate_count_tight S d D z coldSet (by omega)
      hpair zrange (zOn _ zero) zsupport cv znot sign ((S d).card+k-1) (by omega)
        weight (fun i _ => fund i) tight
    refine ⟨dormant D (S d),L,by omega,lsmall,?_,?_,?_,?_⟩
    · intro i dis big
      by_cases small : (S i).card≤k
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis,big,small⟩)
      · exact Or.inl (by omega)
    · intro i ne met
      have h := weights i ne
      rw [show weight i=min y.card (S i).card by simp [weight,met,k]] at h
      omega
    · intro w wr wa wv wz
      exact role w wr (by simp [coldSet,wa,wv]) wz
    · rw [dormant_singleton_filter_empty,Finset.card_empty,Nat.zero_add]
      exact lsmall
  · have lempty := Finset.not_nonempty_iff_eq_empty.mp lpos
    obtain ⟨Q,J,num,jc,weights,role,singletons⟩ := projection_gate_count_one_slack_singletons S d D z coldSet (by omega)
      hpair zrange (zOn _ zero) zsupport cv znot sign ((S d).card+k-1) (by omega)
        weight (fun i _ => fund i) (by omega)
    refine ⟨Q,J,num,jc,?_,fun i ne met => by simpa [weight,met] using (weights i ne).le,?_,singletons⟩
    · intro i dis big
      left
      by_contra! smaller
      have ine : i∈L := Finset.mem_filter.mpr ⟨Finset.mem_univ _,dis,big,smaller⟩
      simpa [lempty] using ine
    · intro w wr wa wv wz
      exact role w wr (by simp [coldSet,wa,wv]) wz

end PEqualNP.Outside.L_meta_997.Light
namespace PEqualNP.Outside.L_meta_997.Light
open PEqualNP.CircuitLowerBounds

theorem projected_singleton_gate_count {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C D : Circuit) (z v : ℕ) (A Q : Finset ℕ) (slackRows : ℕ)
    (sz : D.size=C.size)
    (same : ∀ w, w≠v → support (n:=n) D w=support C w)
    (guard : ∀ w∈A, support (n:=n) C w=∅)
    (switch : (support (n:=n) C z).card≠1)
    (classify : ∀ w∈Finset.Ico n (n+D.size), w∉A → w≠v → w≠z →
      (∃ i, w∈assigned D (S i)) ∨ w∈Q)
    (quota : (Q.filter (fun w => (support (n:=n) D w).card=1)).card+slackRows≤1) :
    ((Finset.Ico n (n+C.size)).filter (fun w => (support (n:=n) C w).card=1)).card+slackRows ≤
      1+(if (support (n:=n) C v).card=1 then 1 else 0) := by
  classical
  let E := (Finset.Ico n (n+C.size)).filter (fun w => (support (n:=n) C w).card=1)
  let T := Q.filter (fun w => (support (n:=n) D w).card=1)
  have covered (w) (hw : w∈E) (nv : w≠v) : w∈T := by
    obtain ⟨wr,wc⟩ := Finset.mem_filter.mp hw
    have wd : w∈Finset.Ico n (n+D.size) := by rwa [sz]
    have na : w∉A := by
      intro wa
      rw [guard w wa] at wc
      simp at wc
    have nz : w≠z := fun e => switch (e ▸ wc)
    have q := (classify w wd na nv nz).resolve_left (by
      rintro ⟨i,wi⟩
      have big := (Finset.mem_filter.mp wi).2.2
      rw [same w nv,wc] at big
      omega)
    exact Finset.mem_filter.mpr ⟨q,by rwa [same w nv]⟩
  change T.card+slackRows≤1 at quota
  change E.card+slackRows≤_
  by_cases vS : (support (n:=n) C v).card=1
  · rw [if_pos vS]
    have sub : E⊆insert v T := by
      intro w hw
      by_cases e : w=v
      · exact Finset.mem_insert.mpr (Or.inl e)
      · exact Finset.mem_insert.mpr (Or.inr (covered w hw e))
    have cap := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
    omega
  · rw [if_neg vS,Nat.add_zero]
    have sub : E⊆T := fun w hw => covered w hw (fun e => vS (e ▸ (Finset.mem_filter.mp hw).2))
    have cap := Finset.card_le_card sub
    omega

end PEqualNP.Outside.L_meta_997.Light
namespace PEqualNP.Outside.L_meta_997.Small

-- Every regular OR row charged to an exterior cold singleton also
-- determines a pair with y. A cold singleton in y instead loses its own
-- point from the pool of possible OR partners.
theorem regular_or_partner_packing {n m : ℕ} (S : Fin m → Finset (Fin n))
    (E : Finset (Fin m)) (y : Finset (Fin n)) (H G : Finset ℕ) (σ : ℕ → Finset (Fin n))
    (touch : ∀ i∈E, ¬Disjoint (S i) y)
    (linear : ∀ i j, i ≠ j → (S i ∩ S j).card≤1)
    (roles : ∀ i∈E, ∃ u∈G, ∃ p : Fin n, σ u={p} ∧ p∈S i ∧
      ∃ s∈S i, s≠p ∧ (s∈y ∨ ∃ v∈H, σ v={s})) :
    E.card ≤ G.card * max y.card (y.card+H.card-1) := by
  classical
  have ex (i : E) := roles i.val i.property
  choose u hu p sp hp s hs sn st using ex
  let Y := y ∪ singletonPoints H σ
  let F (v : ℕ) := E.attach.filter (fun i => u i=v)
  have cover : G.biUnion F = E.attach := by
    ext i
    simp only [Finset.mem_biUnion,F,Finset.mem_filter,Finset.mem_attach,true_and,iff_true]
    exact ⟨u i,hu i,rfl⟩
  have yBound : Y.card≤y.card+H.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_left (singleton_points_card H σ) _)
  have pairBound (v : ℕ) (p₀ : Fin n) (L : Finset (Fin n)) (sig : σ v={p₀})
      (rep : ∀ i∈F v, ∃ a∈L, a≠p₀ ∧ a∈S i.val) : (F v).card≤L.card := by
    have exist (i : F v) := rep i.val i.property
    choose q hq qne qmem using exist
    let e : F v → L := fun i => ⟨q i,hq i⟩
    have injective : Function.Injective e := by
      intro i j idem
      by_contra distinct
      have different : i.val.val≠j.val.val := fun eq => distinct (Subtype.ext (Subtype.ext eq))
      have label (k : F v) : p k.val=p₀ := by
        have uk := (Finset.mem_filter.mp k.property).2
        have sk : ({p k.val} : Finset (Fin n))={p₀} :=
          (sp k.val).symm.trans ((congrArg σ uk).trans sig)
        simpa using sk
      have qi : q i=q j := congrArg Subtype.val idem
      have two : ({q i,p₀} : Finset (Fin n)) ⊆ S i.val.val ∩ S j.val.val := by
        intro r hr
        simp only [Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨qmem i,qi.symm ▸ qmem j⟩
        · exact Finset.mem_inter.mpr ⟨label i ▸ hp i.val,label j ▸ hp j.val⟩
      have count := (Finset.card_le_card two).trans (linear _ _ different)
      rw [Finset.card_pair (qne i)] at count
      omega
    simpa using Fintype.card_le_of_injective e injective
  have each (v : ℕ) (_ : v∈G) : (F v).card≤max y.card (y.card+H.card-1) := by
    by_cases empty : (F v).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.mp empty,Finset.card_empty]
      exact Nat.zero_le _
    obtain ⟨i0,hi0⟩ := empty
    have sig : σ v={p i0} := ((congrArg σ (Finset.mem_filter.mp hi0).2).symm.trans (sp i0))
    have label (i) (hi : i∈F v) : p i=p i0 := by
      have r := (sp i).symm.trans ((congrArg σ (Finset.mem_filter.mp hi).2).trans sig)
      simpa using r
    by_cases hy : p i0∈y
    · have k : p i0∈Y := Finset.mem_union.mpr (Or.inl hy)
      have size := pairBound v (p i0) (Y.erase (p i0)) sig (by
        intro i hi
        have ne : s i≠p i0 := fun eq => sn i (eq.trans (label i hi).symm)
        have inY : s i∈Y := Finset.mem_union.mpr ((st i).imp_right (fun h =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
        exact ⟨s i,Finset.mem_erase.mpr ⟨ne,inY⟩,ne,hs i⟩)
      rw [Finset.card_erase_of_mem k] at size
      omega
    · have size := pairBound v (p i0) y sig (by
        intro i hi
        obtain ⟨q,qs,qy⟩ := Finset.not_disjoint_iff.mp (touch i.val i.property)
        exact ⟨q,qy,fun e => hy (e ▸ qy),qs⟩)
      omega
  have h := Finset.card_biUnion_le_card_mul G F _ each
  rw [cover,Finset.card_attach] at h
  exact h

end PEqualNP.Outside.L_meta_997.Small
namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Light PEqualNP.Outside.L_meta_997_aux

lemma crossing_or_output_partner {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (i : Fin m) (y : Finset (Fin n)) (t w o : ℕ) (F : Finset ℕ) (p r : Fin n)
    (hg : hasAllowedGates C)
    (hu : onlyNegAt C t)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ q ∈ S i, x q = true))
    (htouch : ¬Disjoint (S i) y) (hthree : (S i).card = 3)
    (hw_before : n+t < w ∧ w < o)
    (hassigned : assigned C (S i) = {w,o})
    (hsw : support C w = {p,r}) (hpr : p ≠ r)
    (hw_cold : value C (fun q => decide (q ∈ y)) w = false)
    (hroles : ∀ v ∈ Finset.Ico n (n+C.size),
      (support (n:=n) C v).card=1 → v∈F)
    (notAnd : ¬andAt C n o) :
    (∃ s ∈ S i, s ≠ p ∧ (s ∈ y ∨ ∃ v ∈ F, support C v = {s} ∧
      value C (fun q => decide (q ∈ y)) v = true)) := by
  classical
  have hso : support C o = S i := by ext q; rw [mem_support,hout]; simp
  have hww : w ∈ assigned C (S i) := hassigned.symm ▸ Finset.mem_insert_self _ _
  have hws : support C w ⊆ S i := (Finset.mem_filter.mp hww).2.1
  have hp : p ∈ S i := hws (hsw.symm ▸ Finset.mem_insert_self _ _)
  have hr : r ∈ S i := hws (hsw.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  obtain ⟨q,hqi,hqy⟩ := Finset.not_disjoint_iff.mp htouch
  let χ : Fin n → Bool := fun q => decide (q ∈ y)
  have hot : value C χ o = true := by
    rw [hout]; exact decide_eq_true ⟨q,hqi,decide_eq_true hqy⟩
  obtain ⟨hon,horange⟩ := support_gate C o (by rw [hso,hthree]; decide)
  have hidx : o-n < C.gates.length := by change o<n+C.gates.length at horange; omega
  let g := C.gates[o-n]
  obtain ⟨hop,hlen⟩ := hg g (List.getElem_mem _)
  let read (x : Fin n → Bool) (v : ℕ) := if v < o then value C x v else false
  have eqv (x : Fin n → Bool) : value C x o = g.op.eval (g.inputs.map (read x)) :=
    gate_value C x o hon horange
  have to_w (v : ℕ) (less : v < o) (sub : support C v ⊆ S i)
      (large : 2 ≤ (support (n:=n) C v).card) : v = w := by
    have ass : v ∈ assigned C (S i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C v large),sub,large⟩
    rw [hassigned] at ass
    simpa [show v ≠ o by omega] using ass
  rcases hop with hand | hor | hnot
  · exact (notAnd (by simp [andAt,g,hidx,hand])).elim
  · have hany (x : Fin n → Bool) : value C x o = true ↔ ∃ v ∈ g.inputs, read x v = true := by
      rw [eqv x,hor]; simp [GateOp.eval]
    let P := g.inputs.toFinset.filter (· < o)
    have Pbound : P.card ≤ 2 := (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen)
    have Pmem {v} : v ∈ P ↔ v ∈ g.inputs ∧ v < o := by simp [P]
    have support_parent {v} (hv : v ∈ P) : support C v ⊆ S i := by
      intro a ha
      have data := Pmem.mp hv
      rw [←hso,mem_support,hany]
      exact ⟨v,data.1, by simpa [read,data.2] using (mem_support C v a).mp ha⟩
    have covered (a) (ha : a ∈ S i) : ∃ v ∈ P, a ∈ support C v := by
      obtain ⟨v,hv,honv⟩ := (hany _).mp ((mem_support C o a).mp (hso.symm ▸ ha))
      have vo : v<o := by by_contra h; simp [read,h] at honv
      exact ⟨v,Pmem.mpr ⟨hv,vo⟩,(mem_support _ _ _).mpr (by simpa [read,vo] using honv)⟩
    have sc : ({p,r} : Finset (Fin n)).card < (S i).card := by rw [Finset.card_pair hpr,hthree]; decide
    obtain ⟨s,hsi,hsout⟩ := Finset.exists_mem_notMem_of_card_lt_card sc
    have hsp : s ≠ p := fun e => hsout (e ▸ Finset.mem_insert_self _ _)
    have hsr : s ≠ r := fun e => hsout (e ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    obtain ⟨v,hv,hsv⟩ := covered s hsi
    have hvw : v ≠ w := by intro e; exact hsout (hsw ▸ e ▸ hsv)
    have vlt := (Pmem.mp hv).2
    have vsmall : (support (n:=n) C v).card ≤ 1 := by
      by_contra! big; exact hvw (to_w v vlt (support_parent hv) (by omega))
    have vraw : support C v = {s} :=
      Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hsv) (by simpa using vsmall) |>.symm
    obtain ⟨vp,hvp,hpvp⟩ := covered p hp
    obtain ⟨vr,hvr,hrvr⟩ := covered r hr
    have hpn : vp ≠ v := by
      intro e; rw [e,vraw] at hpvp
      exact hsp (Finset.mem_singleton.mp hpvp).symm
    have hrn : vr ≠ v := by
      intro e; rw [e,vraw] at hrvr
      exact hsr (Finset.mem_singleton.mp hrvr).symm
    have hvpr : vp = vr := by
      by_contra h
      have sub : ({vp,vr,v} : Finset ℕ) ⊆ P := by
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl|rfl
        exacts [hvp,hvr,hv]
      have hc := Finset.card_le_card sub
      rw [Finset.card_triple_eq_three_iff.mpr ⟨h,hpn,hrn⟩] at hc
      omega
    have hbig : 2 ≤ (support (n:=n) C vp).card := by
      have sub : ({p,r} : Finset (Fin n)) ⊆ support C vp := by
        intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl
        exacts [hpvp,hvpr.symm ▸ hrvr]
      simpa [Finset.card_pair hpr] using Finset.card_le_card sub
    have vpw := to_w vp (Pmem.mp hvp).2 (support_parent hvp) hbig
    have hwm : w ∈ P := vpw ▸ hvp
    have pair : P = {w,v} := by
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro a ha
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha
        rcases ha with rfl|rfl
        exacts [hwm,hv]
      · simpa [Finset.card_pair hvw.symm] using Pbound
    obtain ⟨a,ha,hya⟩ := (hany χ).mp hot
    have ha_lt : a < o := by by_contra h; simp [read,h] at hya
    have ha_support : a ∈ P := Pmem.mpr ⟨ha,ha_lt⟩
    rw [pair] at ha_support
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha_support
    have hya' : value C χ a = true := by simpa [read,ha_lt] using hya
    rcases ha_support with e|e
    · exact Bool.noConfusion (hw_cold.symm.trans (e ▸ hya'))
    · rw [e] at hya'
      refine ⟨s,hsi,hsp,?_⟩
      by_cases hf : v ∈ F
      · exact Or.inr ⟨v,hf,vraw,hya'⟩
      · have vinput : v < n := by
          by_contra! hlo
          have vrange : v ∈ Finset.Ico n (n+C.size) :=
            Finset.mem_Ico.mpr ⟨hlo,vlt.trans horange⟩
          exact hf (hroles v vrange (by rw [vraw,Finset.card_singleton]))
        let a : Fin n := ⟨v,vinput⟩
        have on : value C (fun z : Fin n => decide (z = s)) a = true := (mem_support C v s).mp hsv
        rw [input_value] at on
        have vi : v = (s : ℕ) := congrArg Fin.val (of_decide_eq_true on)
        rw [vi,input_value] at hya'
        exact Or.inl (of_decide_eq_true hya')
  · have e := hu ⟨o-n,hidx⟩ hnot
    change o-n=t at e
    omega

end PEqualNP.Outside.L_meta_997.Small
namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Light PEqualNP.Outside.L_meta_997_aux

-- A regular crossing OR needs a cold singleton and a different hot point.
theorem crossing_triples_singleton_set_cap {n m : ℕ} (S : Fin m → Finset (Fin n)) (C D : Circuit)
    (f : ℕ → ℕ) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (E : Finset (Fin m)) (F : Finset ℕ)
    (hlin : rowLinearity S) (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (hout : rowOutputs C S o) (gd : good D)
    (agreement : ∀ x : Fin n → Bool, (Finset.univ.filter (fun p => x p=true)).card≤2 →
      ∀ w, value D x (f w)=value C x w)
    (onlySingleton : ∀ u∈Finset.Ico n (n+C.size), (support (n:=n) C u).card=1 → u∈F)
    (triples : ∀ i ∈ E, ¬ Disjoint (S i) y ∧ (S i).card=3 ∧ ∃ w j,
      n+t<w ∧ w<o i ∧ assigned C (S i)={w,o i} ∧ Disjoint y (S j) ∧
      w ∈ highOrGates C y (S j) ∧ (support C w \ S j).Nonempty) :
    let H := F.filter (fun w => value C (fun p => decide (p∈y)) w=true)
    let G := F.filter (fun w => ¬value C (fun p => decide (p∈y)) w=true)
    E.card ≤ G.card*max y.card (y.card+H.card-1) := by
  classical
  let H := F.filter (fun w => value C (fun p => decide (p∈y)) w=true)
  let G := F.filter (fun w => ¬value C (fun p => decide (p∈y)) w=true)
  change E.card ≤ G.card*max y.card (y.card+H.card-1)
  apply regular_or_partner_packing S E y H G (support C) (fun i hi => (triples i hi).1) hlin
  intro i hi
  obtain ⟨met,three,w,j,after,earlier,paid,_,high,lost⟩ := triples i hi
  obtain ⟨u,_,p,r,uf,_,distinct,sig,_,_,cold,_,row,_,_⟩ :=
    crossing_parent_signatures_from_support S C (o i) t w y i j F onlySingleton hg hu
      after earlier paid high lost
  have wown : w ∈ assigned C (S i) := by simp [paid]
  have pi : p∈S i := (Finset.mem_filter.mp wown).2.1 (row.symm ▸ Finset.mem_insert_self _ _)
  have hot : value C (fun q => decide (q∈y)) (o i)=true := by
    obtain ⟨q,qi,qy⟩ := Finset.not_disjoint_iff.mp met
    rw [hout]
    exact decide_eq_true ⟨q,qi,decide_eq_true qy⟩
  have wCold := (Finset.mem_filter.mp (Finset.mem_filter.mp high).1).2.2.2
  have no := two_assigned_hot_output_not_and C D f (S i) w (o i)
    (fun q => decide (q∈y)) (by rw [three]; decide) hg gd agreement (hout i) paid wCold hot
  obtain ⟨s,si,different,partner⟩ := crossing_or_output_partner C S i y t w (o i) F p r hg hu
    (hout i) met three ⟨after,earlier⟩ paid row distinct wCold onlySingleton no
  refine ⟨u,Finset.mem_filter.mpr ⟨uf,by simp [cold]⟩,p,sig,pi,s,si,different,?_⟩
  exact partner.imp_right (fun ⟨v,vf,vs,vhot⟩ => ⟨v,Finset.mem_filter.mpr ⟨vf,vhot⟩,vs⟩)

end PEqualNP.Outside.L_meta_997.Small
namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Light PEqualNP.Outside.L_meta_997_aux

-- One spare projection slot can permit a singleton wire or a row surplus.
-- A singleton reader is itself too small to own a row credit.
open Classical in
theorem three_near_folded_projection {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (d : Fin m) (hk : y.card=3)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card≤1)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t) (ho : computesRows C S o)
    (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p∈y)) (n+t)=false)
    (large : ∀ i, Disjoint (S i) y → 5≤(S i).card → (assigned C (S i)).card+1<(S i).card)
    (profile : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
      d∈B ∧ 3≤B.card ∧ (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+5) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length+(refunds S C y).card+m := by
  classical
  by_contra bad
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
  obtain ⟨hd,three,hquota⟩ : d∈B ∧ 3≤B.card ∧
      (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+5 := profile
  have dat (i) (hi : i∈B) := (Finset.mem_filter.mp hi).2
  have quote : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ y.card+2≤(S i).card)
    (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+2 := by
    rw [hk]
    change (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+3+2
    omega
  obtain ⟨a,ta,rd⟩ := switch_has_reader C (S d) (o d) t (by omega : 2≤y.card)
    hg hu (ho d) hl (dat d hd).2.1
  let v := n+a.val
  have av : n+t<v := by dsimp [v]; omega
  have ar : v<n+C.size := Nat.add_lt_add_left a.isLt n
  obtain ⟨D,f,gD,sameSize,dead,unchanged,agree,_,_⟩ := fold_one_reader_stable C t a ta rd hg hu hl
  obtain ⟨A,ac,range,aRoles⟩ := guard_hot_gates C t y (by omega : 0<y.card) hg hu hl hy
  have large' (i) (di : Disjoint (S i) y) (big : y.card+2≤(S i).card) :=
    large i di (by omega : 5≤(S i).card)
  obtain ⟨Q,J,_,_,_,weights,classify,singletonQ⟩ :=
    folded_model_one_slack_singletons S d C o t y (by omega) hlin hg hu ho hl (dat d hd).2.1
      large' quote bad D f v gD sameSize av ar dead unchanged agree A ac range
      (fun w hw => (aRoles w hw).1)
  have sing (p : Fin n) :
      (Finset.univ.filter (fun q : Fin n => decide (q=p)=true)).card<y.card := by
    have e : (Finset.univ.filter (fun q : Fin n => decide (q=p)=true))={p} := by ext q; simp
    rw [e,Finset.card_singleton,hk]
    decide
  have same (w) (nw : w≠v) : support (n:=n) D w=support C w := by
    ext p
    rw [mem_support,mem_support,←unchanged w nw,agree _ (sing p) w,unchanged w nw]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,v,dead]
  have assigns (i) : (assigned C (S i)).erase v = assigned D (S i) := by
    ext w
    by_cases eq : w=v
    · subst w
      simp [assigned,empty]
    · rw [Finset.mem_erase,assigned,assigned,Finset.mem_filter,Finset.mem_filter,same w eq,sameSize]
      simp [eq]
  let R := Finset.univ.filter (fun i => v∈assigned C (S i))
  have once : R.card≤1 := by
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    by_contra ne
    obtain ⟨_,si,bi⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hi).2
    obtain ⟨_,sj,_⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hj).2
    have sub : support C v ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨si hp,sj hp⟩
    have cp := (Finset.card_le_card sub).trans (hlin i j ne)
    omega
  have extra (i) : touchingCredit C t y (S i) ≤ (if i∈J then 1 else 0)+(if i∈R then 1 else 0) := by
    by_cases met : Disjoint (S i) y
    · simp [touchingCredit,met]
    have ne : i≠d := fun e => met (e.symm ▸ (dat d hd).1)
    have assignedDown := weights i ne
    have le := Finset.card_erase_le (s:=assigned C (S i)) (a:=n+t)
    have cs : (assigned C (S i)).card ≤ (assigned D (S i)).card + (if i∈R then 1 else 0) := by
      by_cases h : v∈assigned C (S i)
      · have hR : i∈R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
        have e := Finset.card_erase_add_one h
        rw [assigns i] at e
        simp only [if_pos hR]
        omega
      · have hR : i∉R := fun eq => h (Finset.mem_filter.mp eq).2
        have e := assigns i
        rw [Finset.erase_eq_of_notMem h] at e
        simp [hR,e]
    simp only [touchingCredit,met,ite_false]
    omega
  have credits : (∑ i, touchingCredit C t y (S i))≤J.card+R.card := by
    have r := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin m))) (fun i _ => extra i)
    simpa [Finset.sum_add_distrib,Finset.sum_boole] using r
  have n5 : 5≤n := ((dat d hd).2.2).trans (by simpa using Finset.card_le_univ (S d))
  have zFull : support (n:=n) C (n+t)=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    exact (mem_support _ _ _).mpr (hl _ (sing p))
  have zNotSingleton : (support (n:=n) C (n+t)).card≠1 := by
    rw [zFull]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  let F := (Finset.Ico n (n+C.size)).filter (fun w => (support (n:=n) C w).card=1)
  have single : F.card+J.card ≤ 1+(if (support (n:=n) C v).card=1 then 1 else 0) :=
    projected_singleton_gate_count S C D (n+t) v A Q J.card sameSize same
      (fun w hw => (aRoles w hw).1) zNotSingleton (by
        intro w wr na nv nz
        exact (classify w wr na nv nz).imp_left (fun ⟨i,_,wi⟩ => ⟨i,wi⟩)) singletonQ
  have F2 : F.card≤2 := by split at single <;> omega
  have r := disjoint_outputs_refunded S C o y B hlin ho (fun i hi =>
    ⟨(dat i hi).1,by have b := (dat i hi).2.2; omega⟩)
  obtain ⟨E,lb,triples⟩ := regular_crossing_triples S C o t y hk hlin hg hu ho hl hy bad
  have hout : rowOutputs C S o := fun i x => ho i x
  have pack := crossing_triples_singleton_set_cap S C D f o t y E F hlin hg hu hout gD
    (fun x hx w => agree x (by omega) w) (fun w wr wc => Finset.mem_filter.mpr ⟨wr,wc⟩)
    (by
      intro i hi
      obtain ⟨meet,sz,w,j,a,b,c,d,e,f,_⟩ := triples i hi
      exact ⟨meet,sz,w,j,a,b,c,d,e,f⟩)
  let H := F.filter (fun w => value C (fun p => decide (p∈y)) w=true)
  let G := F.filter (fun w => ¬ value C (fun p => decide (p∈y)) w=true)
  change E.card ≤ G.card*max y.card (y.card+H.card-1) at pack
  have sep : H.card+G.card=F.card := Finset.card_filter_add_card_filter_not _
  rw [hk] at pack
  have numeric (h g : ℕ) (cap : h+g≤2) : g*max 3 (3+h-1)≤3*(h+g) := by
    have h2 : h≤2 := by omega
    interval_cases h <;> norm_num <;> omega
  have upper := pack.trans (numeric H.card G.card (by omega))
  have lower : B.card+4≤E.card+J.card+R.card := by omega
  by_cases vS : (support (n:=n) C v).card=1
  · have noR : R.card=0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have b := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2.2
      rw [vS] at b
      omega
    rw [if_pos vS] at single
    omega
  · rw [if_neg vS] at single
    omega

end PEqualNP.Outside.L_meta_997.Small
namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Light PEqualNP.Outside.L_meta_997_aux

-- One spare projection slot can permit a singleton wire or a row surplus.
-- A singleton reader is itself too small to own a row credit.
open Classical in
theorem three_near_folded_projection_paid {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (d : Fin m) (hk : y.card=3)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card≤1)
    (hg : hasAllowedGates C) (hu : onlyNegAt C t) (ho : computesRows C S o)
    (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p∈y)) (n+t)=false)
    (profile : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
      d∈B ∧ 3≤B.card ∧ (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+5) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length+(refunds S C y).card+m := by
  classical
  by_contra bad
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ 5≤(S i).card)
  obtain ⟨hd,three,hquota⟩ : d∈B ∧ 3≤B.card ∧
      (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+5 := profile
  have dat (i) (hi : i∈B) := (Finset.mem_filter.mp hi).2
  have quote : let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card+1<(S i).card ∧ y.card+2≤(S i).card)
    (∑ i ∈ B, (S i).card) ≤ (y.card+1)*B.card+(S d).card+y.card+2 := by
    rw [hk]
    change (∑ i ∈ B, (S i).card) ≤ 4*B.card+(S d).card+3+2
    omega
  obtain ⟨a,ta,rd⟩ := switch_has_reader C (S d) (o d) t (by omega : 2≤y.card)
    hg hu (ho d) hl (dat d hd).2.1
  let v := n+a.val
  have av : n+t<v := by dsimp [v]; omega
  have ar : v<n+C.size := Nat.add_lt_add_left a.isLt n
  obtain ⟨D,f,gD,sameSize,dead,unchanged,agree,_,_⟩ := fold_one_reader_stable C t a ta rd hg hu hl
  obtain ⟨A,ac,range,aRoles⟩ := guard_hot_gates C t y (by omega : 0<y.card) hg hu hl hy
  obtain ⟨Q,J,_,_,_,weights,classify,singletonQ⟩ :=
    folded_model_one_slack_paid S d C o t y (by omega) hlin hg hu ho hl (dat d hd).2.1
      quote bad D f v gD sameSize av ar dead unchanged agree A ac range
      (fun w hw => (aRoles w hw).1)
  have sing (p : Fin n) :
      (Finset.univ.filter (fun q : Fin n => decide (q=p)=true)).card<y.card := by
    have e : (Finset.univ.filter (fun q : Fin n => decide (q=p)=true))={p} := by ext q; simp
    rw [e,Finset.card_singleton,hk]
    decide
  have same (w) (nw : w≠v) : support (n:=n) D w=support C w := by
    ext p
    rw [mem_support,mem_support,←unchanged w nw,agree _ (sing p) w,unchanged w nw]
  have empty : support (n:=n) D v=∅ := by ext p; simp [mem_support,v,dead]
  have assigns (i) : (assigned C (S i)).erase v = assigned D (S i) := by
    ext w
    by_cases eq : w=v
    · subst w
      simp [assigned,empty]
    · rw [Finset.mem_erase,assigned,assigned,Finset.mem_filter,Finset.mem_filter,same w eq,sameSize]
      simp [eq]
  let R := Finset.univ.filter (fun i => v∈assigned C (S i))
  have once : R.card≤1 := by
    apply Finset.card_le_one_iff.mpr
    intro i j hi hj
    by_contra ne
    obtain ⟨_,si,bi⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hi).2
    obtain ⟨_,sj,_⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hj).2
    have sub : support C v ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨si hp,sj hp⟩
    have cp := (Finset.card_le_card sub).trans (hlin i j ne)
    omega
  have extra (i) : touchingCredit C t y (S i) ≤ (if i∈J then 1 else 0)+(if i∈R then 1 else 0) := by
    by_cases met : Disjoint (S i) y
    · simp [touchingCredit,met]
    have ne : i≠d := fun e => met (e.symm ▸ (dat d hd).1)
    have assignedDown := weights i ne met
    have le := Finset.card_erase_le (s:=assigned C (S i)) (a:=n+t)
    have cs : (assigned C (S i)).card ≤ (assigned D (S i)).card + (if i∈R then 1 else 0) := by
      by_cases h : v∈assigned C (S i)
      · have hR : i∈R := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
        have e := Finset.card_erase_add_one h
        rw [assigns i] at e
        simp only [if_pos hR]
        omega
      · have hR : i∉R := fun eq => h (Finset.mem_filter.mp eq).2
        have e := assigns i
        rw [Finset.erase_eq_of_notMem h] at e
        simp [hR,e]
    simp only [touchingCredit,met,ite_false]
    omega
  have credits : (∑ i, touchingCredit C t y (S i))≤J.card+R.card := by
    have r := Finset.sum_le_sum (s:=(Finset.univ : Finset (Fin m))) (fun i _ => extra i)
    simpa [Finset.sum_add_distrib,Finset.sum_boole] using r
  have n5 : 5≤n := ((dat d hd).2.2).trans (by simpa using Finset.card_le_univ (S d))
  have zFull : support (n:=n) C (n+t)=Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro p
    exact (mem_support _ _ _).mpr (hl _ (sing p))
  have zNotSingleton : (support (n:=n) C (n+t)).card≠1 := by
    rw [zFull]
    simp only [Finset.card_univ,Fintype.card_fin]
    omega
  let F := (Finset.Ico n (n+C.size)).filter (fun w => (support (n:=n) C w).card=1)
  have single : F.card+J.card ≤ 1+(if (support (n:=n) C v).card=1 then 1 else 0) :=
    projected_singleton_gate_count S C D (n+t) v A Q J.card sameSize same
      (fun w hw => (aRoles w hw).1) zNotSingleton (by
        intro w wr na nv nz
        exact (classify w wr na nv nz).imp_left (fun ⟨i,_,wi⟩ => ⟨i,wi⟩)) singletonQ
  have F2 : F.card≤2 := by split at single <;> omega
  have r := disjoint_outputs_refunded S C o y B hlin ho (fun i hi =>
    ⟨(dat i hi).1,by have b := (dat i hi).2.2; omega⟩)
  obtain ⟨E,lb,triples⟩ := regular_crossing_triples S C o t y hk hlin hg hu ho hl hy bad
  have hout : rowOutputs C S o := fun i x => ho i x
  have pack := crossing_triples_singleton_set_cap S C D f o t y E F hlin hg hu hout gD
    (fun x hx w => agree x (by omega) w) (fun w wr wc => Finset.mem_filter.mpr ⟨wr,wc⟩)
    (by
      intro i hi
      obtain ⟨meet,sz,w,j,a,b,c,d,e,f,_⟩ := triples i hi
      exact ⟨meet,sz,w,j,a,b,c,d,e,f⟩)
  let H := F.filter (fun w => value C (fun p => decide (p∈y)) w=true)
  let G := F.filter (fun w => ¬ value C (fun p => decide (p∈y)) w=true)
  change E.card ≤ G.card*max y.card (y.card+H.card-1) at pack
  have sep : H.card+G.card=F.card := Finset.card_filter_add_card_filter_not _
  rw [hk] at pack
  have numeric (h g : ℕ) (cap : h+g≤2) : g*max 3 (3+h-1)≤3*(h+g) := by
    have h2 : h≤2 := by omega
    interval_cases h <;> norm_num <;> omega
  have upper := pack.trans (numeric H.card G.card (by omega))
  have lower : B.card+4≤E.card+J.card+R.card := by omega
  by_cases vS : (support (n:=n) C v).card=1
  · have noR : R.card=0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have b := (Finset.mem_filter.mp (Finset.mem_filter.mp hi).2).2.2
      rw [vS] at b
      omega
    rw [if_pos vS] at single
    omega
  · rw [if_neg vS] at single
    omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Light PEqualNP.Outside.L_meta_997_aux

theorem twenty_six_near_residual {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hn : n ≤ 26)
    (hlin : rowLinearity S) (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m)) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card + 1 < (S i).card ∧ 5 ≤ (S i).card)
    let M := ∑ i ∈ B, (S i).card
    n = 26 ∧ y.card = 3 ∧
    ((B.card = 5 ∧ M = 33) ∨ (B.card = 6 ∧ M = 38) ∨ (B.card = 7 ∧ M = 44)) ∧
    (∀ i ∈ B, 4 * B.card + (S i).card + 5 < M) ∧
    (M = 23 + B.card.choose 2 → B.biUnion S = Finset.univ \ y) := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card + 1 < (S i).card ∧ 5 ≤ (S i).card)
  let M := ∑ i ∈ B, (S i).card
  obtain ⟨n26, hk, cases, _, cover⟩ :=
    twenty_six_sharp_residual S C o t y hn hlin hg hu ho hl hy bad
  have shape : (B.card = 3 ∧ M = 26) ∨ (B.card = 4 ∧ 28 ≤ M ∧ M ≤ 29) ∨
      (B.card = 5 ∧ M = 33) ∨ (B.card = 6 ∧ M = 38) ∨ (B.card = 7 ∧ M = 44) := cases
  have three : 3 ≤ B.card := by
    rcases shape with h | h | h | h | h <;> omega
  have sharp (i) (hi : i ∈ B) : 4 * B.card + (S i).card + 5 < M := by
    by_contra! paid
    exact bad (three_near_folded_projection_paid S C o t y i hk hlin hg hu ho hl hy
      ⟨hi, three, paid⟩)
  have sum_bound (bound : ℕ) (sizes : ∀ i ∈ B, (S i).card ≤ bound) :
      M ≤ B.card * bound := by
    simpa only [Finset.sum_const, smul_eq_mul] using Finset.sum_le_sum (s:=B) sizes
  refine ⟨n26, hk, ?_, sharp, cover⟩
  rcases shape with ⟨card, mass⟩ | ⟨card, lower, upper⟩ | rest
  · exfalso
    have charge := sum_bound 8 (fun i hi => by have := sharp i hi; omega)
    rw [card] at charge
    omega
  · exfalso
    have charge := sum_bound 7 (fun i hi => by have := sharp i hi; omega)
    rw [card] at charge
    have mass : M = 28 := by omega
    have charge' := sum_bound 6 (fun i hi => by have := sharp i hi; omega)
    rw [card] at charge'
    omega
  · exact rest

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small

theorem covered_membership_saturated {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset α) (S : α → Finset β) (T : Finset β)
    (linear : ∀ i ∈ B, (T ∩ S i).card ≤ 1)
    (saturated : (T ∩ B.biUnion S).card = B.card) :
    ∀ i ∈ B, ∃ p ∈ T ∩ S i, ∀ j ∈ B, p ∈ S j → j = i := by
  classical
  intro i hi
  have : ¬ T ∩ S i ⊆ (B.erase i).biUnion S := by
    intro noPrivate
    have skip : T ∩ B.biUnion S ⊆ T ∩ (B.erase i).biUnion S := by
      intro p hp
      obtain ⟨pT,pCover⟩ := Finset.mem_inter.mp hp
      obtain ⟨j,jB,pS⟩ := Finset.mem_biUnion.mp pCover
      exact Finset.mem_inter.mpr ⟨pT,by
        by_cases e : j=i
        · exact noPrivate (Finset.mem_inter.mpr ⟨pT,e ▸ pS⟩)
        · exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_erase.mpr ⟨e,jB⟩,pS⟩⟩
    have sc := Finset.card_le_card skip
    have cap := card_inter_biUnion_linear (B.erase i) S T
      (fun j hj => linear j (Finset.mem_of_mem_erase hj))
    rw [Finset.card_erase_of_mem hi] at cap
    have pos := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  obtain ⟨p,hp,avoid⟩ := Finset.not_subset.mp this
  refine ⟨p,hp,fun j hj pj => ?_⟩
  by_contra e
  exact avoid (Finset.mem_biUnion.mpr ⟨j,Finset.mem_erase.mpr ⟨e,hj⟩,pj⟩)



end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small

-- Equality in the union bound puts one separate point at each row pair.
-- At a fixed row, count the points covered by the other rows after erasing it.
theorem saturated_line_union_intersection {n m : ℕ} (S : Fin m → Finset (Fin n))
    (B : Finset (Fin m)) (linear : ∀ i j, i ≠ j → (S i ∩ S j).card≤1)
    (mass : (∑ i ∈ B, (S i).card)=(B.biUnion S).card+B.card.choose 2)
    {i : Fin m} (hi : i∈B) :
    (S i ∩ (B.erase i).biUnion S).card = (B.erase i).card := by
  classical
  let J := B.erase i
  have upper : (S i ∩ J.biUnion S).card ≤ J.card :=
    card_inter_biUnion_linear J S (S i) (fun j hj =>
      linear i j (Finset.mem_erase.mp hj).1.symm)
  have lower := line_union S linear J
  have split := Finset.sum_erase_add B (fun j => (S j).card) hi
  change (∑ j ∈ J, (S j).card)+(S i).card = _ at split
  have eq : S i ∪ J.biUnion S = B.biUnion S := by
    rw [←Finset.biUnion_insert,show insert i J=B from Finset.insert_erase hi]
  have inter := Finset.card_union_add_card_inter (S i) (J.biUnion S)
  rw [eq] at inter
  have card : B.card = J.card+1 := by
    dsimp [J]
    have e := Finset.card_erase_of_mem hi
    have p := Finset.card_pos.mpr ⟨i,hi⟩
    omega
  rw [card,Nat.choose_succ_succ,Nat.choose_one_right] at mass
  change (∑ j ∈ B, (S j).card) = (B.biUnion S).card + (J.card + J.card.choose 2) at mass
  change (S i ∩ J.biUnion S).card=J.card
  omega

theorem saturated_line_union_junctions {n m : ℕ} (S : Fin m → Finset (Fin n))
    (B : Finset (Fin m)) (linear : ∀ i j, i ≠ j → (S i ∩ S j).card≤1)
    (mass : (∑ i ∈ B, (S i).card)=(B.biUnion S).card+B.card.choose 2) :
    (∀ i ∈ B, (S i \ (B.erase i).biUnion S).card = (S i).card-(B.card-1)) ∧
    (∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∃ p ∈ S i ∩ S j,
      ∀ k ∈ B, p ∈ S k → k=i ∨ k=j) := by
  classical
  refine ⟨fun i hi => ?_,fun i hi j hj ne => ?_⟩
  · have hit := saturated_line_union_intersection S B linear mass hi
    have split := Finset.card_sdiff_add_card_inter (S i) ((B.erase i).biUnion S)
    rw [hit,Finset.card_erase_of_mem hi] at split
    omega
  · obtain ⟨p,hp,only⟩ := covered_membership_saturated (B.erase i) S (S i)
      (fun j hj => linear i j (Finset.mem_erase.mp hj).1.symm)
      (saturated_line_union_intersection S B linear mass hi) j (Finset.mem_erase.mpr ⟨ne.symm,hj⟩)
    refine ⟨p,hp,fun k hk pk => ?_⟩
    by_cases eq : k=i
    · exact Or.inl eq
    · exact Or.inr (only k (Finset.mem_erase.mpr ⟨eq,hk⟩) pk)

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Light PEqualNP.Outside.L_meta_997_aux

theorem twenty_six_residual_junctions {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (hn : n ≤ 26)
    (hlin : rowLinearity S) (hg : hasAllowedGates C) (hu : onlyNegAt C t)
    (ho : computesRows C S o) (hl : switchLight (n:=n) C t y.card)
    (hy : value C (fun p => decide (p ∈ y)) (n+t) = false)
    (bad : ¬ ((∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.size + (refunds S C y).card + m)) :
    let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
      (assigned C (S i)).card + 1 < (S i).card ∧ 5 ≤ (S i).card)
    let M := ∑ i ∈ B, (S i).card
    B.biUnion S = Finset.univ \ y ∧
    (∀ i ∈ B, (S i \ (B.erase i).biUnion S).card = (S i).card - (B.card - 1)) ∧
    (∀ i ∈ B, ∀ j ∈ B, i ≠ j → ∃ p ∈ S i ∩ S j,
      ∀ k ∈ B, p ∈ S k → k = i ∨ k = j) ∧
    (∑ i ∈ B, (S i \ (B.erase i).biUnion S).card) + B.card * (B.card - 1) = M := by
  classical
  let B := Finset.univ.filter (fun i => Disjoint (S i) y ∧
    (assigned C (S i)).card + 1 < (S i).card ∧ 5 ≤ (S i).card)
  let M := ∑ i ∈ B, (S i).card
  obtain ⟨n26, hk, cases, _, covers⟩ :=
    twenty_six_near_residual S C o t y hn hlin hg hu ho hl hy bad
  have shape : (B.card = 5 ∧ M = 33) ∨ (B.card = 6 ∧ M = 38) ∨
      (B.card = 7 ∧ M = 44) := cases
  have sat : M = 23 + B.card.choose 2 := by
    rcases shape with ⟨hs, hm⟩ | ⟨hs, hm⟩ | ⟨hs, hm⟩ <;> rw [hs, hm] <;> decide
  have cover : B.biUnion S = Finset.univ \ y := covers sat
  have un : (B.biUnion S).card = 23 := by
    rw [cover, Finset.card_sdiff_of_subset (Finset.subset_univ y), Finset.card_univ,
      Fintype.card_fin]
    omega
  have mass : (∑ i ∈ B, (S i).card) = (B.biUnion S).card + B.card.choose 2 := by
    rw [un]
    exact sat
  have geometry := saturated_line_union_junctions S B hlin mass
  refine ⟨cover, geometry.1, geometry.2, ?_⟩
  have count (i : Fin m) (hi : i ∈ B) :
      (S i \ (B.erase i).biUnion S).card + (B.card - 1) = (S i).card := by
    have hit := saturated_line_union_intersection S B hlin mass hi
    have split := Finset.card_sdiff_add_card_inter (S i) ((B.erase i).biUnion S)
    rw [hit, Finset.card_erase_of_mem hi] at split
    exact split
  calc
    (∑ i ∈ B, (S i \ (B.erase i).biUnion S).card) + B.card * (B.card - 1) =
        ∑ i ∈ B, ((S i \ (B.erase i).biUnion S).card + (B.card - 1)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
    _ = M := Finset.sum_congr rfl count

end PEqualNP.Outside.L_meta_997.Small
