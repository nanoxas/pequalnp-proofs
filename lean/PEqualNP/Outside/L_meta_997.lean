import Mathlib
import PEqualNP.Defs

-- Restricted two-window lower bound for Boolean sums.
-- The final theorems give the desk inequality for at most seventeen inputs,
-- and whenever the witness has at most two points or n ≤ 4 times its size plus five.
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

lemma reserve_geometry {n m : ℕ} (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n))
    (hk : 3 ≤ Y.card) (hn : n ≤ 4*Y.card+5)
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∀ i, Disjoint (S i) Y → (S i).card ≤ Y.card+1) ∨
    ∃ d, 2 ≤ (S d).card ∧ (∑ i, if Disjoint (S i) Y then (S i).card-Y.card else 0) ≤
      ((S d).card-Y.card) + (Finset.univ.filter (fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card)).card + Y.card := by
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
  have h5 : B.card ≤ 5 := by
    by_contra! hlarge
    obtain ⟨I,hI,h6⟩ := Finset.exists_subset_card_eq (s:=B) (n:=6) (by omega)
    have hcap := price_cap S Y hlin I (fun i hi => (binfo (hI hi)).1)
    have hsum := Finset.sum_le_sum (s:=I) (fun i hi => (binfo (hI hi)).2)
    simp only [Finset.sum_const, h6, smul_eq_mul] at hsum
    rw [h6] at hcap
    norm_num [Nat.choose] at hcap
    omega
  have hp := price_cap S Y hlin B (fun i hi => (binfo hi).1)
  change k + _ ≤ _ at hp
  have hM := Finset.sum_le_sum (s:=B) (fun i hi => hm i hi)
  simp only [Finset.sum_const,smul_eq_mul] at hM
  have hpos : 0 < B.card := Finset.card_pos.mpr hne
  have key : (∑ i ∈ B, (S i).card) ≤ B.card * (k+1) + (S d).card := by
    generalize hr : B.card = r at *
    interval_cases r <;> norm_num [Nat.choose] at * <;> omega
  let b (i : Fin m) := (S i).card - (k+1)
  have splitB (i : Fin m) (hi : i ∈ B) : (S i).card = (k+1) + b i := by
    have h := (binfo hi).2
    dsimp [b]
    omega
  have heq := Finset.sum_congr (s₂:=B) rfl splitB
  rw [Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul] at heq
  have hbudget : (∑ i ∈ B, b i) ≤ (S d).card := by omega
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
  change (∑ i, if Disjoint (S i) Y then (S i).card-k else 0) ≤ ((S d).card-k)+D.card+k
  omega

end PEqualNP.Outside.L_meta_997.Small

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.Outside.L_meta_997.Light

theorem size_window : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), (y.card ≤ 2 ∨ n ≤ 4*y.card+5) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by

  classical
  intro n m S C o t y hn hlin hg hu ho hlight hy
  by_cases hk : y.card ≤ 2
  · exact PEqualNP.Outside.L_meta_997_aux.two_window_of_card_le_two C y t S o hg hu hy hlin ho hk
  rcases reserve_geometry S y (by omega) (hn.resolve_left hk) hlin with hr | ⟨d,hds,hb⟩
  · exact window_bound_one_extra S C o t y hlin hg hu ho hlight hr
  · let D := Finset.univ.filter (fun i => Disjoint (S i) y ∧ 2 ≤ (S i).card)
    have href := disjoint_outputs_refunded S C o y D hlin ho (fun i hi => (Finset.mem_filter.mp hi).2)
    apply window_bound_reserve S d C o t y (by omega) hds hlin hg hu ho hlight hy
    exact hb.trans (Nat.add_le_add_right (Nat.add_le_add_left href _) _)

theorem num_inputs_seventeen : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)), n ≤ 17 → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i : Fin C.gates.length, (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (i : ℕ) = t) → (∀ (i : Fin m) (x : Fin n → Bool), (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true)) → (∀ x : Fin n → Bool, (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card → (C.wires (List.ofFn x)).getD (n + t) false = true) → (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD (n + t) false = false → (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))).card + m := by
  intro n m S C o t y hn
  apply size_window n m S C o t y
  omega

end PEqualNP.Outside.L_meta_997.Small
