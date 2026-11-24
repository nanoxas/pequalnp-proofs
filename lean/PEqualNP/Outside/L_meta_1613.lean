import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext
import PEqualNP.Defs

-- Apache-2.0.
-- Evaluation, monotonicity, cut, and replacement helpers adapt accepted L-meta-986.
-- Light-window counts adapt accepted L-meta-270 and L-meta-782.
-- OR-only private counts refine the accepted L-meta-988 method.
-- Reader-aware charges, anchors, co-line representatives, and finite counts
-- are local extensions of those checked helpers.

namespace PEqualNP.Outside.L_meta_1613_aux

-- Component MintermSlack.
namespace MintermSlack

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

noncomputable def branches {n : ℕ} (C : Circuit) (y : Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter fun w =>
    (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and ∧
      support (n := n) C w = ∅ ∧ value C y w = true

lemma empty_true_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (y : Fin n → Bool) (w : ℕ) (hs : support (n := n) C w = ∅) (hy : value C y w = true) :
    ∃ P : Finset ℕ,
      (P.card ≤ 1 ∨ (w ∈ branches C y ∧ P.card ≤ 2)) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C y r = true) ∧
      ∀ x : Fin n → Bool, (∀ r ∈ P, value C x r = true) → value C x w = true := by
  classical
  have hn : n ≤ w := by
    by_contra! h
    let p : Fin n := ⟨w, h⟩
    have hp : p ∈ support (n := n) C w := by
      apply (mem_support C w p).mpr
      change value C (fun q => decide (q = p)) p = true
      simp [input_value]
    simp [hs] at hp
  have hw : w < n + C.size := by
    by_contra! h
    rw [missing_value C y w h] at hy
    contradiction
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem hj)
  have form (x : Fin n → Bool) : value C x w =
      g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
    gate_value C x w hn hw
  have read_true (r : ℕ) (h : (if r < w then value C y r else false) = true) :
      r < w ∧ value C y r = true := by
    by_cases hr : r < w
    · exact ⟨hr, by simpa [hr] using h⟩
    · simp [hr] at h
  rw [form] at hy
  rcases hop with hop | hop
  · have hall : ∀ r ∈ g.inputs, r < w ∧ value C y r = true := by
      intro r hr
      apply read_true
      have h := hy
      simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at h
      exact h r hr
    refine ⟨g.inputs.toFinset, Or.inr ⟨?_, (List.toFinset_card_le _).trans hlen⟩,
      ?_, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨hn, hw⟩, ?_, hs, ?_⟩
      · rw [List.getD_eq_getElem _ _ hj]
        exact hop
      · rw [form]
        exact hy
    · intro r hr
      exact (hall r (List.mem_toFinset.mp hr)).1
    · intro r hr
      exact (hall r (List.mem_toFinset.mp hr)).2
    · intro x hx
      rw [form]
      simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq]
      intro r hr
      rw [ite_eq_left (hall r hr).1]
      exact hx r (List.mem_toFinset.mpr hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hy
    obtain ⟨r, hr, hv⟩ := hy
    obtain ⟨hrw, hry⟩ := read_true r hv
    refine ⟨{r}, Or.inl (by simp), ?_, ?_, ?_⟩
    · intro a ha
      simpa using (Finset.mem_singleton.mp ha ▸ hrw)
    · intro a ha
      simpa using (Finset.mem_singleton.mp ha ▸ hry)
    · intro x hx
      rw [form]
      simp only [hop, GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq]
      exact ⟨r, hr, by simpa [hrw] using hx r (Finset.mem_singleton_self r)⟩

lemma true_frontier {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (y : Fin n → Bool) (t : ℕ) (F : Finset ℕ)
    (hFy : ∀ w ∈ F, value C y w = true)
    (hFt : ∀ w ∈ F, support (n := n) C w = ∅ → w < t) :
    ∃ B : Finset ℕ,
      (∀ w ∈ B, (support (n := n) C w).Nonempty) ∧
      B.card ≤ F.card + ((branches C y).filter (· < t)).card ∧
      ∀ x : Fin n → Bool, (∀ w ∈ B, value C x w = true) →
        ∀ w ∈ F, value C x w = true := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, ?_, by simp, fun _ h => h⟩
    intro w hw
    by_contra hn
    have hs : support (n := n) C w = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have := hFt w hw hs
    omega
  | succ t ih =>
    by_cases hex : t ∈ F ∧ support (n := n) C t = ∅
    · obtain ⟨P, hPc, hPt, hPy, hforce⟩ := empty_true_inputs C hG y t hex.2 (hFy t hex.1)
      let F' := F.erase t ∪ P
      have hF'y : ∀ w ∈ F', value C y w = true := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFy w (Finset.mem_erase.mp hw).2
        · exact hPy w hw
      have hF't : ∀ w ∈ F', support (n := n) C w = ∅ → w < t := by
        intro w hw hs
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFt w (Finset.mem_erase.mp hw).2 hs
          omega
        · exact hPt w hw
      obtain ⟨B, hB, hc, htransfer⟩ := ih F' hF'y hF't
      refine ⟨B, hB, ?_, ?_⟩
      · have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        rcases hPc with hPc | ⟨htA, hPc⟩
        · have hmono : ((branches C y).filter (· < t)).card ≤
              ((branches C y).filter (· < t + 1)).card :=
            Finset.card_le_card fun w hw => Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
          omega
        · have hfilter : (branches C y).filter (· < t + 1) =
              insert t ((branches C y).filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨ha, hlt⟩
              by_cases hw : w = t
              · exact Or.inl hw
              · exact Or.inr ⟨ha, by omega⟩
            · rintro (rfl | ⟨ha, hlt⟩)
              · exact ⟨htA, by omega⟩
              · exact ⟨ha, by omega⟩
          rw [hfilter, Finset.card_insert_of_notMem (by simp)]
          omega
      · intro x hx w hw
        by_cases hwt : w = t
        · subst w
          exact hforce x fun r hr => htransfer x hx r (Finset.mem_union_right _ hr)
        · exact htransfer x hx w
            (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩))
    · have hFt' : ∀ w ∈ F, support (n := n) C w = ∅ → w < t := by
        intro w hw hs
        have hne : w ≠ t := by intro e; subst w; exact hex ⟨hw, hs⟩
        have hlt := hFt w hw hs
        omega
      obtain ⟨B, hB, hc, htransfer⟩ := ih F hFy hFt'
      have hmono : ((branches C y).filter (· < t)).card ≤
          ((branches C y).filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hB, by omega, htransfer⟩

def bit {n : ℕ} (A : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∈ A)

lemma small_witness {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (y : Fin n → Bool) (o : ℕ) (hy : value C y o = true) :
    ∃ A : Finset (Fin n), A.card ≤ ((branches C y).filter (· ≤ o)).card + 1 ∧ value C (bit A) o = true := by
  classical
  obtain ⟨B, hB, hc, ht⟩ := true_frontier C hG y (o + 1) {o}
    (by intro w hw; simpa only [Finset.mem_singleton.mp hw] using hy)
    (by intro w hw _; have := Finset.mem_singleton.mp hw; omega)
  choose p hp using fun w : ↥B => hB w.val w.property
  let A : Finset (Fin n) := Finset.univ.image p
  have ha : A.card ≤ B.card := by
    have h := Finset.card_image_le (f := p) (s := Finset.univ)
    simpa [A] using h
  have hv : ∀ w ∈ B, value C (bit A) w = true := by
    intro w hw
    let j : ↥B := ⟨w, hw⟩
    have hj : value C (fun q => decide (q = p j)) w = true :=
      (mem_support C w (p j)).mp (hp j)
    apply value_mono C hG _ (bit A) _ w hj
    intro q hq
    have e : q = p j := of_decide_eq_true hq
    subst q
    apply decide_eq_true
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  refine ⟨A, ?_, ht (bit A) hv o (Finset.mem_singleton_self o)⟩
  simp only [Finset.card_singleton, Nat.lt_succ_iff] at hc
  omega

lemma minterm_bound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (y : Fin n → Bool) (o k : ℕ) (hy : value C y o = true)
    (hmin : ∀ x : Fin n → Bool, value C x o = true →
      k ≤ (Finset.univ.filter (fun p : Fin n => x p = true)).card) :
    k ≤ ((branches C y).filter (· ≤ o)).card + 1 := by
  obtain ⟨A, hA, hv⟩ := small_witness C hG y o hy
  have hm := hmin (bit A) hv
  have hset : Finset.univ.filter (fun p : Fin n => bit A p = true) = A := by
    ext p
    simp [bit]
  rw [hset] at hm
  exact hm.trans hA

end MintermSlack

-- Component PlaneGeometry.
namespace PlaneGeometry

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack

def coLine {N : ℕ} (L : Fin N → Finset (Fin N)) (t : Fin N) : Fin N → Bool :=
  fun p => decide (p ∉ L t)

lemma plane_size {q N : ℕ} (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1) :
    q + 1 < N ∧ 3 ≤ N := by
  have hsq : 4 ≤ q * q := Nat.mul_le_mul hq hq
  simp only [pow_two] at hN
  constructor <;> omega

lemma exists_point_outside {q N : ℕ} (L : Fin N → Finset (Fin N))
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ i : Fin N, (L i).card = q + 1) (i : Fin N) :
    ∃ p : Fin N, p ∉ L i := by
  classical
  by_contra! h
  have hs : (Finset.univ : Finset (Fin N)) ⊆ L i := by
    intro p _
    exact h p
  have hc := Finset.card_le_card hs
  simp only [Finset.card_univ, Fintype.card_fin, hL i] at hc
  have hn := (plane_size hq hN).1
  omega

lemma exists_line_difference {q N : ℕ} (L : Fin N → Finset (Fin N))
    (hq : 2 ≤ q) (hL : ∀ i : Fin N, (L i).card = q + 1)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (t u : Fin N) (htu : t ≠ u) :
    ∃ p : Fin N, p ∈ L t ∧ p ∉ L u := by
  classical
  by_contra! h
  have hs : L t ⊆ L u := by
    intro p hp
    exact h p hp
  have hc := hI t u htu
  rw [Finset.inter_eq_left.mpr hs, hL t] at hc
  omega

lemma line_or_coLine_iff {q N : ℕ} (L : Fin N → Finset (Fin N))
    (hq : 2 ≤ q) (hL : ∀ i : Fin N, (L i).card = q + 1)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (t u : Fin N) :
    (∃ p ∈ L t, coLine L u p = true) ↔ t ≠ u := by
  classical
  constructor
  · rintro ⟨p, hp, hv⟩ htu
    subst u
    simp [coLine, hp] at hv
  · intro htu
    obtain ⟨p, hpt, hpu⟩ := exists_line_difference L hq hL hI t u htu
    exact ⟨p, hpt, by simp [coLine, hpu]⟩

lemma line_or_coLine {q N : ℕ} (L : Fin N → Finset (Fin N))
    (hq : 2 ≤ q) (hL : ∀ i : Fin N, (L i).card = q + 1)
    (hI : ∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1)
    (t u : Fin N) :
    decide (∃ p ∈ L t, coLine L u p = true) = decide (u ≠ t) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact (line_or_coLine_iff L hq hL hI t u).trans ne_comm

lemma no_raw_coSignature {q N : ℕ} (L : Fin N → Finset (Fin N))
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ i : Fin N, (L i).card = q + 1)
    (hPair : ∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i)
    (p i : Fin N) :
    ¬ ∀ t : Fin N, coLine L t p = decide (t ≠ i) := by
  classical
  intro hs
  have hpi : p ∈ L i := by
    by_contra hp
    have hi := hs i
    simp [coLine, hp] at hi
  obtain ⟨p', hp'⟩ := exists_point_outside L hq hN hL i
  have hpp' : p ≠ p' := by
    intro he
    subst p'
    exact hp' hpi
  obtain ⟨u, hpu, hp'u⟩ := hPair p p' hpp'
  have hui : u ≠ i := by
    intro he
    subst u
    exact hp' hp'u
  have hu := hs u
  simp [coLine, hpu, hui] at hu

lemma ancestor_lt {N : ℕ} (gates : List Gate) (h g : Fin gates.length)
    (hclosure : ∀ T : Finset (Fin gates.length),
      (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
        N + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) :
    g < h := by
  classical
  let T : Finset (Fin gates.length) := Finset.univ.filter fun i => i < h
  have hg : g ∈ T := hclosure T (by
    intro i g' hi _ hgi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hi with hi | hi
    · simpa only [hi] using hgi
    · exact lt_trans hgi (Finset.mem_filter.mp hi).2)
  exact (Finset.mem_filter.mp hg).2

lemma ancestor_set_lt {N : ℕ} (gates : List Gate) (h : Fin gates.length)
    (I : Finset (Fin gates.length))
    (hI : ∀ g ∈ I, (gates.get g).op = GateOp.and ∧
      ∀ T : Finset (Fin gates.length),
        (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          N + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) :
    ∀ g ∈ I, g < h := by
  intro g hg
  exact ancestor_lt gates h g (hI g hg).2

end PlaneGeometry

-- Component OrPrivateCount.
namespace OrPrivateCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack

def sampleSupport {n r : ℕ} (C : Circuit) (X : Fin r → Fin n → Bool)
    (w : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun p => value C (X p) w = true

lemma mem_sampleSupport {n r : ℕ} (C : Circuit) (X : Fin r → Fin n → Bool)
    (w : ℕ) (p : Fin r) :
    p ∈ sampleSupport C X w ↔ value C (X p) w = true := by
  simp [sampleSupport]

noncomputable def orBranches {n r : ℕ} (C : Circuit) (a : Fin n → Bool)
    (X : Fin r → Fin n → Bool) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter fun w =>
    (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.or ∧
      value C a w = false ∧ 2 ≤ (sampleSupport C X w).card

lemma false_wide_inputs {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (w : ℕ) (ha : value C a w = false)
    (hs : 2 ≤ (sampleSupport C X w).card) :
    ∃ P : Finset ℕ,
      (P.card ≤ 1 ∨ (w ∈ orBranches C a X ∧ P.card ≤ 2)) ∧
      (∀ v ∈ P, v < w) ∧ (∀ v ∈ P, value C a v = false) ∧
      ∀ x : Fin n → Bool, (∀ v ∈ P, value C x v = false) → value C x w = false := by
  classical
  have hn : n ≤ w := by
    by_contra! h
    let p : Fin n := ⟨w, h⟩
    have hap : a p = false := by
      have h := ha
      change value C a p = false at h
      simpa only [input_value] using h
    have he : sampleSupport C X w = Finset.univ.filter (fun q : Fin r => X q p = true) := by
      ext q
      simp only [mem_sampleSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      change value C (X q) p = true ↔ X q p = true
      rw [input_value]
    rw [he] at hs
    have := hraw p hap
    omega
  have hw : w < n + C.size := by
    by_contra! h
    have he : sampleSupport C X w = ∅ := by
      ext q
      simp [mem_sampleSupport, missing_value C (X q) w h]
    simp [he] at hs
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem hj)
  have form (x : Fin n → Bool) : value C x w =
      g.op.eval (g.inputs.map fun v => if v < w then value C x v else false) :=
    gate_value C x w hn hw
  have hnon : (sampleSupport C X w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hnon
  have hpval := (mem_sampleSupport C X w p).mp hp
  rcases hop with hop | hop
  · have earlier : ∀ v ∈ g.inputs, v < w := by
      rw [form] at hpval
      simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at hpval
      intro v hv
      by_contra! h
      have := hpval v hv
      simp [Nat.not_lt.mpr h] at this
    have hsome : ∃ v ∈ g.inputs, value C a v = false := by
      by_contra! h
      have hv : value C a w = true := by
        rw [form]
        simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
          Function.comp_apply, id_eq]
        intro v hv
        rw [ite_eq_left (earlier v hv)]
        simpa using h v hv
      rw [ha] at hv
      contradiction
    obtain ⟨v, hvg, hva⟩ := hsome
    refine ⟨{v}, Or.inl (by simp), ?_, ?_, ?_⟩
    · intro u hu
      simpa only [Finset.mem_singleton.mp hu] using earlier v hvg
    · intro u hu
      simpa only [Finset.mem_singleton.mp hu] using hva
    · intro x hx
      apply Bool.eq_false_iff.mpr
      intro hwtrue
      rw [form] at hwtrue
      simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at hwtrue
      have h := hwtrue v hvg
      rw [ite_eq_left (earlier v hvg), hx v (Finset.mem_singleton_self v)] at h
      contradiction
  · let P := g.inputs.toFinset.filter (· < w)
    have hall : ∀ v ∈ P, value C a v = false := by
      intro v hv
      obtain ⟨hvg, hvw⟩ := Finset.mem_filter.mp hv
      have h := ha
      rw [form] at h
      simp only [hop, GateOp.eval, List.any_map, List.any_eq_false,
        Function.comp_apply, id_eq] at h
      apply Bool.eq_false_iff.mpr
      simpa only [ite_eq_left hvw] using h v (List.mem_toFinset.mp hvg)
    refine ⟨P, Or.inr ⟨?_, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)⟩,
      (fun _ hv => (Finset.mem_filter.mp hv).2), hall, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Ico.mpr ⟨hn, hw⟩, ?_, ha, hs⟩
      rw [List.getD_eq_getElem _ _ hj]
      exact hop
    · intro x hx
      rw [form]
      simp only [hop, GateOp.eval, List.any_map, List.any_eq_false,
        Function.comp_apply, id_eq]
      intro v hv
      by_cases h : v < w
      · rw [ite_eq_left h]
        rw [hx v (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, h⟩)]
        decide
      · simp [h]

lemma false_frontier {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (t : ℕ) (F : Finset ℕ)
    (hFa : ∀ w ∈ F, value C a w = false)
    (hFt : ∀ w ∈ F, 2 ≤ (sampleSupport C X w).card → w < t) :
    ∃ B : Finset ℕ,
      (∀ w ∈ B, (sampleSupport C X w).card ≤ 1) ∧
      B.card ≤ F.card + ((orBranches C a X).filter (· < t)).card ∧
      ∀ x : Fin n → Bool, (∀ w ∈ B, value C x w = false) →
        ∀ w ∈ F, value C x w = false := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, ?_, by simp, fun _ h => h⟩
    intro w hw
    by_contra! hn
    have := hFt w hw (by omega)
    omega
  | succ t ih =>
    by_cases hex : t ∈ F ∧ 2 ≤ (sampleSupport C X t).card
    · obtain ⟨P, hPc, hPt, hPa, hforce⟩ :=
        false_wide_inputs C hG a X hraw t (hFa t hex.1) hex.2
      let F' := F.erase t ∪ P
      have hF'a : ∀ w ∈ F', value C a w = false := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFa w (Finset.mem_erase.mp hw).2
        · exact hPa w hw
      have hF't : ∀ w ∈ F', 2 ≤ (sampleSupport C X w).card → w < t := by
        intro w hw hs
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFt w (Finset.mem_erase.mp hw).2 hs
          omega
        · exact hPt w hw
      obtain ⟨B, hB, hc, htransfer⟩ := ih F' hF'a hF't
      refine ⟨B, hB, ?_, ?_⟩
      · have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        rcases hPc with hPc | ⟨htA, hPc⟩
        · have hmono : ((orBranches C a X).filter (· < t)).card ≤
              ((orBranches C a X).filter (· < t + 1)).card :=
            Finset.card_le_card fun w hw => Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
          omega
        · have hfilter : (orBranches C a X).filter (· < t + 1) =
              insert t ((orBranches C a X).filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨ha, hlt⟩
              by_cases hw : w = t
              · exact Or.inl hw
              · exact Or.inr ⟨ha, by omega⟩
            · rintro (rfl | ⟨ha, hlt⟩)
              · exact ⟨htA, by omega⟩
              · exact ⟨ha, by omega⟩
          rw [hfilter, Finset.card_insert_of_notMem (by simp)]
          omega
      · intro x hx w hw
        by_cases hwt : w = t
        · subst w
          exact hforce x fun v hv => htransfer x hx v (Finset.mem_union_right _ hv)
        · exact htransfer x hx w
            (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩))
    · have hFt' : ∀ w ∈ F, 2 ≤ (sampleSupport C X w).card → w < t := by
        intro w hw hs
        have hne : w ≠ t := by intro e; subst w; exact hex ⟨hw, hs⟩
        have hlt := hFt w hw hs
        omega
      obtain ⟨B, hB, hc, htransfer⟩ := ih F hFa hFt'
      have hmono : ((orBranches C a X).filter (· < t)).card ≤
          ((orBranches C a X).filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hB, by omega, htransfer⟩

lemma sample_or_prefix_count {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (o : ℕ) (ha : value C a o = false) (T : Finset (Fin r))
    (hpos : ∀ p ∈ T, value C (X p) o = true) :
    T.card ≤ ((orBranches C a X).filter (· ≤ o)).card + 1 := by
  classical
  obtain ⟨B, hB, hc, ht⟩ := false_frontier C hG a X hraw (o + 1) {o}
    (by intro w hw; simpa only [Finset.mem_singleton.mp hw] using ha)
    (by intro w hw _; have := Finset.mem_singleton.mp hw; omega)
  have hcover : T ⊆ B.biUnion (sampleSupport C X) := by
    intro p hp
    by_contra hnot
    have hb : ∀ w ∈ B, value C (X p) w = false := by
      intro w hw
      apply Bool.eq_false_iff.mpr
      intro hv
      exact hnot (Finset.mem_biUnion.mpr ⟨w, hw, (mem_sampleSupport C X w p).mpr hv⟩)
    have hfalse := ht (X p) hb o (Finset.mem_singleton_self o)
    rw [hpos p hp] at hfalse
    contradiction
  have hcard := Finset.card_le_card hcover
  have hsum := Finset.card_biUnion_le_card_mul B (sampleSupport C X) 1 hB
  simp only [mul_one] at hsum
  simp only [Finset.card_singleton, Nat.lt_succ_iff] at hc
  omega

lemma sample_or_count {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (o : ℕ) (ha : value C a o = false) (T : Finset (Fin r))
    (hpos : ∀ p ∈ T, value C (X p) o = true) :
    T.card ≤ (orBranches C a X).card + 1 := by
  have h := sample_or_prefix_count C hG a X hraw o ha T hpos
  have hc := Finset.card_filter_le (orBranches C a X) (· ≤ o)
  omega

def negative {n : ℕ} (T : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ T)

def baseSamples {n : ℕ} (Y : Finset (Fin n)) (p q : Fin n) : Bool :=
  decide (q ∈ Y ∨ q = p)

lemma baseSamples_raw {n : ℕ} (Y T : Finset (Fin n)) (hYT : Disjoint Y T)
    (p : Fin n) (ha : negative T p = false) :
    (Finset.univ.filter fun q : Fin n => baseSamples Y q p = true).card ≤ 1 := by
  have hpT : p ∈ T := by simpa [negative] using ha
  have hpY : p ∉ Y := fun h => Finset.disjoint_left.mp hYT h hpT
  have he : Finset.univ.filter (fun q : Fin n => baseSamples Y q p = true) = {p} := by
    ext q
    simp [baseSamples, hpY, eq_comm]
  simp [he]

lemma sampleSupport_subset {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (hYT : Disjoint Y T) (w : ℕ)
    (ha : value C (negative T) w = false) :
    sampleSupport C (baseSamples Y) w ⊆ T := by
  intro p hp
  by_contra hnot
  have hv := (mem_sampleSupport C (baseSamples Y) w p).mp hp
  have hm : value C (negative T) w = true := by
    apply value_mono C hG (baseSamples Y p) (negative T) _ w hv
    intro q hq
    apply decide_eq_true
    intro hqT
    have hq' : q ∈ Y ∨ q = p := of_decide_eq_true hq
    rcases hq' with hqY | rfl
    · exact Finset.disjoint_left.mp hYT hqY hqT
    · exact hnot hqT
  rw [ha] at hm
  contradiction

noncomputable def heavyAssigned {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ :=
  orBranches C (negative T) (baseSamples Y)

lemma heavy_or_prefix_count {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (hYT : Disjoint Y T) (o : ℕ)
    (ha : value C (negative T) o = false)
    (hpos : ∀ p ∈ T, value C (baseSamples Y p) o = true) :
    T.card - 1 ≤ ((heavyAssigned C Y T).filter (· ≤ o)).card := by
  have h := sample_or_prefix_count C hG (negative T) (baseSamples Y)
    (baseSamples_raw Y T hYT) o ha T hpos
  change T.card ≤ ((heavyAssigned C Y T).filter (· ≤ o)).card + 1 at h
  omega

lemma heavy_or_count {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (hYT : Disjoint Y T) (o : ℕ)
    (ha : value C (negative T) o = false)
    (hpos : ∀ p ∈ T, value C (baseSamples Y p) o = true) :
    T.card - 1 ≤ (heavyAssigned C Y T).card := by
  exact (heavy_or_prefix_count C hG Y T hYT o ha hpos).trans (Finset.card_filter_le _ _)

lemma heavyAssigned_disjoint {n m : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y : Finset (Fin n)) (S : Fin m → Finset (Fin n))
    (hYS : ∀ i, Disjoint Y (S i))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => heavyAssigned C Y (S i)) := by
  classical
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr fun w hi hj => ?_
  have hai := (Finset.mem_filter.mp hi).2.2.1
  have haj := (Finset.mem_filter.mp hj).2.2.1
  have hwide := (Finset.mem_filter.mp hi).2.2.2
  have hsub : sampleSupport C (baseSamples Y) w ⊆ S i ∩ S j := by
    intro p hp
    exact Finset.mem_inter.mpr
      ⟨sampleSupport_subset C hG Y (S i) (hYS i) w hai hp,
       sampleSupport_subset C hG Y (S j) (hYS j) w haj hp⟩
  have hcard := Finset.card_le_card hsub
  have hsmall := hinter i j hij
  omega

lemma heavy_or_sum_bound {n m : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y : Finset (Fin n)) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hYS : ∀ i, Disjoint Y (S i))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (ha : ∀ i, value C (negative (S i)) (o i) = false)
    (hpos : ∀ i p, p ∈ S i → value C (baseSamples Y p) (o i) = true) :
    (∑ i : Fin m, ((S i).card - 1)) ≤
      (Finset.univ.biUnion (fun i => heavyAssigned C Y (S i))).card := by
  classical
  calc
    (∑ i : Fin m, ((S i).card - 1)) ≤
        ∑ i : Fin m, (heavyAssigned C Y (S i)).card :=
      Finset.sum_le_sum fun i _ => heavy_or_count C hG Y (S i) (hYS i) (o i) (ha i) (hpos i)
    _ = (Finset.univ.biUnion (fun i => heavyAssigned C Y (S i))).card :=
      (Finset.card_biUnion (heavyAssigned_disjoint C hG Y S hYS hinter)).symm

end OrPrivateCount

-- Component ReaderOrCount.
namespace ReaderOrCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack
open PEqualNP.Outside.L_meta_1613_aux.OrPrivateCount

noncomputable def readerOrBranches {n r : ℕ} (C : Circuit) (z : ℕ)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool) : Finset ℕ := by
  classical
  exact (orBranches C a X).filter fun w =>
    ¬ (z < w ∧ z ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs)

lemma mem_readerOrBranches {n r : ℕ} (C : Circuit) (z : ℕ)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool) (w : ℕ) :
    w ∈ readerOrBranches C z a X ↔
      w ∈ Finset.Ico n (n + C.size) ∧
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.or ∧
      value C a w = false ∧ 2 ≤ (sampleSupport C X w).card ∧
      ¬ (z < w ∧ z ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs) := by
  classical
  simp only [readerOrBranches, orBranches, Finset.mem_filter]
  tauto

lemma reader_false_wide_inputs {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : ℕ) (hzero : ∀ x : Fin n → Bool, value C x z = false)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (w : ℕ) (ha : value C a w = false)
    (hs : 2 ≤ (sampleSupport C X w).card) :
    ∃ P : Finset ℕ,
      (P.card ≤ 1 ∨ (w ∈ readerOrBranches C z a X ∧ P.card ≤ 2)) ∧
      (∀ v ∈ P, v < w) ∧ (∀ v ∈ P, value C a v = false) ∧
      ∀ x : Fin n → Bool, (∀ v ∈ P, value C x v = false) → value C x w = false := by
  classical
  have hn : n ≤ w := by
    by_contra! h
    let p : Fin n := ⟨w, h⟩
    have hap : a p = false := by
      have h := ha
      change value C a p = false at h
      simpa only [input_value] using h
    have he : sampleSupport C X w = Finset.univ.filter (fun q : Fin r => X q p = true) := by
      ext q
      simp only [mem_sampleSupport, Finset.mem_filter, Finset.mem_univ, true_and]
      change value C (X q) p = true ↔ X q p = true
      rw [input_value]
    rw [he] at hs
    have := hraw p hap
    omega
  have hw : w < n + C.size := by
    by_contra! h
    have he : sampleSupport C X w = ∅ := by
      ext q
      simp [mem_sampleSupport, missing_value C (X q) w h]
    simp [he] at hs
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem hj)
  have form (x : Fin n → Bool) : value C x w =
      g.op.eval (g.inputs.map fun v => if v < w then value C x v else false) :=
    gate_value C x w hn hw
  have hnon : (sampleSupport C X w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hnon
  have hpval := (mem_sampleSupport C X w p).mp hp
  rcases hop with hop | hop
  · have earlier : ∀ v ∈ g.inputs, v < w := by
      rw [form] at hpval
      simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at hpval
      intro v hv
      by_contra! h
      have := hpval v hv
      simp [Nat.not_lt.mpr h] at this
    have hsome : ∃ v ∈ g.inputs, value C a v = false := by
      by_contra! h
      have hv : value C a w = true := by
        rw [form]
        simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
          Function.comp_apply, id_eq]
        intro v hv
        rw [ite_eq_left (earlier v hv)]
        simpa using h v hv
      rw [ha] at hv
      contradiction
    obtain ⟨v, hvg, hva⟩ := hsome
    refine ⟨{v}, Or.inl (by simp), ?_, ?_, ?_⟩
    · intro u hu
      simpa only [Finset.mem_singleton.mp hu] using earlier v hvg
    · intro u hu
      simpa only [Finset.mem_singleton.mp hu] using hva
    · intro x hx
      apply Bool.eq_false_iff.mpr
      intro hwtrue
      rw [form] at hwtrue
      simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at hwtrue
      have h := hwtrue v hvg
      rw [ite_eq_left (earlier v hvg), hx v (Finset.mem_singleton_self v)] at h
      contradiction
  · let Q := g.inputs.toFinset.filter (· < w)
    let P := Q.erase z
    have hQcard : Q.card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
    have hPsub : P ⊆ Q := Finset.erase_subset _ _
    have hPcard : P.card ≤ 2 := (Finset.card_le_card hPsub).trans hQcard
    have hall : ∀ v ∈ P, value C a v = false := by
      intro v hv
      obtain ⟨hvg, hvw⟩ := Finset.mem_filter.mp (hPsub hv)
      have h := ha
      rw [form] at h
      simp only [hop, GateOp.eval, List.any_map, List.any_eq_false,
        Function.comp_apply, id_eq] at h
      apply Bool.eq_false_iff.mpr
      simpa only [ite_eq_left hvw] using h v (List.mem_toFinset.mp hvg)
    have hcost : P.card ≤ 1 ∨ (w ∈ readerOrBranches C z a X ∧ P.card ≤ 2) := by
      by_cases hread : z < w ∧ z ∈ g.inputs
      · have hzQ : z ∈ Q := Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr hread.2, hread.1⟩
        have he := Finset.card_erase_add_one hzQ
        exact Or.inl (by change (Q.erase z).card ≤ 1; omega)
      · refine Or.inr ⟨?_, hPcard⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_Ico.mpr ⟨hn, hw⟩, ?_, ha, hs⟩
          rw [List.getD_eq_getElem _ _ hj]
          exact hop
        · rw [List.getD_eq_getElem _ _ hj]
          exact hread
    refine ⟨P, hcost, (fun _ hv => (Finset.mem_filter.mp (hPsub hv)).2), hall, ?_⟩
    intro x hx
    rw [form]
    simp only [hop, GateOp.eval, List.any_map, List.any_eq_false,
      Function.comp_apply, id_eq]
    intro v hv
    by_cases h : v < w
    · rw [ite_eq_left h]
      by_cases hvz : v = z
      · subst v
        rw [hzero x]
        decide
      · rw [hx v (Finset.mem_erase.mpr
          ⟨hvz, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, h⟩⟩)]
        decide
    · simp [h]

lemma reader_false_frontier {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : ℕ) (hzero : ∀ x : Fin n → Bool, value C x z = false)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (t : ℕ) (F : Finset ℕ)
    (hFa : ∀ w ∈ F, value C a w = false)
    (hFt : ∀ w ∈ F, 2 ≤ (sampleSupport C X w).card → w < t) :
    ∃ B : Finset ℕ,
      (∀ w ∈ B, (sampleSupport C X w).card ≤ 1) ∧
      B.card ≤ F.card + ((readerOrBranches C z a X).filter (· < t)).card ∧
      ∀ x : Fin n → Bool, (∀ w ∈ B, value C x w = false) →
        ∀ w ∈ F, value C x w = false := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, ?_, by simp, fun _ h => h⟩
    intro w hw
    by_contra! hn
    have := hFt w hw (by omega)
    omega
  | succ t ih =>
    by_cases hex : t ∈ F ∧ 2 ≤ (sampleSupport C X t).card
    · obtain ⟨P, hPc, hPt, hPa, hforce⟩ :=
        reader_false_wide_inputs C hG z hzero a X hraw t (hFa t hex.1) hex.2
      let F' := F.erase t ∪ P
      have hF'a : ∀ w ∈ F', value C a w = false := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFa w (Finset.mem_erase.mp hw).2
        · exact hPa w hw
      have hF't : ∀ w ∈ F', 2 ≤ (sampleSupport C X w).card → w < t := by
        intro w hw hs
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFt w (Finset.mem_erase.mp hw).2 hs
          omega
        · exact hPt w hw
      obtain ⟨B, hB, hc, htransfer⟩ := ih F' hF'a hF't
      refine ⟨B, hB, ?_, ?_⟩
      · have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        rcases hPc with hPc | ⟨htA, hPc⟩
        · have hmono : ((readerOrBranches C z a X).filter (· < t)).card ≤
              ((readerOrBranches C z a X).filter (· < t + 1)).card :=
            Finset.card_le_card fun w hw => Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
          omega
        · have hfilter : (readerOrBranches C z a X).filter (· < t + 1) =
              insert t ((readerOrBranches C z a X).filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨ha, hlt⟩
              by_cases hw : w = t
              · exact Or.inl hw
              · exact Or.inr ⟨ha, by omega⟩
            · rintro (rfl | ⟨ha, hlt⟩)
              · exact ⟨htA, by omega⟩
              · exact ⟨ha, by omega⟩
          rw [hfilter, Finset.card_insert_of_notMem (by simp)]
          omega
      · intro x hx w hw
        by_cases hwt : w = t
        · subst w
          exact hforce x fun v hv => htransfer x hx v (Finset.mem_union_right _ hv)
        · exact htransfer x hx w
            (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩))
    · have hFt' : ∀ w ∈ F, 2 ≤ (sampleSupport C X w).card → w < t := by
        intro w hw hs
        have hne : w ≠ t := by intro e; subst w; exact hex ⟨hw, hs⟩
        have hlt := hFt w hw hs
        omega
      obtain ⟨B, hB, hc, htransfer⟩ := ih F hFa hFt'
      have hmono : ((readerOrBranches C z a X).filter (· < t)).card ≤
          ((readerOrBranches C z a X).filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hB, by omega, htransfer⟩

lemma reader_sample_or_prefix_count {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : ℕ) (hzero : ∀ x : Fin n → Bool, value C x z = false)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (o : ℕ) (ha : value C a o = false) (T : Finset (Fin r))
    (hpos : ∀ p ∈ T, value C (X p) o = true) :
    T.card ≤ ((readerOrBranches C z a X).filter (· ≤ o)).card + 1 := by
  classical
  obtain ⟨B, hB, hc, ht⟩ := reader_false_frontier C hG z hzero a X hraw (o + 1) {o}
    (by intro w hw; simpa only [Finset.mem_singleton.mp hw] using ha)
    (by intro w hw _; have := Finset.mem_singleton.mp hw; omega)
  have hcover : T ⊆ B.biUnion (sampleSupport C X) := by
    intro p hp
    by_contra hnot
    have hb : ∀ w ∈ B, value C (X p) w = false := by
      intro w hw
      apply Bool.eq_false_iff.mpr
      intro hv
      exact hnot (Finset.mem_biUnion.mpr ⟨w, hw, (mem_sampleSupport C X w p).mpr hv⟩)
    have hfalse := ht (X p) hb o (Finset.mem_singleton_self o)
    rw [hpos p hp] at hfalse
    contradiction
  have hcard := Finset.card_le_card hcover
  have hsum := Finset.card_biUnion_le_card_mul B (sampleSupport C X) 1 hB
  simp only [mul_one] at hsum
  simp only [Finset.card_singleton, Nat.lt_succ_iff] at hc
  omega

lemma reader_sample_or_count {n r : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : ℕ) (hzero : ∀ x : Fin n → Bool, value C x z = false)
    (a : Fin n → Bool) (X : Fin r → Fin n → Bool)
    (hraw : ∀ p : Fin n, a p = false →
      (Finset.univ.filter fun q : Fin r => X q p = true).card ≤ 1)
    (o : ℕ) (ha : value C a o = false) (T : Finset (Fin r))
    (hpos : ∀ p ∈ T, value C (X p) o = true) :
    T.card ≤ (readerOrBranches C z a X).card + 1 := by
  have h := reader_sample_or_prefix_count C hG z hzero a X hraw o ha T hpos
  have hc := Finset.card_filter_le (readerOrBranches C z a X) (· ≤ o)
  omega

end ReaderOrCount

-- Component LightCount.
namespace MintermSlack

open PEqualNP.CircuitLowerBounds

def lightAssigned {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (z : ℕ) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    w ≠ z ∧ support (n := n) C w ⊆ S ∧ 2 ≤ (support (n := n) C w).card

lemma light_card_assigned {n k c : ℕ} (C : Circuit) (S : Finset (Fin n)) (o z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ S)
    (hsparse : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ S, x q = false) → value C x o = false)
    (hk : c < k) (hc : c + 1 ≤ S.card) :
    c ≤ (lightAssigned C S z).card := by
  classical
  let G := lightAssigned C S z
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

  let clean (w : ℕ) : Finset (Fin n) :=
    if value C (fun _ : Fin n => false) w = true then ∅
    else if support (n := n) C w ⊆ S then support (n := n) C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hzero : value C (fun _ : Fin n => false) w = true
    · simp [clean, hzero]
    by_cases hs : support (n := n) C w ⊆ S
    · change (if value C (fun _ : Fin n => false) w = true then ∅
        else if support (n := n) C w ⊆ S then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_right hzero, ite_eq_left hs]
      by_contra! hlarge
      have hwz : w ≠ z := by
        intro he
        subst w
        exact hzero (hz (fun _ => false))
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hwz, hs, by omega⟩)
    · simp [clean, hzero, hs]
  have hcover : (B.biUnion clean).card < S.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover

  let D := B.filter fun w =>
    value C (fun _ : Fin n => false) w ≠ true ∧ ¬ support (n := n) C w ⊆ S
  have hout (w : {w // w ∈ D}) :
      ∃ q : Fin n, q ∈ support (n := n) C w.val ∧ q ∉ S := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2.2 h
  choose q hq using hout
  let U := D.attach.image q
  let x : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card < k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ c := hb
    _ < k := hk
  have hxfalse : value C x o = false := by
    apply hsparse x
    · have hset : Finset.univ.filter (fun r => x r = true) = U := by
        ext r
        simp [x]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [x, hnot]
  have hxtrue : value C x o = true := by
    apply hcut (fun r => decide (r = p)) x _ o
      (Finset.mem_singleton_self o) ((ho p).mpr hp)
    intro w hw hv
    by_cases hzero : value C (fun _ : Fin n => false) w = true
    · apply value_mono C hG (fun _ : Fin n => false) x _ w hzero
      intro r hr
      contradiction
    by_cases hs : support (n := n) C w ⊆ S
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_right hzero, ite_eq_left hs, mem_support] using hv⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hzero, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) x _ w
        ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [x, hm]
  simp [hxfalse] at hxtrue

lemma light_window_bound {n k : ℕ} (C : Circuit) (S : Finset (Fin n)) (o z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hwindow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    min k S.card - 1 ≤ (lightAssigned C S z).card := by
  classical
  by_cases hsmall : min k S.card ≤ 1
  · have hzero : min k S.card - 1 = 0 := by omega
    simp [hzero]
  have hlarge : 2 ≤ min k S.card := by omega
  have hk : 1 < k := by have := Nat.min_le_left k S.card; omega
  have ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ S := by
    intro p
    have hset : Finset.univ.filter (fun q : Fin n => decide (q = p) = true) = {p} := by
      ext q
      simp
    have hweight : (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card < k := by
      rw [hset, Finset.card_singleton]
      exact hk
    rw [hwindow (fun q : Fin n => decide (q = p)) hweight]
    simp
  have hsparse : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ S, x q = false) → value C x o = false := by
    intro x hx hS
    rw [hwindow x hx]
    have hnone : ¬ ∃ p ∈ S, x p = true := by
      rintro ⟨p, hp, hv⟩
      rw [hS p hp] at hv
      contradiction
    simp [hnone]
  apply light_card_assigned C S o z hG hz ho hsparse
  · have := Nat.min_le_left k S.card
    omega
  · have := Nat.min_le_right k S.card
    omega

lemma lightAssigned_pairwise_disjoint {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => lightAssigned C (S i) z) := by
  classical
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
  rcases (Finset.mem_filter.mp hwi).2 with ⟨_, hi, hwide⟩
  rcases (Finset.mem_filter.mp hwj).2 with ⟨_, hj, _⟩
  have hsub : support (n := n) C w ⊆ S i ∩ S j :=
    fun p hp => Finset.mem_inter.mpr ⟨hi hp, hj hp⟩
  have hle := Finset.card_le_card hsub
  have hsmall := hinter i j hij
  omega

lemma light_window_sum_bound {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, (min k (S i).card - 1)) ≤
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card := by
  classical
  calc
    (∑ i : Fin m, (min k (S i).card - 1)) ≤
        ∑ i : Fin m, (lightAssigned C (S i) z).card :=
      Finset.sum_le_sum fun i _ => light_window_bound C (S i) (o i) z hG hz (hwindow i)
    _ = (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card :=
      (Finset.card_biUnion (lightAssigned_pairwise_disjoint C S z hinter)).symm

lemma lightAssigned_union_subset {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) :
    Finset.univ.biUnion (fun i => lightAssigned C (S i) z) ⊆
      (Finset.Ico n (n + C.size)).erase z := by
  classical
  intro w hw
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
  have hmem := Finset.mem_filter.mp hi
  exact Finset.mem_erase.mpr ⟨hmem.2.1, hmem.1⟩

end MintermSlack

-- Component LightMinterm.
namespace MintermSlack

open PEqualNP.CircuitLowerBounds

lemma light_minterm_bound {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (u z : ℕ) (y : Fin n → Bool)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hzgate : z ∈ Finset.Ico n (n + C.size))
    (huz : u < z)
    (hy : value C y u = true)
    (hmin : ∀ x : Fin n → Bool, value C x u = true →
      k ≤ (Finset.univ.filter (fun p : Fin n => x p = true)).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, (min k (S i).card - 1)) + k ≤ C.size := by
  classical
  let L := Finset.univ.biUnion (fun i => lightAssigned C (S i) z)
  let A := (branches C y).filter (· ≤ u)
  let R := Finset.Ico n (n + C.size)
  have hL : L ⊆ R.erase z := lightAssigned_union_subset C S z
  have hA : A ⊆ R.erase z := by
    intro w hw
    obtain ⟨hwa, hwu⟩ := Finset.mem_filter.mp hw
    have hgate := (Finset.mem_filter.mp hwa).1
    exact Finset.mem_erase.mpr ⟨by omega, hgate⟩
  have hdis : Disjoint L A := by
    refine Finset.disjoint_left.mpr fun w hwL hwA => ?_
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hwL
    have hwide := (Finset.mem_filter.mp hwi).2.2.2
    obtain ⟨hwa, _⟩ := Finset.mem_filter.mp hwA
    have hempty := (Finset.mem_filter.mp hwa).2.2.1
    simp [hempty] at hwide
  have hcards : L.card + A.card ≤ (R.erase z).card := by
    rw [← Finset.card_union_of_disjoint hdis]
    exact Finset.card_le_card (Finset.union_subset hL hA)
  have hremove : (R.erase z).card + 1 = C.size := by
    have h := Finset.card_erase_add_one hzgate
    simpa [R] using h
  have hlight := light_window_sum_bound C S o z hG hz hinter hwindow
  have hbranch := minterm_bound C hG y u k hy hmin
  change (∑ i : Fin m, (min k (S i).card - 1)) ≤ L.card at hlight
  change k ≤ A.card + 1 at hbranch
  omega

end MintermSlack

-- Component NotWindow.
namespace MintermSlack

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

lemma one_not_window_bound_explicit {n m k : ℕ} (gates : List Gate) (origOut : ℕ)
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

lemma one_not_window_bound {n m k : ℕ} (C : Circuit)
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

end MintermSlack

-- Component HeavyReplacement.
namespace HeavyReplacement

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack

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

open PEqualNP.Outside.L_meta_1613_aux.OrPrivateCount

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

lemma one_not_heavy_or_count {n : ℕ} (gates : List Gate) (i0 : Fin gates.length)
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

lemma false_window_replacement {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n))
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

end HeavyReplacement

-- Component AnchorCount.
namespace AnchorCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack
open PEqualNP.Outside.L_meta_1613_aux.OrPrivateCount
open PEqualNP.Outside.L_meta_1613_aux.ReaderOrCount
open PEqualNP.Outside.L_meta_1613_aux.HeavyReplacement

def anchorSamples {n m : ℕ} (L : Fin m → Finset (Fin n))
    (B : Fin m → Fin n → Finset (Fin n)) (t : Fin m) (p v : Fin n) : Bool :=
  if p ∈ L t then decide (v = p ∨ v ∈ B t p) else negative (L t) v

noncomputable def anchorCharges {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (t : Fin m) : Finset ℕ :=
  readerOrBranches C z (negative (L t)) (anchorSamples L B t)

lemma mem_anchorCharges {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (t : Fin m) (w : ℕ) :
    w ∈ anchorCharges C z L B t ↔
      w ∈ Finset.Ico n (n + C.size) ∧
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.or ∧
      value C (negative (L t)) w = false ∧
      2 ≤ (sampleSupport C (anchorSamples L B t) w).card ∧
      ¬ (z < w ∧ z ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs) :=
  mem_readerOrBranches C z (negative (L t)) (anchorSamples L B t) w

lemma anchor_support_subset {n m : ℕ} (C : Circuit)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (t : Fin m) (w : ℕ) (hfalse : value C (negative (L t)) w = false) :
    sampleSupport C (anchorSamples L B t) w ⊆ L t := by
  intro p hp
  have hv := (mem_sampleSupport C (anchorSamples L B t) w p).mp hp
  by_contra hpnot
  have he : anchorSamples L B t p = negative (L t) := by
    funext v
    simp [anchorSamples, hpnot]
  rw [he, hfalse] at hv
  contradiction

lemma anchor_raw_count {n m : ℕ}
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (t : Fin m) (hB : ∀ p ∈ L t, B t p ∩ L t = ∅)
    (v : Fin n) (hv : negative (L t) v = false) :
    (Finset.univ.filter (fun p : Fin n => anchorSamples L B t p v = true)).card ≤ 1 := by
  classical
  have hvL : v ∈ L t := by simpa [negative] using hv
  have hsub : Finset.univ.filter (fun p : Fin n => anchorSamples L B t p v = true) ⊆ {v} := by
    intro p hp
    have hval := (Finset.mem_filter.mp hp).2
    by_cases hpL : p ∈ L t
    · rw [anchorSamples, ite_eq_left hpL] at hval
      rcases of_decide_eq_true hval with he | hvB
      · exact Finset.mem_singleton.mpr he.symm
      · have hmem : v ∈ B t p ∩ L t := Finset.mem_inter.mpr ⟨hvB, hvL⟩
        rw [hB p hpL] at hmem
        simp at hmem
    · simp only [anchorSamples, ite_eq_right hpL, hv] at hval
      contradiction
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_singleton] using hc

lemma anchor_charge_count {n m q : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (t : Fin m) (o : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : ∀ x : Fin n → Bool, value C x z = false)
    (hcard : (L t).card = q + 1)
    (hB : ∀ p ∈ L t, B t p ∩ L t = ∅)
    (hneg : value C (negative (L t)) o = false)
    (hpos : ∀ p ∈ L t, value C (anchorSamples L B t p) o = true) :
    q ≤ (anchorCharges C z L B t).card := by
  have hc := reader_sample_or_count C hG z hzero (negative (L t)) (anchorSamples L B t)
    (anchor_raw_count L B t hB) o hneg (L t) hpos
  change (L t).card ≤ (anchorCharges C z L B t).card + 1 at hc
  omega

lemma anchor_crossing {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (t t' : Fin m) (hinter : (L t ∩ L t').card ≤ 1) (w : ℕ)
    (hw : w ∈ anchorCharges C z L B t)
    (hfalse : value C (negative (L t')) w = false) :
    ∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty := by
  classical
  have hm := (mem_anchorCharges C z L B t w).mp hw
  have hwide := hm.2.2.2.1
  have hsub := anchor_support_subset C L B t w hm.2.2.1
  have hex : ∃ p, p ∈ sampleSupport C (anchorSamples L B t) w ∧ p ∉ L t' := by
    by_contra! hn
    have hinc : sampleSupport C (anchorSamples L B t) w ⊆ L t ∩ L t' := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨hsub hp, hn p hp⟩
    have hc := Finset.card_le_card hinc
    omega
  obtain ⟨p, hp, hpnot⟩ := hex
  have hpL := hsub hp
  refine ⟨p, Finset.mem_sdiff.mpr ⟨hpL, hpnot⟩, ?_⟩
  by_contra hnone
  have hinput : ∀ v : Fin n, anchorSamples L B t p v = true → negative (L t') v = true := by
    intro v hv
    rw [anchorSamples, ite_eq_left hpL] at hv
    apply decide_eq_true
    rcases of_decide_eq_true hv with he | hvB
    · simpa only [he] using hpnot
    · intro hvL'
      exact hnone ⟨v, Finset.mem_inter.mpr ⟨hvB, hvL'⟩⟩
  have htrue := value_mono C hG (anchorSamples L B t p) (negative (L t')) hinput w
    ((mem_sampleSupport C (anchorSamples L B t) w p).mp hp)
  rw [hfalse] at htrue
  contradiction

lemma anchorCharges_pairwise_disjoint {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (Lam : Finset (Fin m))
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ t t' : Fin m, t ≠ t' → (L t ∩ L t').card ≤ 1)
    (hcross : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
         (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) :
    (Lam : Set (Fin m)).PairwiseDisjoint (anchorCharges C z L B) := by
  intro t ht t' ht' hne
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have hfalse := ((mem_anchorCharges C z L B t w).mp hw).2.2.1
  have hfalse' := ((mem_anchorCharges C z L B t' w).mp hw').2.2.1
  exact hcross t ht t' ht' hne
    ⟨anchor_crossing C z L B hG t t' (hinter t t' hne) w hw hfalse',
      anchor_crossing C z L B hG t' t (hinter t' t hne.symm) w hw' hfalse⟩

lemma anchor_union_count {n m q : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (Lam : Finset (Fin m)) (out : Fin m → ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : ∀ x : Fin n → Bool, value C x z = false)
    (hcard : ∀ t ∈ Lam, (L t).card = q + 1)
    (hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅)
    (hneg : ∀ t ∈ Lam, value C (negative (L t)) (out t) = false)
    (hpos : ∀ t ∈ Lam, ∀ p ∈ L t, value C (anchorSamples L B t p) (out t) = true)
    (hinter : ∀ t t' : Fin m, t ≠ t' → (L t ∩ L t').card ≤ 1)
    (hcross : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
         (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) :
    q * Lam.card ≤ (Lam.biUnion (anchorCharges C z L B)).card := by
  classical
  calc
    q * Lam.card = ∑ t ∈ Lam, q := by simp [Nat.mul_comm]
    _ ≤ ∑ t ∈ Lam, (anchorCharges C z L B t).card :=
      Finset.sum_le_sum (fun t ht => anchor_charge_count C z L B t (out t) hG hzero
        (hcard t ht) (hB t ht) (hneg t ht) (hpos t ht))
    _ = (Lam.biUnion (anchorCharges C z L B)).card :=
      (Finset.card_biUnion (anchorCharges_pairwise_disjoint C z L B Lam hG hinter hcross)).symm

lemma anchor_charge_ne_zero {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (hzero : ∀ x : Fin n → Bool, value C x z = false) (t : Fin m) :
    z ∉ anchorCharges C z L B t := by
  intro hz
  have hwide := ((mem_anchorCharges C z L B t z).mp hz).2.2.2.1
  have he : sampleSupport C (anchorSamples L B t) z = ∅ := by
    ext p
    simp [mem_sampleSupport, hzero]
  simp [he] at hwide

lemma anchorCharges_not_z {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (hzero : ∀ x : Fin n → Bool, value C x z = false) (t : Fin m) :
    z ∉ anchorCharges C z L B t := anchor_charge_ne_zero C z L B hzero t

lemma anchorCharges_not_h {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (t : Fin m) (h : ℕ) (htrue : value C (negative (L t)) h = true) :
    h ∉ anchorCharges C z L B t := by
  intro hh
  have hfalse := ((mem_anchorCharges C z L B t h).mp hh).2.2.1
  rw [hfalse] at htrue
  contradiction

lemma mem_anchor_union {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (Lam : Finset (Fin m)) (w : ℕ) :
    w ∈ Lam.biUnion (anchorCharges C z L B) ↔
      ∃ t ∈ Lam, w ∈ anchorCharges C z L B t := by
  classical
  exact Finset.mem_biUnion

lemma anchor_union_properties {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (Lam : Finset (Fin m)) (w : ℕ)
    (hw : w ∈ Lam.biUnion (anchorCharges C z L B)) :
    w ∈ Finset.Ico n (n + C.size) ∧
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.or ∧
      ¬ (z < w ∧ z ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs) ∧
      ∃ t ∈ Lam, value C (negative (L t)) w = false := by
  obtain ⟨t, ht, hwt⟩ := (mem_anchor_union C z L B Lam w).mp hw
  have hmem := (mem_anchorCharges C z L B t w).mp hwt
  exact ⟨hmem.1, hmem.2.1, hmem.2.2.2.2, t, ht, hmem.2.2.1⟩

lemma anchor_union_not_h {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (Lam : Finset (Fin m)) (h : ℕ)
    (htrue : ∀ t ∈ Lam, value C (negative (L t)) h = true) :
    h ∉ Lam.biUnion (anchorCharges C z L B) := by
  intro hh
  obtain ⟨t, ht, hht⟩ := (mem_anchor_union C z L B Lam h).mp hh
  exact anchorCharges_not_h C z L B t h (htrue t ht) hht

lemma anchor_union_not_z {n m : ℕ} (C : Circuit) (z : ℕ)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (Lam : Finset (Fin m)) (hzero : ∀ x : Fin n → Bool, value C x z = false) :
    z ∉ Lam.biUnion (anchorCharges C z L B) := by
  intro hz
  obtain ⟨t, _, hzt⟩ := (mem_anchor_union C z L B Lam z).mp hz
  exact anchorCharges_not_z C z L B hzero t hzt

lemma false_replacement_of_head_true {n : ℕ} (gates : List Gate)
    (j : Fin gates.length) (origOut u : ℕ)
    (hop : (gates.get j).op = GateOp.not)
    (hhead : (gates.get j).inputs.head? = some u)
    (hlt : u < n + j.val) (x : Fin n → Bool)
    (hx : value ⟨gates, origOut⟩ x u = true) (w : ℕ) :
    value (repl0C gates j.val) x w = value ⟨gates, origOut⟩ x w := by
  apply repl0C_eq gates j origOut x _ w
  rw [orig_not_value gates j origOut u hop hhead hlt x, hx]
  rfl

end AnchorCount

-- Component CoLineCount.
namespace CoLineCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack

lemma zero_reader_predecessor {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (z : ℕ) (hz : ∀ x : Fin n → Bool, value C x z = false)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hzw : z < w)
    (hread : z ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs)
    (a : Fin n → Bool) (ha : value C a w = true) :
    ∃ v : ℕ, v < w ∧ ∀ x : Fin n → Bool, value C x w = value C x v := by
  classical
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  have hzg : z ∈ g.inputs := by
    simpa only [List.getD_eq_getElem _ _ hj] using hread
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem hj)
  have form (x : Fin n → Bool) : value C x w =
      g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
    gate_value C x w hn hw
  rcases hop with hop | hop
  · have h := ha
    rw [form] at h
    simp only [hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at h
    have hztrue := h z hzg
    rw [ite_eq_left hzw, hz a] at hztrue
    contradiction
  · let Q := g.inputs.toFinset.filter (· < w)
    let P := Q.erase z
    have hQcard : Q.card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
    have hzQ : z ∈ Q := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hzg, hzw⟩
    have hPcard : P.card ≤ 1 := by
      have h := Finset.card_erase_add_one hzQ
      change (Q.erase z).card ≤ 1
      omega
    have hsome : ∃ v ∈ P, value C a v = true := by
      have h := ha
      rw [form] at h
      simp only [hop, GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq] at h
      obtain ⟨v, hvg, hv⟩ := h
      have hvw : v < w := by
        by_contra! h
        simp [Nat.not_lt.mpr h] at hv
      have hva : value C a v = true := by simpa only [ite_eq_left hvw] using hv
      have hvz : v ≠ z := by
        intro he
        subst v
        rw [hz a] at hva
        contradiction
      exact ⟨v, Finset.mem_erase.mpr
        ⟨hvz, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hvg, hvw⟩⟩, hva⟩
    obtain ⟨v, hvP, _⟩ := hsome
    obtain ⟨_, hvQ⟩ := Finset.mem_erase.mp hvP
    obtain ⟨hvg, hvw⟩ := Finset.mem_filter.mp hvQ
    refine ⟨v, hvw, ?_⟩
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro h
      rw [form] at h
      simp only [hop, GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq] at h
      obtain ⟨r, hrg, hr⟩ := h
      have hrw : r < w := by
        by_contra! h
        simp [Nat.not_lt.mpr h] at hr
      have hrx : value C x r = true := by simpa only [ite_eq_left hrw] using hr
      have hrz : r ≠ z := by
        intro he
        subst r
        rw [hz x] at hrx
        contradiction
      have hrP : r ∈ P := Finset.mem_erase.mpr
        ⟨hrz, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hrg, hrw⟩⟩
      have he := Finset.card_le_one.mp hPcard r hrP v hvP
      simpa only [he] using hrx
    · intro hv
      rw [form]
      simp only [hop, GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq]
      exact ⟨v, List.mem_toFinset.mp hvg, by simpa only [ite_eq_left hvw] using hv⟩

def coSignature {n r : ℕ} (C : Circuit) (X : Fin r → Fin n → Bool)
    (w : ℕ) (i : Fin r) : Prop :=
  ∀ t : Fin r, value C (X t) w = decide (t ≠ i)

lemma signature_representatives {n r : ℕ} (C : Circuit)
    (X : Fin r → Fin n → Bool) (out : Fin r → ℕ) (z : ℕ) (hr : 2 ≤ r)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = false)
    (hraw : ∀ (p : Fin n) (i : Fin r), ¬ ∀ t : Fin r, X t p = decide (t ≠ i))
    (hout : ∀ i : Fin r, coSignature C X (out i) i) :
    ∃ rep : Fin r → ℕ, Function.Injective rep ∧
      ∀ i : Fin r, rep i ∈ Finset.Ico n (n + C.size) ∧
        coSignature C X (rep i) i ∧
        ¬ (z < rep i ∧ z ∈ (C.gates.getD (rep i - n) ⟨GateOp.or, []⟩).inputs) := by
  classical
  let : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  have hex (i : Fin r) : ∃ w : ℕ, coSignature C X w i := ⟨out i, hout i⟩
  let rep : Fin r → ℕ := fun i => Nat.find (hex i)
  have hsig (i : Fin r) : coSignature C X (rep i) i := Nat.find_spec (hex i)
  have hmin (i : Fin r) (v : ℕ) (hv : v < rep i) : ¬ coSignature C X v i :=
    Nat.find_min (hex i) hv
  have hprops (i : Fin r) : rep i ∈ Finset.Ico n (n + C.size) ∧
      coSignature C X (rep i) i ∧
      ¬ (z < rep i ∧ z ∈ (C.gates.getD (rep i - n) ⟨GateOp.or, []⟩).inputs) := by
    obtain ⟨j, hji⟩ := exists_ne i
    have htrue : value C (X j) (rep i) = true := by
      rw [hsig i j]
      exact decide_eq_true hji
    have hn : n ≤ rep i := by
      by_contra! h
      let p : Fin n := ⟨rep i, h⟩
      apply hraw p i
      intro t
      have hs := hsig i t
      change value C (X t) p = decide (t ≠ i) at hs
      simpa only [input_value] using hs
    have hw : rep i < n + C.size := by
      by_contra! h
      rw [missing_value C (X j) (rep i) h] at htrue
      contradiction
    refine ⟨Finset.mem_Ico.mpr ⟨hn, hw⟩, hsig i, ?_⟩
    rintro ⟨hzw, hread⟩
    obtain ⟨v, hv, he⟩ := zero_reader_predecessor C hG z hz (rep i) hn hw
      hzw hread (X j) htrue
    apply hmin i v hv
    intro t
    rw [← he (X t)]
    exact hsig i t
  refine ⟨rep, ?_, hprops⟩
  intro i j he
  by_contra hij
  have hi := hsig i i
  have hj := hsig j i
  rw [he] at hi
  have hf : value C (X i) (rep j) = false := by simpa using hi
  rw [hf] at hj
  simp [hij] at hj

end CoLineCount

-- Component ChargeCount.
namespace ChargeCount

lemma five_category_count (U R A E : Finset ℕ) (z h : ℕ)
    (hRU : R ⊆ U) (hzU : z ∈ U) (hhU : h ∈ U)
    (hAU : A ⊆ U) (hEU : E ⊆ U) (hzh : z ≠ h)
    (hzR : z ∉ R) (hhR : h ∉ R)
    (hRA : Disjoint R A) (hRE : Disjoint R E)
    (hzA : z ∉ A) (hhA : h ∉ A)
    (hzE : z ∉ E) (hhE : h ∉ E) (hAE : Disjoint A E) :
    R.card + 2 + A.card + E.card ≤ U.card := by
  classical
  have hZU : ({z, h} : Finset ℕ) ⊆ U := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hzU
    · simpa only [Finset.mem_singleton.mp hw] using hhU
  have hRZ : Disjoint R ({z, h} : Finset ℕ) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwR hwZ
    rcases Finset.mem_insert.mp hwZ with rfl | hwZ
    · exact hzR hwR
    · exact hhR (by simpa only [Finset.mem_singleton.mp hwZ] using hwR)
  have hZA : Disjoint ({z, h} : Finset ℕ) A := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwZ hwA
    rcases Finset.mem_insert.mp hwZ with rfl | hwZ
    · exact hzA hwA
    · exact hhA (by simpa only [Finset.mem_singleton.mp hwZ] using hwA)
  have hZE : Disjoint ({z, h} : Finset ℕ) E := by
    refine Finset.disjoint_left.mpr ?_
    intro w hwZ hwE
    rcases Finset.mem_insert.mp hwZ with rfl | hwZ
    · exact hzE hwE
    · exact hhE (by simpa only [Finset.mem_singleton.mp hwZ] using hwE)
  have hRZA : Disjoint (R ∪ {z, h}) A :=
    Finset.disjoint_union_left.mpr ⟨hRA, hZA⟩
  have hRZAE : Disjoint ((R ∪ {z, h}) ∪ A) E :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_left.mpr ⟨hRE, hZE⟩, hAE⟩
  have hsub : ((R ∪ {z, h}) ∪ A) ∪ E ⊆ U :=
    Finset.union_subset (Finset.union_subset (Finset.union_subset hRU hZU) hAU) hEU
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hRZAE,
    Finset.card_union_of_disjoint hRZA,
    Finset.card_union_of_disjoint hRZ] at hc
  simpa only [Finset.card_pair hzh] using hc

lemma five_category_max_count (U R A E F : Finset ℕ) (a e f : ℕ)
    (hA : a ≤ A.card) (hE : e ≤ E.card) (hF : f ≤ F.card)
    (he : R.card + 2 + A.card + E.card ≤ U.card)
    (hf : R.card + 2 + A.card + F.card ≤ U.card) :
    R.card + 2 + a + max e f ≤ U.card := by omega

end ChargeCount

-- Component CombinedCount.
namespace CombinedCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack
open PEqualNP.Outside.L_meta_1613_aux.OrPrivateCount
open PEqualNP.Outside.L_meta_1613_aux.AnchorCount
open PEqualNP.Outside.L_meta_1613_aux.CoLineCount
open PEqualNP.Outside.L_meta_1613_aux.ChargeCount

noncomputable def directReaders (n : ℕ) (C : Circuit) (z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter fun w =>
    z < w ∧ z ∈ (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs

lemma combined_count {n m q : ℕ} (C : Circuit)
    (L : Fin m → Finset (Fin n)) (B : Fin m → Fin n → Finset (Fin n))
    (Lam : Finset (Fin m)) (out : Fin m → ℕ) (z H : ℕ) (I : Finset ℕ)
    (hm : 2 ≤ m)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = false)
    (hzgate : z ∈ Finset.Ico n (n + C.size))
    (hHgate : H ∈ Finset.Ico n (n + C.size)) (hHz : H < z)
    (hH : ∀ t : Fin m, value C (negative (L t)) H = true)
    (hraw : ∀ (p : Fin n) (i : Fin m),
      ¬ ∀ t : Fin m, negative (L t) p = decide (t ≠ i))
    (hout : ∀ t : Fin m, coSignature C (fun u => negative (L u)) (out t) t)
    (hcard : ∀ t ∈ Lam, (L t).card = q + 1)
    (hB : ∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅)
    (hpos : ∀ t ∈ Lam, ∀ p ∈ L t, value C (anchorSamples L B t p) (out t) = true)
    (hinter : ∀ t t' : Fin m, t ≠ t' → (L t ∩ L t').card ≤ 1)
    (hcross : ∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' →
      ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧
         (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty)))
    (hI : ∀ w ∈ I, w ∈ Finset.Ico n (n + C.size) ∧
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and ∧ w < H) :
    (directReaders n C z).card + 2 + q * Lam.card + max (m - Lam.card) I.card ≤ C.size := by
  classical
  let U := Finset.Ico n (n + C.size)
  let R := directReaders n C z
  let A := Lam.biUnion (anchorCharges C z L B)
  have hneg : ∀ t ∈ Lam, value C (negative (L t)) (out t) = false := by
    intro t _
    have h := hout t t
    simpa using h
  have hAcount : q * Lam.card ≤ A.card :=
    anchor_union_count C z L B Lam out hG hz hcard hB hneg hpos hinter hcross
  obtain ⟨rep, hinj, hrep⟩ :=
    signature_representatives C (fun t => negative (L t)) out z hm hG hz hraw hout
  let J := (Finset.univ : Finset (Fin m)) \ Lam
  let O := J.image rep
  have hOcard : O.card = m - Lam.card := by
    have he : O.card = J.card := Finset.card_image_of_injective J hinj
    have hc := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin m)) Lam
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hc
    change J.card + Lam.card = m at hc
    omega
  have hRU : R ⊆ U := fun _ hw => (Finset.mem_filter.mp hw).1
  have hAU : A ⊆ U := by
    intro w hw
    exact (anchor_union_properties C z L B Lam w hw).1
  have hOU : O ⊆ U := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact (hrep i).1
  have hIU : I ⊆ U := fun w hw => (hI w hw).1
  have hzR : z ∉ R := by
    intro hw
    have h := (Finset.mem_filter.mp hw).2.1
    omega
  have hHR : H ∉ R := by
    intro hw
    have h := (Finset.mem_filter.mp hw).2.1
    omega
  have hzA : z ∉ A := anchor_union_not_z C z L B Lam hz
  have hHA : H ∉ A := anchor_union_not_h C z L B Lam H (fun t _ => hH t)
  have hzO : z ∉ O := by
    intro hw
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hw
    let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    obtain ⟨j, hji⟩ := exists_ne i
    have hs := (hrep i).2.1 j
    rw [he, hz] at hs
    simp [hji] at hs
  have hHO : H ∉ O := by
    intro hw
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hw
    have hs := (hrep i).2.1 i
    rw [he, hH] at hs
    simp at hs
  have hzI : z ∉ I := by
    intro hw
    have h := (hI z hw).2.2
    omega
  have hHI : H ∉ I := by
    intro hw
    exact lt_irrefl H (hI H hw).2.2
  have hRA : Disjoint R A := by
    apply Finset.disjoint_left.mpr
    intro w hwR hwA
    exact (anchor_union_properties C z L B Lam w hwA).2.2.1
      (Finset.mem_filter.mp hwR).2
  have hRO : Disjoint R O := by
    apply Finset.disjoint_left.mpr
    intro w hwR hwO
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hwO
    exact (hrep i).2.2 (Finset.mem_filter.mp hwR).2
  have hRI : Disjoint R I := by
    apply Finset.disjoint_left.mpr
    intro w hwR hwI
    have hr := (Finset.mem_filter.mp hwR).2.1
    have hi := (hI w hwI).2.2
    omega
  have hAO : Disjoint A O := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwO
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hwO
    obtain ⟨t, ht, hfalse⟩ := (anchor_union_properties C z L B Lam (rep i) hwA).2.2.2
    have hinot := (Finset.mem_sdiff.mp hi).2
    have hti : t ≠ i := by intro he; subst t; exact hinot ht
    have hs := (hrep i).2.1 t
    rw [hfalse] at hs
    simp [hti] at hs
  have hAI : Disjoint A I := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwI
    have ha := (anchor_union_properties C z L B Lam w hwA).2.1
    rw [(hI w hwI).2.1] at ha
    cases ha
  have hO := five_category_count U R A O z H hRU hzgate hHgate hAU hOU
    (by omega) hzR hHR hRA hRO hzA hHA hzO hHO hAO
  have hIcount := five_category_count U R A I z H hRU hzgate hHgate hAU hIU
    (by omega) hzR hHR hRA hRI hzA hHA hzI hHI hAI
  have hc := five_category_max_count U R A O I (q * Lam.card) (m - Lam.card) I.card
    hAcount (by omega) le_rfl hO hIcount
  simpa [U, R] using hc

end CombinedCount

-- Component ReplacementBridge.
namespace ReplacementBridge

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack
open PEqualNP.Outside.L_meta_1613_aux.HeavyReplacement

lemma value_output_irrel {n : ℕ} (gates : List Gate) (o o' w : ℕ)
    (x : Fin n → Bool) : value ⟨gates, o⟩ x w = value ⟨gates, o'⟩ x w := rfl

lemma eval_eq_value {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gates, w⟩ (List.ofFn x) = value ⟨gates, 0⟩ x w := rfl

lemma false_replacement_setup {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j) :
    (repl0C gates j.val).size = gates.length ∧
      (∀ g ∈ (repl0C gates j.val).gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool, value (repl0C gates j.val) x (n + j.val) = false :=
  ⟨repl0C_size gates j.val, repl0C_gates gates j hgate hnot,
    repl0C_false gates j⟩

lemma not_false_of_h_true {n : ℕ} (gates : List Gate)
    (j h : Fin gates.length)
    (hop : (gates.get j).op = GateOp.not) (hhj : h < j)
    (hhead : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (x : Fin n → Bool)
    (hx : Circuit.eval ⟨gates, n + h.val⟩ (List.ofFn x) = true) :
    value ⟨gates, 0⟩ x (n + j.val) = false := by
  obtain ⟨r, hr⟩ := hhead
  have hh : (gates.get j).inputs.head? = some (n + h.val) := by rw [hr]; rfl
  rw [orig_not_value gates j 0 (n + h.val) hop hh (by omega) x]
  change value ⟨gates, 0⟩ x (n + h.val) = true at hx
  rw [hx]
  rfl

lemma replacement_agrees_of_h_true {n : ℕ} (gates : List Gate)
    (j h : Fin gates.length)
    (hop : (gates.get j).op = GateOp.not) (hhj : h < j)
    (hhead : ∃ r : List ℕ, (gates.get j).inputs = (n + h.val) :: r)
    (x : Fin n → Bool)
    (hx : Circuit.eval ⟨gates, n + h.val⟩ (List.ofFn x) = true)
    (w : ℕ) :
    value (repl0C gates j.val) x w = value ⟨gates, 0⟩ x w :=
  repl0C_eq gates j 0 x (not_false_of_h_true gates j h hop hhj hhead x hx) w

lemma replacement_h_eq {n : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (hhj : h < j) (x : Fin n → Bool) :
    value (repl0C gates j.val) x (n + h.val) =
      Circuit.eval ⟨gates, n + h.val⟩ (List.ofFn x) := by
  exact repl0C_prefix_eq gates j (n + h.val) x (n + h.val) (by omega)

lemma replacement_h_true {n r : ℕ} (gates : List Gate) (j h : Fin gates.length)
    (hhj : h < j) (X : Fin r → Fin n → Bool)
    (hX : ∀ t : Fin r,
      Circuit.eval ⟨gates, n + h.val⟩ (List.ofFn (X t)) = true) :
    ∀ t : Fin r, value (repl0C gates j.val) (X t) (n + h.val) = true := by
  intro t
  rw [replacement_h_eq gates j h hhj (X t), hX t]

lemma replacement_gate_eq (gates : List Gate) (j i : Fin gates.length)
    (hij : i ≠ j) :
    (repl0C gates j.val).gates.get ⟨i.val, by simp [repl0C]⟩ = gates.get i := by
  have hne : j.val ≠ i.val := by
    intro he
    exact hij (Fin.ext he.symm)
  simp [repl0C, hne]

lemma replacement_getD_eq (gates : List Gate) (j i : Fin gates.length)
    (hij : i ≠ j) :
    (repl0C gates j.val).gates.getD i.val ⟨GateOp.or, []⟩ = gates.get i := by
  have hi : i.val < (repl0C gates j.val).gates.length := by simp [repl0C]
  rw [List.getD_eq_getElem _ _ hi]
  exact replacement_gate_eq gates j i hij

lemma replacement_op_eq (gates : List Gate) (j i : Fin gates.length)
    (hij : i ≠ j) :
    ((repl0C gates j.val).gates.getD i.val ⟨GateOp.or, []⟩).op =
      (gates.get i).op := by
  rw [replacement_getD_eq gates j i hij]

lemma replacement_inputs_eq (gates : List Gate) (j i : Fin gates.length)
    (hij : i ≠ j) :
    ((repl0C gates j.val).gates.getD i.val ⟨GateOp.or, []⟩).inputs =
      (gates.get i).inputs := by
  rw [replacement_getD_eq gates j i hij]

lemma replacement_reader_iff (n : ℕ) (gates : List Gate) (j i : Fin gates.length) :
    (n + j.val < n + i.val ∧ n + j.val ∈
      ((repl0C gates j.val).gates.getD i.val ⟨GateOp.or, []⟩).inputs) ↔
      j < i ∧ n + j.val ∈ (gates.get i).inputs := by
  by_cases hji : j < i
  · have hij : i ≠ j := by intro he; subst i; exact (lt_irrefl j hji)
    rw [replacement_inputs_eq gates j i hij]
    simp only [Nat.add_lt_add_iff_left]
    rfl
  · have hnat : ¬ (n + j.val < n + i.val) := by omega
    simp [hji, hnat]

end ReplacementBridge

-- Component WireIndex.
namespace WireIndex

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack
open PEqualNP.Outside.L_meta_1613_aux.HeavyReplacement
open PEqualNP.Outside.L_meta_1613_aux.ReplacementBridge
open PEqualNP.Outside.L_meta_1613_aux.CombinedCount

lemma wire_image_card {s : ℕ} (n : ℕ) (I : Finset (Fin s)) :
    (I.image (fun i : Fin s => n + i.val)).card = I.card := by
  apply Finset.card_image_of_injective
  intro i j h
  apply Fin.ext
  change n + i.val = n + j.val at h
  omega

lemma wire_image_subset {s : ℕ} (n : ℕ) (I : Finset (Fin s)) :
    I.image (fun i : Fin s => n + i.val) ⊆ Finset.Ico n (n + s) := by
  intro w hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
  exact Finset.mem_Ico.mpr ⟨by omega, by have := i.isLt; omega⟩

lemma directReaders_replacement_image (n : ℕ) (gates : List Gate)
    (j : Fin gates.length) :
    directReaders n (repl0C gates j.val) (n + j.val) =
      (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + j.val ∈ (gates.get i).inputs)).image
          (fun i : Fin gates.length => n + i.val) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨hwU, hr⟩ := Finset.mem_filter.mp hw
    obtain ⟨hn, hwlt⟩ := Finset.mem_Ico.mp hwU
    rw [repl0C_size] at hwlt
    let i : Fin gates.length := ⟨w - n, by omega⟩
    have he : w = n + i.val := by dsimp [i]; omega
    have hr' : n + j.val < n + i.val ∧ n + j.val ∈
        ((repl0C gates j.val).gates.getD i.val ⟨GateOp.or, []⟩).inputs := by
      simpa only [he, Nat.add_sub_cancel_left] using hr
    have hi := (replacement_reader_iff n gates j i).mp hr'
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, he.symm⟩
  · intro hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hr := (replacement_reader_iff n gates j i).mpr (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
    · rw [repl0C_size]
      have := i.isLt
      omega
    · simpa only [Nat.add_sub_cancel_left] using hr

lemma directReaders_replacement_card (n : ℕ) (gates : List Gate)
    (j : Fin gates.length) :
    (directReaders n (repl0C gates j.val) (n + j.val)).card =
      (Finset.univ.filter (fun i : Fin gates.length =>
        j < i ∧ n + j.val ∈ (gates.get i).inputs)).card := by
  rw [directReaders_replacement_image, wire_image_card]

end WireIndex

end PEqualNP.Outside.L_meta_1613_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1613_aux.MintermSlack
open PEqualNP.Outside.L_meta_1613_aux.OrPrivateCount
open PEqualNP.Outside.L_meta_1613_aux.HeavyReplacement
open PEqualNP.Outside.L_meta_1613_aux.AnchorCount
open PEqualNP.Outside.L_meta_1613_aux.CoLineCount
open PEqualNP.Outside.L_meta_1613_aux.CombinedCount
open PEqualNP.Outside.L_meta_1613_aux.PlaneGeometry
open PEqualNP.Outside.L_meta_1613_aux.ReplacementBridge
open PEqualNP.Outside.L_meta_1613_aux.WireIndex

theorem PEqualNP.Outside.L_meta_1613 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) → (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (N + (h : ℕ)) :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∀ t : Fin N, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L t))) = true) →
    ∀ (Lam : Finset (Fin N)) (B : Fin N → Fin N → Finset (Fin N)),
    (∀ t ∈ Lam, ∀ p ∈ L t, B t p ∩ L t = ∅ ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, N + (h : ℕ)⟩ (List.ofFn (fun v : Fin N => decide (v = p ∨ v ∈ B t p))) = true) →
    (∀ t ∈ Lam, ∀ t' ∈ Lam, t ≠ t' → ¬ ((∃ p ∈ L t \ L t', (B t p ∩ L t').Nonempty) ∧ (∃ p ∈ L t' \ L t, (B t' p ∩ L t).Nonempty))) →
    ∀ I : Finset (Fin gates.length),
      (∀ g ∈ I, (gates.get g).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∀ T : Finset (Fin gates.length), (∀ i g' : Fin gates.length, (i = h ∨ i ∈ T) →
          N + (g' : ℕ) ∈ (gates.get i).inputs → g' < i → g' ∈ T) → g ∈ T) →
      (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ N + (j : ℕ) ∈ (gates.get i).inputs)).card + 2 + q * Lam.card + max (N - Lam.card) I.card ≤ gates.length := by
  classical
  intro q N L hq hN hcard hinter hpoints gates o j h hgate _hwell hjop honly hhj hhead hout hhcol
    Lam B hB hcross I hI
  let D := repl0C gates j.val
  obtain ⟨hsize, hG, hz⟩ := false_replacement_setup (n := N) gates j hgate honly
  change D.size = gates.length at hsize
  change (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) at hG
  change ∀ x : Fin N → Bool, value D x (N + j.val) = false at hz
  have hDh : ∀ t : Fin N, value D (negative (L t)) (N + h.val) = true := by
    intro t
    rw [replacement_h_eq gates j h hhj]
    exact hhcol t
  have hDout : ∀ t : Fin N, coSignature D (fun u => negative (L u)) (o t) t := by
    intro t u
    rw [replacement_agrees_of_h_true gates j h hjop hhj hhead
      (negative (L u)) (hhcol u) (o t)]
    change Circuit.eval ⟨gates, o t⟩ (List.ofFn (negative (L u))) = decide (u ≠ t)
    rw [hout]
    exact line_or_coLine L hq hcard hinter t u
  have hDpos : ∀ t ∈ Lam, ∀ p ∈ L t,
      value D (anchorSamples L B t p) (o t) = true := by
    intro t ht p hp
    have hs : anchorSamples L B t p = (fun v => decide (v = p ∨ v ∈ B t p)) := by
      funext v
      simp only [anchorSamples, ite_eq_left hp]
    rw [hs]
    rw [replacement_agrees_of_h_true gates j h hjop hhj hhead
      (fun v => decide (v = p ∨ v ∈ B t p)) (hB t ht p hp).2 (o t)]
    change Circuit.eval ⟨gates, o t⟩
      (List.ofFn (fun v => decide (v = p ∨ v ∈ B t p))) = true
    rw [hout]
    exact decide_eq_true ⟨p, hp, by simp⟩
  have hzgate : N + j.val ∈ Finset.Ico N (N + D.size) := by
    apply Finset.mem_Ico.mpr
    rw [hsize]
    exact ⟨by omega, Nat.add_lt_add_left j.isLt N⟩
  have hHgate : N + h.val ∈ Finset.Ico N (N + D.size) := by
    apply Finset.mem_Ico.mpr
    rw [hsize]
    exact ⟨by omega, Nat.add_lt_add_left h.isLt N⟩
  let Iw : Finset ℕ := I.image (fun i => N + i.val)
  have hIlt := ancestor_set_lt (N := N) gates h I hI
  have hIw : ∀ w ∈ Iw, w ∈ Finset.Ico N (N + D.size) ∧
      (D.gates.getD (w - N) ⟨GateOp.or, []⟩).op = GateOp.and ∧ w < N + h.val := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hih := hIlt i hi
    have hij : i ≠ j := by
      intro he
      subst i
      exact (lt_irrefl j (lt_trans hih hhj))
    refine ⟨?_, ?_, Nat.add_lt_add_left hih N⟩
    · apply Finset.mem_Ico.mpr
      rw [hsize]
      exact ⟨by omega, Nat.add_lt_add_left i.isLt N⟩
    · simp only [Nat.add_sub_cancel_left]
      exact (replacement_op_eq gates j i hij).trans (hI i hi).1
  have hcount := combined_count D L B Lam o (N + j.val) (N + h.val) Iw
    (by have := (plane_size hq hN).2; omega) hG hz hzgate hHgate
    (Nat.add_lt_add_left hhj N) hDh
    (no_raw_coSignature L hq hN hcard hpoints) hDout
    (fun t _ => hcard t) (fun t ht p hp => (hB t ht p hp).1) hDpos
    (fun t t' hne => by rw [hinter t t' hne]) hcross hIw
  have hIcard : Iw.card = I.card := wire_image_card N I
  have hRcard := directReaders_replacement_card N gates j
  change (directReaders N D (N + j.val)).card = _ at hRcard
  rw [hIcard, hRcard, hsize] at hcount
  exact hcount
