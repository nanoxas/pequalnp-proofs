import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext
import PEqualNP.Defs

namespace PEqualNP.Research.MintermSlack

-- Circuit evaluation, monotonicity, and cut helpers below reuse accepted L-meta-986.
-- The empty-support branch count is a new adaptation for the current research.
-- The source repository and this adaptation use the Apache-2.0 license.
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

theorem small_witness {n : ℕ} (C : Circuit)
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

theorem minterm_bound {n : ℕ} (C : Circuit)
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

end PEqualNP.Research.MintermSlack

#print axioms PEqualNP.Research.MintermSlack.small_witness
#print axioms PEqualNP.Research.MintermSlack.minterm_bound

