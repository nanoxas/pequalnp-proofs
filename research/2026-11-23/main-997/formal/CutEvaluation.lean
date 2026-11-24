import CoupledCut
import OrCompensation

namespace PEqualNP.Research.CutEvaluation

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.CoupledCut
open PEqualNP.Research.OrCompensation

def Admissible (n : ℕ) (C : Circuit) (G : Finset ℕ) (v : ℕ → Bool) : Prop :=
  ∀ w ∈ G, v w = (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op.eval
    ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs.map
      fun r => if r < w then v r else false)

def cutValue (n : ℕ) (C : Circuit) (G : Finset ℕ) (b : ℕ → Bool) (w : ℕ) : Bool :=
  if w ∈ G then
    (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op.eval
      ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs.map
        fun r => if _h : r < w then cutValue n C G b r else false)
  else b w
termination_by w

lemma cutValue_admissible (n : ℕ) (C : Circuit) (G : Finset ℕ) (b : ℕ → Bool) :
    Admissible n C G (cutValue n C G b) := by
  intro w hw
  rw [cutValue, ite_eq_left hw]
  simp only [dite_eq_ite]

lemma cutValue_boundary (n : ℕ) (C : Circuit) (G : Finset ℕ)
    (b : ℕ → Bool) (w : ℕ) (hw : w ∉ G) : cutValue n C G b w = b w := by
  rw [cutValue, ite_eq_right hw]

lemma actual_admissible {n : ℕ} (C : Circuit) (G : Finset ℕ)
    (hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size) (x : Fin n → Bool) :
    Admissible n C G (value C x) := by
  intro w hw
  obtain ⟨hn, hlt⟩ := hgate w hw
  have hj : w - n < C.gates.length := by unfold Circuit.size at hlt; omega
  rw [List.getD_eq_getElem _ _ hj]
  exact gate_value C x w hn hlt

lemma gate_shape {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and ∨
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.or) ∧
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs.length ≤ 2 := by
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  rw [List.getD_eq_getElem _ _ hj]
  exact hG _ (List.getElem_mem hj)

lemma admissible_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (v u : ℕ → Bool) (hv : Admissible n C G v) (hu : Admissible n C G u)
    (hboundary : ∀ w, w ∉ G → v w = true → u w = true) :
    ∀ w, v w = true → u w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hval
    by_cases hw : w ∈ G
    · obtain ⟨hop, _⟩ := gate_shape C hG w (hgate w hw).1 (hgate w hw).2
      have hform := hv w hw
      have uform := hu w hw
      rw [hform] at hval
      rw [uform]
      rcases hop with hand | hor
      · simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
          Function.comp_apply, id_eq] at hval ⊢
        intro r hr
        have hvtrue := hval r hr
        by_cases hrw : r < w
        · rw [ite_eq_left hrw]
          exact ih r hrw (by simpa only [ite_eq_left hrw] using hvtrue)
        · simp only [ite_eq_right hrw, Bool.false_eq_true] at hvtrue
      · simp only [hor, GateOp.eval, List.any_map, List.any_eq_true,
          Function.comp_apply, id_eq] at hval ⊢
        obtain ⟨r, hr, hvtrue⟩ := hval
        by_cases hrw : r < w
        · exact ⟨r, hr, by
            rw [ite_eq_left hrw]
            exact ih r hrw (by simpa only [ite_eq_left hrw] using hvtrue)⟩
        · simp only [ite_eq_right hrw, Bool.false_eq_true] at hvtrue
    · exact hboundary w hw hval

def branchOp (b : Bool) : GateOp := if b then GateOp.and else GateOp.or

lemma admissible_positive_ports {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (v : ℕ → Bool) (hv : Admissible n C G v)
    (w : ℕ) (hw : w ∈ G) (hval : v w = true) :
    ∃ Q : Finset ℕ, Q ⊆ ports n C w ∧
      (Q.card ≤ 1 ∨
        ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and ∧ Q.card ≤ 2)) ∧
      (∀ r ∈ Q, v r = true) ∧
      ∀ u : ℕ → Bool, Admissible n C G u →
        (∀ r ∈ Q, u r = true) → u w = true := by
  classical
  let g := C.gates.getD (w - n) ⟨GateOp.or, []⟩
  obtain ⟨hop, _⟩ := gate_shape C hG w (hgate w hw).1 (hgate w hw).2
  have memP (r : ℕ) : r ∈ ports n C w ↔ r ∈ g.inputs ∧ r < w := by
    simp only [ports, g, Finset.mem_filter, List.mem_toFinset]
  have read_true (r : ℕ) (hr : (if r < w then v r else false) = true) :
      r < w ∧ v r = true := by
    by_cases h : r < w
    · exact ⟨h, by simpa only [ite_eq_left h] using hr⟩
    · simp only [ite_eq_right h, Bool.false_eq_true] at hr
  rcases hop with hand | hor
  · have hall : ∀ r ∈ g.inputs, r < w ∧ v r = true := by
      rw [hv w hw] at hval
      simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at hval
      intro r hr
      exact read_true r (hval r hr)
    refine ⟨ports n C w, Finset.Subset.refl _,
      Or.inr ⟨hand, ports_card C hG w (hgate w hw).1 (hgate w hw).2⟩, ?_, ?_⟩
    · intro r hr
      exact (hall r ((memP r).mp hr).1).2
    · intro u hu hx
      rw [hu w hw]
      simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq]
      intro r hr
      rw [ite_eq_left (hall r hr).1]
      exact hx r ((memP r).mpr ⟨hr, (hall r hr).1⟩)
  · rw [hv w hw] at hval
    simp only [hor, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hval
    obtain ⟨r, hr, hvtrue⟩ := hval
    obtain ⟨hrw, hrtrue⟩ := read_true r hvtrue
    refine ⟨{r}, ?_, Or.inl (by simp), ?_, ?_⟩
    · intro s hs
      have he := Finset.mem_singleton.mp hs
      subst s
      exact (memP r).mpr ⟨hr, hrw⟩
    · intro s hs
      simpa only [Finset.mem_singleton.mp hs] using hrtrue
    · intro u hu hx
      rw [hu w hw]
      simp only [hor, GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq]
      exact ⟨r, hr, by simpa only [ite_eq_left hrw] using hx r (Finset.mem_singleton_self r)⟩

lemma admissible_negative_ports {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (v : ℕ → Bool) (hv : Admissible n C G v)
    (w : ℕ) (hw : w ∈ G) (hval : v w = false) :
    ∃ Q : Finset ℕ, Q ⊆ ports n C w ∧
      (Q.card ≤ 1 ∨
        ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.or ∧ Q.card ≤ 2)) ∧
      (∀ r ∈ Q, v r = false) ∧
      ∀ u : ℕ → Bool, Admissible n C G u →
        (∀ r ∈ Q, u r = false) → u w = false := by
  classical
  let g := C.gates.getD (w - n) ⟨GateOp.or, []⟩
  obtain ⟨hop, _⟩ := gate_shape C hG w (hgate w hw).1 (hgate w hw).2
  have memP (r : ℕ) : r ∈ ports n C w ↔ r ∈ g.inputs ∧ r < w := by
    simp only [ports, g, Finset.mem_filter, List.mem_toFinset]
  rcases hop with hand | hor
  · rw [hv w hw] at hval
    simp only [hand, GateOp.eval, List.all_map, List.all_eq_false,
      Function.comp_apply, id_eq, Bool.not_eq_true] at hval
    obtain ⟨r, hr, hvfalse⟩ := hval
    by_cases hrw : r < w
    · have hrfalse : v r = false := by simpa only [ite_eq_left hrw] using hvfalse
      refine ⟨{r}, ?_, Or.inl (by simp), ?_, ?_⟩
      · intro s hs
        have he := Finset.mem_singleton.mp hs
        subst s
        exact (memP r).mpr ⟨hr, hrw⟩
      · intro s hs
        simpa only [Finset.mem_singleton.mp hs] using hrfalse
      · intro u hu hx
        apply Bool.eq_false_iff.mpr
        intro htrue
        rw [hu w hw] at htrue
        simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
          Function.comp_apply, id_eq] at htrue
        have h := htrue r hr
        rw [ite_eq_left hrw, hx r (Finset.mem_singleton_self r)] at h
        contradiction
    · refine ⟨∅, Finset.empty_subset _, Or.inl (by simp), by simp, ?_⟩
      intro u hu _
      apply Bool.eq_false_iff.mpr
      intro htrue
      rw [hu w hw] at htrue
      simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at htrue
      have h := htrue r hr
      simp only [ite_eq_right hrw, Bool.false_eq_true] at h
  · rw [hv w hw] at hval
    simp only [hor, GateOp.eval, List.any_map, List.any_eq_false,
      Function.comp_apply, id_eq, Bool.not_eq_true] at hval
    refine ⟨ports n C w, Finset.Subset.refl _,
      Or.inr ⟨hor, ports_card C hG w (hgate w hw).1 (hgate w hw).2⟩, ?_, ?_⟩
    · intro r hr
      obtain ⟨hrg, hrw⟩ := (memP r).mp hr
      simpa only [ite_eq_left hrw] using hval r hrg
    · intro u hu hx
      rw [hu w hw]
      simp only [hor, GateOp.eval, List.any_map, List.any_eq_false,
        Function.comp_apply, id_eq, Bool.not_eq_true]
      intro r hr
      by_cases hrw : r < w
      · rw [ite_eq_left hrw]
        exact hx r ((memP r).mpr ⟨hr, hrw⟩)
      · simp only [ite_eq_right hrw]

lemma admissible_choice {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (v : ℕ → Bool) (hv : Admissible n C G v)
    (b : Bool) (w : ℕ) (hw : w ∈ G) (hval : v w = b) :
    ∃ Q : Finset ℕ, Q ⊆ ports n C w ∧
      (Q.card ≤ 1 ∨
        ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = branchOp b ∧ Q.card ≤ 2)) ∧
      (∀ r ∈ Q, v r = b) ∧
      ∀ u : ℕ → Bool, Admissible n C G u →
        (∀ r ∈ Q, u r = b) → u w = b := by
  cases b
  · simpa only [branchOp, Bool.false_eq_true, ite_false] using
      admissible_negative_ports C hG G hgate v hv w hw hval
  · simpa only [branchOp, ite_true] using
      admissible_positive_ports C hG G hgate v hv w hw hval

theorem admissible_frontier {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (v : ℕ → Bool) (hv : Admissible n C G v) (b : Bool)
    (t : ℕ) (F : Finset ℕ) (hFb : ∀ w ∈ F, v w = b)
    (hFt : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧
      B.card ≤ F.card + ((opPart n C (branchOp b) G).filter (· < t)).card ∧
      (∀ w ∈ B, v w = b) ∧
      ∀ u : ℕ → Bool, Admissible n C G u →
        (∀ w ∈ B, u w = b) → ∀ w ∈ F, u w = b := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, ?_, by simp, hFb, fun _ _ hx => hx⟩
    apply Finset.disjoint_left.mpr
    intro w hwF hwG
    have := hFt w hwF hwG
    omega
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨Q, hQP, hQc, hQb, hQforce⟩ :=
        admissible_choice C hG G hgate v hv b t hex.2 (hFb t hex.1)
      let F' := F.erase t ∪ Q
      have hF'b : ∀ w ∈ F', v w = b := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFb w (Finset.mem_erase.mp hw).2
        · exact hQb w hw
      have hF't : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hwG
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFt w (Finset.mem_erase.mp hw).2 hwG
          omega
        · exact ports_lt n C t w (hQP hw)
      obtain ⟨B, hd, hc, hb, hforce⟩ := ih F' hF'b hF't
      refine ⟨B, hd, ?_, hb, ?_⟩
      · have hu := Finset.card_union_le (F.erase t) Q
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        rcases hQc with hsmall | ⟨hop, htwo⟩
        · have hm := filter_lt_mono_card (opPart n C (branchOp b) G) t
          omega
        · have htA : t ∈ opPart n C (branchOp b) G :=
            Finset.mem_filter.mpr ⟨hex.2, hop⟩
          rw [filter_lt_succ _ t htA, Finset.card_insert_of_notMem (by simp)]
          omega
      · intro u hu hx w hw
        by_cases hwt : w = t
        · subst w
          apply hQforce u hu
          intro r hr
          exact hforce u hu hx r (Finset.mem_union_right _ hr)
        · exact hforce u hu hx w
            (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩))
    · have hFt' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hwG
        have hwt : w ≠ t := by intro he; subst w; exact hex ⟨hw, hwG⟩
        have hlt := hFt w hw hwG
        omega
      obtain ⟨B, hd, hc, hb, hforce⟩ := ih F hFb hFt'
      have hm := filter_lt_mono_card (opPart n C (branchOp b) G) t
      exact ⟨B, hd, by omega, hb, hforce⟩

end PEqualNP.Research.CutEvaluation

#print axioms PEqualNP.Research.CutEvaluation.cutValue_admissible
#print axioms PEqualNP.Research.CutEvaluation.admissible_mono
#print axioms PEqualNP.Research.CutEvaluation.admissible_frontier
