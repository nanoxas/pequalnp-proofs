import MintermSlack

namespace PEqualNP.Research.CoupledCut

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

def ports (n : ℕ) (C : Circuit) (w : ℕ) : Finset ℕ :=
  ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs.toFinset).filter (· < w)

lemma ports_lt (n : ℕ) (C : Circuit) (w : ℕ) :
    ∀ r ∈ ports n C w, r < w := by
  intro r hr
  exact (Finset.mem_filter.mp hr).2

lemma ports_card {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    (ports n C w).card ≤ 2 := by
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  have hlen : (C.gates.getD (w - n) ⟨GateOp.or, []⟩).inputs.length ≤ 2 := by
    rw [List.getD_eq_getElem _ _ hj]
    exact (hG _ (List.getElem_mem hj)).2
  exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)

lemma positive_ports {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (y : Fin n → Bool) (hy : value C y w = true) :
    ∃ Q : Finset ℕ, Q ⊆ ports n C w ∧
      (Q.card ≤ 1 ∨
        ((C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and ∧ Q.card ≤ 2)) ∧
      (∀ r ∈ Q, value C y r = true) ∧
      ∀ x : Fin n → Bool, (∀ r ∈ Q, value C x r = true) → value C x w = true := by
  classical
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  have hget : C.gates.getD (w - n) ⟨GateOp.or, []⟩ = g :=
    List.getD_eq_getElem _ _ hj
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem hj)
  have form (x : Fin n → Bool) : value C x w =
      g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
    gate_value C x w hn hw
  have memP (r : ℕ) : r ∈ ports n C w ↔ r ∈ g.inputs ∧ r < w := by
    simp only [ports, hget, Finset.mem_filter, List.mem_toFinset]
  have read_true (r : ℕ) (hr : (if r < w then value C y r else false) = true) :
      r < w ∧ value C y r = true := by
    by_cases h : r < w
    · exact ⟨h, by simpa only [ite_eq_left h] using hr⟩
    · simp only [ite_eq_right h, Bool.false_eq_true] at hr
  rcases hop with hand | hor
  · have hall : ∀ r ∈ g.inputs, r < w ∧ value C y r = true := by
      have h := hy
      rw [form] at h
      simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq] at h
      intro r hr
      exact read_true r (h r hr)
    refine ⟨ports n C w, Finset.Subset.refl _, Or.inr ?_, ?_, ?_⟩
    · exact ⟨by simpa only [hget] using hand, ports_card C hG w hn hw⟩
    · intro r hr
      exact (hall r ((memP r).mp hr).1).2
    · intro x hx
      rw [form]
      simp only [hand, GateOp.eval, List.all_map, List.all_eq_true,
        Function.comp_apply, id_eq]
      intro r hr
      rw [ite_eq_left (hall r hr).1]
      exact hx r ((memP r).mpr ⟨hr, (hall r hr).1⟩)
  · have h := hy
    rw [form] at h
    simp only [hor, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at h
    obtain ⟨r, hr, hv⟩ := h
    obtain ⟨hrw, hry⟩ := read_true r hv
    refine ⟨{r}, ?_, Or.inl (by simp), ?_, ?_⟩
    · intro s hs
      have he := Finset.mem_singleton.mp hs
      subst s
      exact (memP r).mpr ⟨hr, hrw⟩
    · intro s hs
      simpa only [Finset.mem_singleton.mp hs] using hry
    · intro x hx
      rw [form]
      simp only [hor, GateOp.eval, List.any_map, List.any_eq_true,
        Function.comp_apply, id_eq]
      exact ⟨r, hr, by simpa only [ite_eq_left hrw] using hx r (Finset.mem_singleton_self r)⟩

lemma filter_lt_mono_card (T : Finset ℕ) (t : ℕ) :
    (T.filter (· < t)).card ≤ (T.filter (· < t + 1)).card := by
  apply Finset.card_le_card
  intro w hw
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
    by have := (Finset.mem_filter.mp hw).2; omega⟩

lemma filter_lt_succ (T : Finset ℕ) (t : ℕ) (ht : t ∈ T) :
    T.filter (· < t + 1) = insert t (T.filter (· < t)) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hw, hlt⟩
    by_cases he : w = t
    · exact Or.inl he
    · exact Or.inr ⟨hw, by omega⟩
  · rintro (rfl | ⟨hw, hlt⟩)
    · exact ⟨ht, by omega⟩
    · exact ⟨hw, by omega⟩

theorem coupled_cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G A : Finset ℕ)
    (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (hA : ∀ w ∈ G,
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and → w ∈ A)
    (t : ℕ) (F : Finset ℕ) (hFt : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧
      B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ (y : Fin n → Bool) (P0 : Finset ℕ), P0 ⊆ F →
        (∀ w ∈ P0, value C y w = true) →
        ∃ P : Finset ℕ, P ⊆ B ∧
          P.card ≤ P0.card + (A.filter (· < t)).card ∧
          (∀ w ∈ P, value C y w = true) ∧
          ∀ x : Fin n → Bool, (∀ w ∈ P, value C x w = true) →
            ∀ w ∈ P0, value C x w = true := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, ?_, by simp, ?_⟩
    · apply Finset.disjoint_left.mpr
      intro w hwF hwG
      have := hFt w hwF hwG
      omega
    · intro y P0 hP0 hPy
      exact ⟨P0, hP0, by simp, hPy, fun _ hx => hx⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · let Q := ports n C t
      let F' := F.erase t ∪ Q
      have hQt : ∀ w ∈ Q, w < t := ports_lt n C t
      have hQc : Q.card ≤ 2 :=
        ports_card C hG t (hGates t hex.2).1 (hGates t hex.2).2
      have hF't : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hwG
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFt w (Finset.mem_erase.mp hw).2 hwG
          omega
        · exact hQt w hw
      obtain ⟨B, hBG, hBc, hBpos⟩ := ih F' hF't
      refine ⟨B, hBG, ?_, ?_⟩
      · have hu := Finset.card_union_le (F.erase t) Q
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        rw [filter_lt_succ G t hex.2,
          Finset.card_insert_of_notMem (by simp)]
        omega
      · intro y P0 hP0F hP0y
        by_cases htP0 : t ∈ P0
        · obtain ⟨Qp, hQpQ, hQpc, hQpy, hQforce⟩ :=
            positive_ports C hG t (hGates t hex.2).1 (hGates t hex.2).2 y (hP0y t htP0)
          let P1 := P0.erase t ∪ Qp
          have hP1F' : P1 ⊆ F' := by
            intro w hw
            rcases Finset.mem_union.mp hw with hw | hw
            · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
                ⟨(Finset.mem_erase.mp hw).1, hP0F (Finset.mem_erase.mp hw).2⟩)
            · exact Finset.mem_union_right _ (hQpQ hw)
          have hP1y : ∀ w ∈ P1, value C y w = true := by
            intro w hw
            rcases Finset.mem_union.mp hw with hw | hw
            · exact hP0y w (Finset.mem_erase.mp hw).2
            · exact hQpy w hw
          obtain ⟨P, hPB, hPc, hPy, hforce⟩ := hBpos y P1 hP1F' hP1y
          refine ⟨P, hPB, ?_, hPy, ?_⟩
          · have hu := Finset.card_union_le (P0.erase t) Qp
            have he := Finset.card_erase_add_one htP0
            change P1.card ≤ _ at hu
            rcases hQpc with hsmall | ⟨hand, htwo⟩
            · have hm := filter_lt_mono_card A t
              omega
            · have htA := hA t hex.2 hand
              rw [filter_lt_succ A t htA,
                Finset.card_insert_of_notMem (by simp)]
              omega
          · intro x hx w hw
            by_cases hwt : w = t
            · subst w
              apply hQforce x
              intro r hr
              exact hforce x hx r (Finset.mem_union_right _ hr)
            · exact hforce x hx w
                (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩))
        · have hP0F' : P0 ⊆ F' := by
            intro w hw
            have hwt : w ≠ t := by intro he; subst w; exact htP0 hw
            exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hP0F hw⟩)
          obtain ⟨P, hPB, hPc, hPy, hforce⟩ := hBpos y P0 hP0F' hP0y
          have hm := filter_lt_mono_card A t
          exact ⟨P, hPB, by omega, hPy, hforce⟩
    · have hFt' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hwG
        have hwt : w ≠ t := by intro he; subst w; exact hex ⟨hw, hwG⟩
        have hlt := hFt w hw hwG
        omega
      obtain ⟨B, hBG, hBc, hBpos⟩ := ih F hFt'
      have hGmono := filter_lt_mono_card G t
      refine ⟨B, hBG, by omega, ?_⟩
      intro y P0 hP0F hP0y
      obtain ⟨P, hPB, hPc, hPy, hforce⟩ := hBpos y P0 hP0F hP0y
      have hAmono := filter_lt_mono_card A t
      exact ⟨P, hPB, by omega, hPy, hforce⟩

end PEqualNP.Research.CoupledCut

#print axioms PEqualNP.Research.CoupledCut.coupled_cut
