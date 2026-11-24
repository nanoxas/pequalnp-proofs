import MintermSlack

/-
An OR-only refinement of the accepted L-meta-988 private-gate count.
The reverse frontier argument follows MintermSlack, with false propagation
at one fixed negative input. At AND only one false child is needed; OR is
the charged branching operation. All adaptations are Apache-2.0.
-/

namespace PEqualNP.Research.OrPrivateCount

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

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

/-- A negative input and single-source positive samples force OR branches. -/
theorem sample_or_prefix_count {n r : ℕ} (C : Circuit)
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

theorem sample_or_count {n r : ℕ} (C : Circuit)
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

/-- The heavy-input private count can charge only OR gates, and only gates
at or before the selected output. -/
theorem heavy_or_prefix_count {n : ℕ} (C : Circuit)
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

theorem heavy_or_count {n : ℕ} (C : Circuit)
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

/-- The OR-only private charges are disjoint across a linear heavy family. -/
theorem heavy_or_sum_bound {n m : ℕ} (C : Circuit)
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

end PEqualNP.Research.OrPrivateCount

#print axioms PEqualNP.Research.OrPrivateCount.sample_or_count
#print axioms PEqualNP.Research.OrPrivateCount.heavy_or_prefix_count
#print axioms PEqualNP.Research.OrPrivateCount.heavy_or_sum_bound
