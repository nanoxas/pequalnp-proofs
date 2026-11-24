import RefundCount

/-
Global outside-support activation for L-meta-997. This strengthens the
LightCount cut argument using the whole linear target family. It operates
on actual circuit values and singleton supports, with no normalization or
claim of global soundness from singleton support containment.
-/

namespace PEqualNP.Research.OutsideActivation

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

/-- Wide gate supports belonging to no private target class, excluding z. -/
noncomputable def outsideWide {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter fun w =>
    w ≠ z ∧ 2 ≤ (support (n := n) C w).card ∧
      ∀ i : Fin m, ¬ support (n := n) C w ⊆ S i

/-- Fewer than k global outsiders can be activated away from one target.
The resulting cut argument recovers the full private count for that target. -/
theorem outside_activation_count {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hW : (outsideWide C S z).card < k)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hneg : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ S i, x q = false) → value C x o = false) :
    (S i).card - 1 ≤ (lightAssigned C (S i) z).card := by
  classical
  let G := lightAssigned C (S i) z
  let W := outsideWide C S z
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hBlt : B.card < (S i).card := by
    have hf := Finset.card_filter_le G (· < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < (S i).card - 1 at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) :=
    if w = z ∨ w ∈ W then ∅ else support (n := n) C w ∩ S i
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hspecial : w = z ∨ w ∈ W
    · simp [clean, hspecial]
    rw [show clean w = support (n := n) C w ∩ S i from ite_eq_right hspecial]
    have hwz : w ≠ z := fun h => hspecial (Or.inl h)
    have hwW : w ∉ W := fun h => hspecial (Or.inr h)
    by_cases hwide : 2 ≤ (support (n := n) C w).card
    · have hrange := Finset.mem_Ico.mpr (support_gate C w hwide)
      have howner : ∃ j : Fin m, support (n := n) C w ⊆ S j := by
        by_contra hnone
        apply hwW
        exact Finset.mem_filter.mpr ⟨hrange, hwz, hwide, fun j hj => hnone ⟨j, hj⟩⟩
      obtain ⟨j, hj⟩ := howner
      have hji : j ≠ i := by
        intro he
        subst j
        exact Finset.disjoint_left.mp hd hw
          (Finset.mem_filter.mpr ⟨hrange, hwz, hj, hwide⟩)
      have hsub : support (n := n) C w ∩ S i ⊆ S j ∩ S i := by
        intro p hp
        exact Finset.mem_inter.mpr ⟨hj (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩
      exact (Finset.card_le_card hsub).trans (hinter j i hji)
    · have hc := Finset.card_le_card
        (Finset.inter_subset_left (s₁ := support (n := n) C w) (s₂ := S i))
      omega
  have hcover : (B.biUnion clean).card < (S i).card := by
    have hc := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at hc
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have witness (w : {w // w ∈ W}) :
      ∃ q : Fin n, q ∈ support (n := n) C w.val ∧ q ∉ S i := by
    have hnot := (Finset.mem_filter.mp w.property).2.2.2 i
    by_contra! h
    exact hnot h
  choose q hq using witness
  let U := W.attach.image q
  let x : Fin n → Bool := bit U
  have hUcard : U.card < k := calc
    U.card ≤ W.attach.card := Finset.card_image_le
    _ = W.card := Finset.card_attach
    _ < k := hW
  have hUx : (Finset.univ.filter (fun v => x v = true)).card < k := by
    have he : Finset.univ.filter (fun v => x v = true) = U := by
      ext v
      simp [x, bit]
    simpa only [he] using hUcard
  have hUS : ∀ v ∈ S i, x v = false := by
    intro v hvS
    apply Bool.eq_false_iff.mpr
    intro hv
    have hvU : v ∈ U := of_decide_eq_true hv
    obtain ⟨w, _, he⟩ := Finset.mem_image.mp hvU
    exact (hq w).2 (he.symm ▸ hvS)
  have houtside : ∀ w ∈ W, value C x w = true := by
    intro w hw
    let a : {w // w ∈ W} := ⟨w, hw⟩
    have hqU : q a ∈ U := Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩
    have hsingle := (mem_support C w (q a)).mp (hq a).1
    apply value_mono C hG (fun v => decide (v = q a)) x _ w hsingle
    intro v hv
    have he : v = q a := of_decide_eq_true hv
    subst v
    exact decide_eq_true hqU
  have hfalse := hneg x hUx hUS
  have htrue : value C x o = true := by
    apply hcut _ x _ o (Finset.mem_singleton_self _) (hpos p hp)
    intro w hw hv
    by_cases hwz : w = z
    · rw [hwz]
      exact hz x
    by_cases hwW : w ∈ W
    · exact houtside w hwW
    have hpw : p ∈ support (n := n) C w := (mem_support C w p).mpr hv
    have hpc : p ∈ clean w := by
      simp only [clean, hwz, hwW, or_self, ite_false]
      exact Finset.mem_inter.mpr ⟨hpw, hp⟩
    exact False.elim (hpnot (Finset.mem_biUnion.mpr ⟨w, hw, hpc⟩))
  rw [hfalse] at htrue
  contradiction

/-- The per-target counts add for the linear family. -/
theorem outside_activation_sum {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (z : ℕ)
    (hk : 2 ≤ k)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hW : (outsideWide C S z).card < k)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, ((S i).card - 1)) ≤
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card := by
  classical
  have hcount (i : Fin m) : (S i).card - 1 ≤ (lightAssigned C (S i) z).card := by
    apply outside_activation_count C S z hG hz hinter hW i (out i)
    · intro p hp
      have hset : Finset.univ.filter (fun q : Fin n => decide (q = p) = true) = {p} := by
        ext q
        simp
      have hweight : (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card < k := by
        rw [hset, Finset.card_singleton]
        omega
      rw [hwindow i _ hweight]
      exact decide_eq_true ⟨p, hp, by simp⟩
    · intro x hx hzero
      rw [hwindow i x hx]
      apply decide_eq_false
      rintro ⟨p, hp, hv⟩
      rw [hzero p hp] at hv
      contradiction
  calc
    (∑ i : Fin m, ((S i).card - 1)) ≤
        ∑ i : Fin m, (lightAssigned C (S i) z).card :=
      Finset.sum_le_sum (fun i _ => hcount i)
    _ = (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card :=
      (Finset.card_biUnion (lightAssigned_pairwise_disjoint C S z hinter)).symm

/-- Outside wide gates, all private gates, prefix empty-support branches,
and the exceptional wire are disjoint. -/
theorem private_outside_minterm_count {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z u : ℕ) (y : Fin n → Bool)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzgate : z ∈ Finset.Ico n (n + C.size)) (huz : u < z)
    (hy : value C y u = true)
    (hmin : ∀ x : Fin n → Bool, value C x u = true →
      k ≤ (Finset.univ.filter (fun p : Fin n => x p = true)).card) :
    (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card + k +
      (outsideWide C S z).card ≤ C.size := by
  classical
  let L := Finset.univ.biUnion (fun i => lightAssigned C (S i) z)
  let W := outsideWide C S z
  let A := (branches C y).filter (· ≤ u)
  let R := Finset.Ico n (n + C.size)
  have hL : L ⊆ R.erase z := lightAssigned_union_subset C S z
  have hW : W ⊆ R.erase z := by
    intro w hw
    have h := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨h.2.1, h.1⟩
  have hA : A ⊆ R.erase z := by
    intro w hw
    obtain ⟨hwa, hwu⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_erase.mpr ⟨by omega, (Finset.mem_filter.mp hwa).1⟩
  have hLW : Disjoint L W := by
    apply Finset.disjoint_left.mpr
    intro w hwL hwW
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hwL
    exact (Finset.mem_filter.mp hwW).2.2.2 i (Finset.mem_filter.mp hwi).2.2.1
  have hLA : Disjoint L A := by
    apply Finset.disjoint_left.mpr
    intro w hwL hwA
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hwL
    have hwide := (Finset.mem_filter.mp hwi).2.2.2
    have hempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hwA).1).2.2.1
    simp [hempty] at hwide
  have hWA : Disjoint W A := by
    apply Finset.disjoint_left.mpr
    intro w hwW hwA
    have hwide := (Finset.mem_filter.mp hwW).2.2.1
    have hempty := (Finset.mem_filter.mp (Finset.mem_filter.mp hwA).1).2.2.1
    simp [hempty] at hwide
  have hLWA : Disjoint (L ∪ W) A := by
    apply Finset.disjoint_left.mpr
    intro w hw hwA
    rcases Finset.mem_union.mp hw with hwL | hwW
    · exact Finset.disjoint_left.mp hLA hwL hwA
    · exact Finset.disjoint_left.mp hWA hwW hwA
  have hcards : L.card + W.card + A.card ≤ (R.erase z).card := by
    rw [← Finset.card_union_of_disjoint hLW, ← Finset.card_union_of_disjoint hLWA]
    exact Finset.card_le_card (Finset.union_subset (Finset.union_subset hL hW) hA)
  have hremove : (R.erase z).card + 1 = C.size := by
    have h := Finset.card_erase_add_one hzgate
    simpa [R] using h
  have hbranch := minterm_bound C hG y u k hy hmin
  change k ≤ A.card + 1 at hbranch
  change L.card + k + W.card ≤ C.size
  omega

end PEqualNP.Research.OutsideActivation

#print axioms PEqualNP.Research.OutsideActivation.outside_activation_count
#print axioms PEqualNP.Research.OutsideActivation.outside_activation_sum
#print axioms PEqualNP.Research.OutsideActivation.private_outside_minterm_count
