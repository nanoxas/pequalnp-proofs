import RefundCount

/-
Finite incidence accounting for the mandatory-pair-clause route to L-meta-997.
For a point outside Y, each target through that point that meets Y consumes
a different point of Y, because distinct targets intersect in at most one.
-/

namespace PEqualNP.Research.OutsideIncidence

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

noncomputable def lightIncidence {n m : ℕ} (S : Fin m → Finset (Fin n))
    (Y : Finset (Fin n)) (b : Fin n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => b ∈ S i ∧ ¬ Disjoint (S i) Y

noncomputable def largeIncidence {n m : ℕ} (S : Fin m → Finset (Fin n))
    (b : Fin n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => b ∈ S i ∧ 2 ≤ (S i).card

theorem outside_light_incidence_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (Y : Finset (Fin n)) (b : Fin n) (hb : b ∉ Y)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (lightIncidence S Y b).card ≤ Y.card := by
  classical
  let I := lightIncidence S Y b
  have witness (i : ↥I) : ∃ p : Fin n, p ∈ Y ∧ p ∈ S i.val := by
    have hhit := (Finset.mem_filter.mp i.property).2.2
    obtain ⟨p, hpS, hpY⟩ := Finset.not_disjoint_iff.mp hhit
    exact ⟨p, hpY, hpS⟩
  choose q hq using witness
  have hqinj : Function.Injective q := by
    intro i j he
    apply Subtype.ext
    by_contra hij
    have hbi : b ∈ S i.val := (Finset.mem_filter.mp i.property).2.1
    have hbj : b ∈ S j.val := (Finset.mem_filter.mp j.property).2.1
    have hqj : q i ∈ S j.val := by rw [he]; exact (hq j).2
    have hne : b ≠ q i := by
      intro h
      apply hb
      rw [h]
      exact (hq i).1
    have hsub : {b, q i} ⊆ S i.val ∩ S j.val := by
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact Finset.mem_inter.mpr ⟨hbi, hbj⟩
      · have heq := Finset.mem_singleton.mp hp
        subst p
        exact Finset.mem_inter.mpr ⟨(hq i).2, hqj⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_pair hne] at hcard
    have hsmall := hinter i.val j.val hij
    omega
  have hsub : Finset.univ.image q ⊆ Y := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (hq i).1
  have hcard : (Finset.univ.image q).card = I.card := by
    rw [Finset.card_image_of_injective _ hqinj]
    simp
  change I.card ≤ Y.card
  rw [← hcard]
  exact Finset.card_le_card hsub

theorem outside_large_incidence_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (Y : Finset (Fin n)) (b : Fin n) (hb : b ∉ Y)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (largeIncidence S b).card ≤ (heavyNontrivial S Y).card + Y.card := by
  classical
  have hsub : largeIncidence S b ⊆ heavyNontrivial S Y ∪ lightIncidence S Y b := by
    intro i hi
    obtain ⟨_, hib, hlarge⟩ := Finset.mem_filter.mp hi
    by_cases hd : Disjoint (S i) Y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, hlarge⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hib, hd⟩)
  have h := Finset.card_le_card hsub
  have hu := Finset.card_union_le (heavyNontrivial S Y) (lightIncidence S Y b)
  have hl := outside_light_incidence_bound S Y b hb hinter
  omega

/-- The incidence cost of a clause point outside Y is paid by the exact
forced refunds plus the minterm budget. Singleton targets incur no cost. -/
theorem outside_large_incidence_refund {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Y : Finset (Fin n)) (b : Fin n)
    (hb : b ∉ Y)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (largeIncidence S b).card ≤ (refundGates C S Y).card + Y.card := by
  have h := outside_large_incidence_bound S Y b hb hinter
  have hr := forced_refund_count C S out Y hout hinter
  omega

end PEqualNP.Research.OutsideIncidence

#print axioms PEqualNP.Research.OutsideIncidence.outside_light_incidence_bound
#print axioms PEqualNP.Research.OutsideIncidence.outside_large_incidence_refund
