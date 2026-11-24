import HeavyPacking

/-
Finite-set strengthening of the heavy-excess packing bound. Three sets of
size at least k+2 in a linear family occupy at least 3*k+3 points. Hence a
universe of size at most 3*k+1 permits at most two positive excess terms.
This module contains only the packing statement, not the full L-meta-997 claim.
-/

namespace PEqualNP.Research.TriplePacking

lemma triple_card_bound {α : Type*} [DecidableEq α]
    (A B D U : Finset α)
    (hA : A ⊆ U) (hB : B ⊆ U) (hD : D ⊆ U)
    (hAB : (A ∩ B).card ≤ 1) (hAD : (A ∩ D).card ≤ 1)
    (hBD : (B ∩ D).card ≤ 1) :
    A.card + B.card + D.card ≤ U.card + 3 := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A ∪ B) D
  have hi : ((A ∪ B) ∩ D).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have h := Finset.card_union_le (A ∩ D) (B ∩ D)
    omega
  have hu : (A ∪ B) ∪ D ⊆ U :=
    Finset.union_subset (Finset.union_subset hA hB) hD
  have hc := Finset.card_le_card hu
  omega

theorem linear_excess_bound_twice {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (S : ι → Finset α) (U : Finset α) (k : ℕ)
    (hsub : ∀ i ∈ I, S i ⊆ U)
    (hinter : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hsize : U.card ≤ 3 * k + 1) :
    (∑ i ∈ I, ((S i).card - k - 1)) ≤ 2 * k := by
  classical
  by_cases hex : ∃ i ∈ I, k + 1 < (S i).card
  · obtain ⟨i, hi, hlargei⟩ := hex
    by_cases hexj : ∃ j ∈ I, j ≠ i ∧ k + 1 < (S j).card
    · obtain ⟨j, hj, hji, hlargej⟩ := hexj
      have hrest : ∀ l ∈ I, l ≠ i → l ≠ j → (S l).card ≤ k + 1 := by
        intro l hl hli hlj
        have h := triple_card_bound (S i) (S j) (S l) U
          (hsub i hi) (hsub j hj) (hsub l hl)
          (hinter i hi j hj hji.symm) (hinter i hi l hl hli.symm)
          (hinter j hj l hl hlj.symm)
        omega
      have hpair : ({i, j} : Finset ι) ⊆ I := by
        intro l hl
        rcases Finset.mem_insert.mp hl with rfl | hl
        · exact hi
        · exact Finset.mem_singleton.mp hl ▸ hj
      have hsum : (∑ l ∈ I, ((S l).card - k - 1)) =
          ((S i).card - k - 1) + ((S j).card - k - 1) := by
        calc
          (∑ l ∈ I, ((S l).card - k - 1)) =
              ∑ l ∈ ({i, j} : Finset ι), ((S l).card - k - 1) := by
            symm
            apply Finset.sum_subset hpair
            intro l hl hn
            have hli : l ≠ i := by intro he; subst l; simp at hn
            have hlj : l ≠ j := by intro he; subst l; simp at hn
            have h := hrest l hl hli hlj
            omega
          _ = _ := by simp [hji.symm]
      have hcard := Finset.card_union_add_card_inter (S i) (S j)
      have hU := Finset.card_le_card (Finset.union_subset (hsub i hi) (hsub j hj))
      have hsmall := hinter i hi j hj hji.symm
      rw [hsum]
      omega
    · have hsum : (∑ l ∈ I, ((S l).card - k - 1)) = (S i).card - k - 1 := by
        apply Finset.sum_eq_single i
        · intro l hl hli
          have h : (S l).card ≤ k + 1 := by
            by_contra! hn
            exact hexj ⟨l, hl, hli, hn⟩
          omega
        · intro hn
          exact False.elim (hn hi)
      have hcard := Finset.card_le_card (hsub i hi)
      rw [hsum]
      omega
  · have hsum : (∑ i ∈ I, ((S i).card - k - 1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have h : (S i).card ≤ k + 1 := by
        by_contra! hn
        exact hex ⟨i, hi, hn⟩
      omega
    rw [hsum]
    omega

theorem heavy_excess_bound_twice {n m : ℕ}
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) (k : ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hsize : ((Finset.univ : Finset (Fin n)) \ Y).card ≤ 3 * k + 1) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - k - 1 else 0) ≤ 2 * k := by
  classical
  let I := Finset.univ.filter fun i : Fin m => Disjoint (S i) Y
  let U := (Finset.univ : Finset (Fin n)) \ Y
  have hsub : ∀ i ∈ I, S i ⊆ U := by
    intro i hi p hp
    have hd := (Finset.mem_filter.mp hi).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hpY => Finset.disjoint_left.mp hd hp hpY⟩
  have h := linear_excess_bound_twice I S U k hsub
    (fun i _ j _ hij => hinter i j hij) hsize
  simpa only [I, Finset.sum_filter] using h

end PEqualNP.Research.TriplePacking

#print axioms PEqualNP.Research.TriplePacking.triple_card_bound
#print axioms PEqualNP.Research.TriplePacking.linear_excess_bound_twice
#print axioms PEqualNP.Research.TriplePacking.heavy_excess_bound_twice
