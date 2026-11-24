import DeficientSeparation

-- Apache-2.0. Directed separation prevents three deficient targets
-- when the outside-gate count is at most 3*k-4.
namespace PEqualNP.Research.DeficientPacking

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.BoundaryActivation
open PEqualNP.Research.DeficientSeparation

lemma sdiff_card_as_sum {α : Type*} [DecidableEq α] (W A B : Finset α) (hA : A ⊆ W) :
    (A \ B).card = ∑ w ∈ W, if w ∈ A ∧ w ∉ B then 1 else 0 := by
  classical
  have he : A \ B = W.filter (fun w => w ∈ A ∧ w ∉ B) := by
    ext w
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨hA h.1, h⟩
    · intro h
      exact h.2
  rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma triple_directed_difference_bound {α : Type*} [DecidableEq α] (W A B C : Finset α)
    (hA : A ⊆ W) (hB : B ⊆ W) (hC : C ⊆ W) :
    (A \ B).card + (B \ A).card + (A \ C).card + (C \ A).card +
      (B \ C).card + (C \ B).card ≤ 2 * W.card := by
  classical
  rw [sdiff_card_as_sum W A B hA, sdiff_card_as_sum W B A hB,
    sdiff_card_as_sum W A C hA, sdiff_card_as_sum W C A hC,
    sdiff_card_as_sum W B C hB, sdiff_card_as_sum W C B hC]
  have hpoint (w : α) :
      (if w ∈ A ∧ w ∉ B then 1 else 0) +
      (if w ∈ B ∧ w ∉ A then 1 else 0) +
      (if w ∈ A ∧ w ∉ C then 1 else 0) +
      (if w ∈ C ∧ w ∉ A then 1 else 0) +
      (if w ∈ B ∧ w ∉ C then 1 else 0) +
      (if w ∈ C ∧ w ∉ B then 1 else 0) ≤ (2 : ℕ) := by
    by_cases ha : w ∈ A <;> by_cases hb : w ∈ B <;> by_cases hc : w ∈ C <;>
      simp [ha, hb, hc]
  have hs := Finset.sum_le_sum (s := W) (fun w _ => hpoint w)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_comm] using hs

lemma point_avoiding_two {n m k : ℕ} (S : Fin m → Finset (Fin n))
    (hk : 3 ≤ k)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i j l : Fin m) (hij : i ≠ j) (hil : i ≠ l)
    (M : Finset (Fin n)) (hMS : M ⊆ S i) (hM : k + 1 ≤ M.card) :
    ∃ p ∈ M, p ∉ S j ∧ p ∉ S l := by
  classical
  have hnot : ¬ M ⊆ S j ∪ S l := by
    intro hsub
    have hsub' : M ⊆ (S i ∩ S j) ∪ (S i ∩ S l) := by
      intro p hp
      rcases Finset.mem_union.mp (hsub hp) with hj | hl
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hMS hp, hj⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hMS hp, hl⟩)
    have hc := Finset.card_le_card hsub'
    have hu := Finset.card_union_le (S i ∩ S j) (S i ∩ S l)
    have h1 := hinter i j hij
    have h2 := hinter i l hil
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.not_subset.mp hnot
  exact ⟨p, hp, (fun hj => hpnot (Finset.mem_union_left _ hj)),
    (fun hl => hpnot (Finset.mem_union_right _ hl))⟩

noncomputable def deficientClasses {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => (lightAssigned C (S i) z).card < (S i).card - 1

theorem deficient_count_le_two {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (z : ℕ)
    (hk : 3 ≤ k)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hW : (outsideWide C S z).card ≤ 3 * k - 4)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) :
    (deficientClasses C S z).card ≤ 2 := by
  classical
  by_contra! hmany
  obtain ⟨i, hi, j, hj, l, hl, hij, hil, hjl⟩ := Finset.two_lt_card.mp hmany
  have hpos (a : Fin m) := window_singleton_positive C (S a) (out a)
    (show 2 ≤ k by omega) (hwindow a)
  have hneg (a : Fin m) := window_negative C (S a) (out a) (hwindow a)
  have hi' : (lightAssigned C (S i) z).card < (S i).card - 1 :=
    (Finset.mem_filter.mp hi).2
  have hj' : (lightAssigned C (S j) z).card < (S j).card - 1 :=
    (Finset.mem_filter.mp hj).2
  have hl' : (lightAssigned C (S l) z).card < (S l).card - 1 :=
    (Finset.mem_filter.mp hl).2
  obtain ⟨Mi, hMi, hMic, hMiA⟩ :=
    deficient_separated_points C S z hG hz hinter i (out i) (hpos i) (hneg i) hi'
  obtain ⟨Mj, hMj, hMjc, hMjA⟩ :=
    deficient_separated_points C S z hG hz hinter j (out j) (hpos j) (hneg j) hj'
  obtain ⟨Ml, hMl, hMlc, hMlA⟩ :=
    deficient_separated_points C S z hG hz hinter l (out l) (hpos l) (hneg l) hl'
  obtain ⟨pi, hpi, hpij, hpil⟩ := point_avoiding_two S hk hinter i j l hij hil Mi hMi hMic
  obtain ⟨pj, hpj, hpji, hpjl⟩ := point_avoiding_two S hk hinter j i l hij.symm hjl Mj hMj hMjc
  obtain ⟨pl, hpl, hpli, hplj⟩ := point_avoiding_two S hk hinter l i j hil.symm hjl.symm Ml hMl hMlc
  have hijA := (hMiA pi hpi).2 pj hpji
  have hjiA := (hMjA pj hpj).2 pi hpij
  have hilA := (hMiA pi hpi).2 pl hpli
  have hliA := (hMlA pl hpl).2 pi hpil
  have hjlA := (hMjA pj hpj).2 pl hplj
  have hljA := (hMlA pl hpl).2 pj hpjl
  have hsum := triple_directed_difference_bound (outsideWide C S z)
    (activeOutside C S z pi) (activeOutside C S z pj) (activeOutside C S z pl)
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  omega

end PEqualNP.Research.DeficientPacking

#print axioms PEqualNP.Research.DeficientPacking.triple_directed_difference_bound
#print axioms PEqualNP.Research.DeficientPacking.deficient_count_le_two
