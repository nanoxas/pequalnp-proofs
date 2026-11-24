import LightCount

/-
Research helper combining two separately checked counts. The light assigned
gates have singleton support of size at least two; the minterm branches have
empty singleton support and occur before a specified exceptional wire.
This proves the combined B+k bound, not the complete L-meta-997 overlap bound.
-/

namespace PEqualNP.Research.MintermSlack

open PEqualNP.CircuitLowerBounds

theorem light_minterm_bound {n m k : ℕ} (C : Circuit)
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

end PEqualNP.Research.MintermSlack

#print axioms PEqualNP.Research.MintermSlack.light_minterm_bound
