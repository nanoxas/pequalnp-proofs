import Mathlib.Data.Fintype.Powerset
import PEqualNP.Defs

-- Exact finite graph-completeness child of the L-meta-909 reduction.
namespace PEqualNP.Research.BasisCompleteness

set_option synthInstance.maxSize 100000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem basis_complete :
  ∀ G : SimpleGraph (Fin 10), G = SimpleGraph.fromRel (fun a b : Fin 10 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))) →
    let d : ℕ → Finset (Fin 10) := fun m : ℕ => Finset.univ.filter (fun v : Fin 10 => m.testBit (v : ℕ) = true)
    let R : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
    ∀ I : Finset (Fin 10),
      (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) →
      (∀ w : Fin 10, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      (∃ m ∈ R, I = d m) ∧
      (I.card = 3 ∨ ∀ w : Fin 10, w ∉ I →
        ∃ m ∈ R, (d m).card = 3 ∧
          ∃ v : Fin 10, v ∉ d m ∧ insert v (d m) ⊆ insert w I) := by
  intro G hG
  subst G
  dsimp only
  simp only [SimpleGraph.fromRel_adj]
  decide +kernel

#print axioms basis_complete

end PEqualNP.Research.BasisCompleteness
