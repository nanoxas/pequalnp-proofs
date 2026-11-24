import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.MetaComplexity.L1407

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev NoFourCycle (G : SimpleGraph V) : Prop :=
  ∀ a b c d : V, a ≠ c → b ≠ d →
    ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

lemma common_neighbors_card_le_one (G : SimpleGraph V) (hG : NoFourCycle G)
    (a b : V) (hab : a ≠ b) (S : Finset V)
    (ha : ∀ u ∈ S, G.Adj a u) (hb : ∀ u ∈ S, G.Adj b u) :
    S.card ≤ 1 := by
  by_contra h
  have hcard : 1 < S.card := by omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hcard
  exact hG a u b v hab huv ⟨ha u hu, (hb u hu).symm, hb v hv, (ha v hv).symm⟩

lemma biclique_has_singleton_side (G : SimpleGraph V) (hG : NoFourCycle G)
    (S T : Finset V) (hS : S.Nonempty) (hT : T.Nonempty)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) :
    (∃ v, S = {v}) ∨ (∃ v, T = {v}) := by
  by_cases hs : S.card ≤ 1
  · left
    have hc : S.card = 1 := by have := Finset.card_pos.mpr hS; omega
    exact Finset.card_eq_one.mp hc
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
    have ht := common_neighbors_card_le_one G hG a b hab T
      (fun u hu => hcross a ha u hu) (fun u hu => hcross b hb u hu)
    right
    have hc : T.card = 1 := by have := Finset.card_pos.mpr hT; omega
    exact Finset.card_eq_one.mp hc

lemma biclique_is_star (G : SimpleGraph V) (hG : NoFourCycle G)
    (S T : Finset V) (hS : S.Nonempty) (hT : T.Nonempty)
    (hcross : ∀ a ∈ S, ∀ b ∈ T, G.Adj a b) :
    ∃ (v : V) (U : Finset V), U.Nonempty ∧
      ((S = {v} ∧ T = U) ∨ (T = {v} ∧ S = U)) ∧
      (∀ u ∈ U, G.Adj v u) := by
  rcases biclique_has_singleton_side G hG S T hS hT hcross with ⟨v, hv⟩ | ⟨v, hv⟩
  · refine ⟨v, T, hT, Or.inl ⟨hv, rfl⟩, ?_⟩
    intro u hu
    exact hcross v (by simp [hv]) u hu
  · refine ⟨v, S, hS, Or.inr ⟨hv, rfl⟩, ?_⟩
    intro u hu
    exact (hcross u hu v (by simp [hv])).symm

lemma shared_wide_support_implies_same_center (G : SimpleGraph V) (hG : NoFourCycle G)
    (a b : V) (S : Finset V) (hwide : 2 ≤ S.card)
    (ha : ∀ u ∈ S, G.Adj a u) (hb : ∀ u ∈ S, G.Adj b u) : a = b := by
  by_contra hab
  have := common_neighbors_card_le_one G hG a b hab S ha hb
  omega

lemma edge_count_le_star_unions (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : V → Finset V)
    (hcover : ∀ u v : V, G.Adj u v → v ∈ U u ∨ u ∈ U v) :
    G.edgeFinset.card ≤ ∑ v : V, (U v).card := by
  let E : V → Finset (Sym2 V) := fun v => (U v).image (fun u => s(v, u))
  have hsub : G.edgeFinset ⊆ Finset.univ.biUnion E := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      have huv : G.Adj u v := by simpa using he
      rcases hcover u v huv with h | h
      · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, Finset.mem_image.mpr ⟨v, h, rfl⟩⟩
      · apply Finset.mem_biUnion.mpr
        refine ⟨v, Finset.mem_univ _, Finset.mem_image.mpr ⟨u, h, ?_⟩⟩
        exact Sym2.eq_swap
  calc
    G.edgeFinset.card ≤ (Finset.univ.biUnion E).card := Finset.card_le_card hsub
    _ ≤ ∑ v : V, (E v).card := Finset.card_biUnion_le
    _ ≤ ∑ v : V, (U v).card := Finset.sum_le_sum fun v _ => Finset.card_image_le

lemma centers_form_cover {ι : Type*} [DecidableEq ι]
    (G : SimpleGraph V) (A : Finset ι) (center : ι → V)
    (hcover : ∀ u v : V, G.Adj u v → ∃ a ∈ A, center a = u ∨ center a = v) :
    ∃ T : Finset V, (∀ u v : V, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ A.card := by
  refine ⟨A.image center, ?_, Finset.card_image_le⟩
  intro u v huv
  obtain ⟨a, ha, h⟩ := hcover u v huv
  rcases h with h | h
  · exact Or.inl (Finset.mem_image.mpr ⟨a, ha, h⟩)
  · exact Or.inr (Finset.mem_image.mpr ⟨a, ha, h⟩)

lemma sum_center_fibers {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (center : ι → V) :
    (∑ v : V, (A.filter fun a => center a = v).card) = A.card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter A (Finset.univ : Finset V) center

lemma clean_total_assembly (edges cover productive rawMerges aggregation other total : ℕ)
    (hedges : edges ≤ rawMerges + productive)
    (hcover : cover ≤ productive)
    (haggregation : productive ≤ aggregation + 1)
    (htotal : productive + rawMerges + aggregation + other ≤ total) :
    edges + cover ≤ total + 1 := by
  omega

lemma clean_total_from_live (edges cover productive wide live total : ℕ)
    (hedges : edges ≤ wide + productive) (hcover : cover ≤ productive)
    (hports : 2 * productive + wide ≤ live + 1) (hlive : live ≤ total) :
    edges + cover ≤ total + 1 := by
  omega

end PEqualNP.MetaComplexity.L1407
