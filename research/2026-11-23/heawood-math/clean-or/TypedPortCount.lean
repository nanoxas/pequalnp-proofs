import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-
Local research cores for the clean-AND counting argument. This file is not a
project submission. The extraction of the finite sets from root-model circuits
is not formalized here.
-/

namespace CleanPortCount

open Finset

/-- A binary union network with `roots` as its designated outputs needs at least
`inputs.card - roots.card` merge nodes. The live-network hypothesis is expressed
directly: every input or merge node is an output or is consumed by a merge. -/
theorem binary_union_ports {α : Type*} [DecidableEq α]
    (inputs merges roots : Finset α) (children : α → Finset α)
    (hdisjoint : Disjoint inputs merges)
    (hlive : inputs ∪ merges ⊆ roots ∪ merges.biUnion children)
    (hfanin : ∀ g ∈ merges, (children g).card ≤ 2) :
    inputs.card ≤ merges.card + roots.card := by
  have htotal := Finset.card_le_card hlive
  rw [Finset.card_union_of_disjoint hdisjoint] at htotal
  have hused : (merges.biUnion children).card ≤ merges.card * 2 :=
    Finset.card_biUnion_le_card_mul merges children 2 hfanin
  have hunion := Finset.card_union_le roots (merges.biUnion children)
  omega

/-- Empty-support gates in the normalized clean circuit are AND gates and OR
gates with two empty-support inputs. They can only be consumed by that second
OR class or by an OR with exactly one empty-support input. Liveness then forces
at least `ands.card - 1` OR gates among these two classes. -/
theorem typed_aggregation_ports {α : Type*} [DecidableEq α]
    (ands emptyOrs mixedOrs : Finset α) (output : α)
    (emptyChildren : α → Finset α)
    (hdisjoint : Disjoint ands emptyOrs)
    (hlive : ∀ g ∈ ands ∪ emptyOrs, g ≠ output →
      (∃ j ∈ emptyOrs, g ∈ emptyChildren j) ∨
      (∃ j ∈ mixedOrs, g ∈ emptyChildren j))
    (hempty : ∀ j ∈ emptyOrs, (emptyChildren j).card ≤ 2)
    (hmixed : ∀ j ∈ mixedOrs, (emptyChildren j).card ≤ 1) :
    ands.card ≤ emptyOrs.card + mixedOrs.card + 1 := by
  have hsub : ands ∪ emptyOrs ⊆
      insert output ((emptyOrs.biUnion emptyChildren) ∪
        (mixedOrs.biUnion emptyChildren)) := by
    intro g hg
    by_cases hgo : g = output
    · subst g
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rcases hlive g hg hgo with h | h
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr h)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr h)
  have htotal := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisjoint] at htotal
  have htwo : (emptyOrs.biUnion emptyChildren).card ≤ emptyOrs.card * 2 :=
    Finset.card_biUnion_le_card_mul emptyOrs emptyChildren 2 hempty
  have hone : (mixedOrs.biUnion emptyChildren).card ≤ mixedOrs.card := by
    simpa using Finset.card_biUnion_le_card_mul mixedOrs emptyChildren 1 hmixed
  have hinsert := Finset.card_insert_le output
    ((emptyOrs.biUnion emptyChildren) ∪ (mixedOrs.biUnion emptyChildren))
  have hunion := Finset.card_union_le
    (emptyOrs.biUnion emptyChildren) (mixedOrs.biUnion emptyChildren)
  omega

/-- Numerical assembly once the circuit-to-network charges are available. -/
theorem clean_count_assembly (edges cover ands rawOrs aggregationOrs : ℕ)
    (hraw : edges ≤ rawOrs + ands)
    (haggregation : ands ≤ aggregationOrs + 1)
    (hcover : cover ≤ ands) :
    edges ≤ rawOrs + aggregationOrs + 1 ∧
      edges + cover ≤ ands + rawOrs + aggregationOrs + 1 := by
  omega

theorem heawood_assembly (ands rawOrs aggregationOrs : ℕ)
    (hraw : 21 ≤ rawOrs + ands)
    (haggregation : ands ≤ aggregationOrs + 1)
    (hcover : 7 ≤ ands) :
    20 ≤ rawOrs + aggregationOrs ∧
      27 ≤ ands + rawOrs + aggregationOrs := by
  omega

end CleanPortCount
