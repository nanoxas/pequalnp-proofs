import Common
import RawUnionCount
import C4Stars

/-! Instantiation of the raw support count on the actual circuit, followed
by the disjoint charge sum over chosen star centers. -/

namespace PEqualNP.MetaComplexity.L1407

open Finset PEqualNP.CircuitLowerBounds
open scoped BigOperators

noncomputable def liveSupport {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical
  exact if Live (n := n) C w then support C w else ∅

theorem liveSupport_eq {n : ℕ} (C : Circuit) (w : ℕ) (h : Live (n := n) C w) :
    liveSupport (n := n) C w = support C w := by
  classical
  simp only [liveSupport, h, ↓reduceIte]

noncomputable def rawMergesWithin {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (rawMergeGates (n := n) C).filter (fun j => support C (n + j) ⊆ S)

theorem mem_rawMergesWithin {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (j : ℕ) :
    j ∈ rawMergesWithin C S ↔
      j < C.gates.length ∧ RawMerge (n := n) C j ∧ support C (n + j) ⊆ S := by
  classical
  simp only [rawMergesWithin, mem_filter, mem_rawMergeGates]
  exact ⟨fun ⟨⟨hj, hm⟩, hs⟩ => ⟨hj, hm, hs⟩,
    fun ⟨hj, hm, hs⟩ => ⟨⟨hj, hm⟩, hs⟩⟩

theorem rawWideGates_liveSupport {n : ℕ} (C : Circuit) (S : Finset (Fin n)) :
    @rawWideGates (Fin n) _ (RawMerge (n := n) C)
      (fun j => Classical.propDecidable (RawMerge (n := n) C j))
      (liveSupport C) n C.gates.length S =
      rawMergesWithin C S := by
  classical
  ext j
  simp only [mem_rawWideGates, mem_rawMergesWithin]
  constructor
  · rintro ⟨hj, hm, hw, hs⟩
    exact ⟨hj, hm, by simpa only [liveSupport_eq C _ hm.1] using hs⟩
  · rintro ⟨hj, hm, hs⟩
    have hlive := hm.1
    obtain ⟨_, g, a, b, hg, hop, hin, ha, hb, hna, hnb, hwide⟩ := hm
    refine ⟨hj, ⟨hlive, g, a, b, hg, hop, hin, ha, hb, hna, hnb, hwide⟩, ?_, ?_⟩
    · simpa only [liveSupport_eq C _ hlive] using hwide
    · simpa only [liveSupport_eq C _ hlive] using hs

/-- A support union over live roots is bounded by its root count and the
live wide raw merges contained in the same support region. -/
theorem live_raw_union_count {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C)
    (S : Finset (Fin n)) (R : Finset ℕ)
    (hbound : ∀ r ∈ R, r < n + C.gates.length)
    (hlive : ∀ r ∈ R, Live (n := n) C r)
    (hsub : ∀ r ∈ R, support C r ⊆ S) :
    (R.biUnion (support (n := n) C)).card ≤ R.card + (rawMergesWithin C S).card := by
  classical
  have hi : ∀ i < n, (liveSupport (n := n) C i).card ≤ 1 := by
    intro i hi
    by_cases h : Live (n := n) C i
    · simpa only [liveSupport_eq C i h] using input_support_card_le_one C i hi
    · simp only [liveSupport, h, ↓reduceIte, card_empty]
      omega
  have hstep : ∀ j < C.gates.length, 2 ≤ (liveSupport (n := n) C (n + j)).card →
      (∃ a : ℕ, a < n + j ∧ liveSupport (n := n) C (n + j) = liveSupport C a) ∨
      (RawMerge (n := n) C j ∧ ∃ a b : ℕ, a < n + j ∧ b < n + j ∧
        liveSupport (n := n) C (n + j) = liveSupport C a ∪ liveSupport C b) := by
    intro j hj hw
    have hl : Live (n := n) C (n + j) := by
      by_contra h
      simp only [liveSupport, h, ↓reduceIte, card_empty] at hw
      omega
    have hw' : 2 ≤ (support (n := n) C (n + j)).card := by
      simpa only [liveSupport_eq C _ hl] using hw
    have hg : C.gates[j]? = some (C.gates[j]'hj) := List.getElem?_eq_getElem hj
    rcases wide_support_step G C hops hclean j _ hg hl hw' with
      ⟨a, ha, hla, heq⟩ | ⟨hm, a, b, ha, hb, hla, hlb, heq⟩
    · refine Or.inl ⟨a, ha, ?_⟩
      simpa only [liveSupport_eq C _ hl, liveSupport_eq C _ hla] using heq
    · refine Or.inr ⟨hm, a, b, ha, hb, ?_⟩
      simpa only [liveSupport_eq C _ hl, liveSupport_eq C _ hla,
        liveSupport_eq C _ hlb] using heq
  have hs : ∀ r ∈ R, liveSupport (n := n) C r ⊆ S := by
    intro r hr
    simpa only [liveSupport_eq C r (hlive r hr)] using hsub r hr
  have h := raw_union_count (RawMerge (n := n) C) (liveSupport C) n S hi
    C.gates.length hstep R hbound hs
  have hu : R.biUnion (liveSupport (n := n) C) = R.biUnion (support C) := by
    apply Finset.biUnion_congr rfl
    intro r hr
    exact liveSupport_eq C r (hlive r hr)
  rw [hu, rawWideGates_liveSupport C S] at h
  exact h

/-- A finite family of live support roots grouped by star center. No raw
merge can be charged to two centers in a graph without a four-cycle. -/
theorem circuit_family_union_count {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (center : ι → Fin n) (root : ι → ℕ)
    (hroot : ∀ i, root i < n + C.gates.length)
    (hlive : ∀ i, Live (n := n) C (root i))
    (hstar : ∀ i u, u ∈ support C (root i) → G.Adj (center i) u) :
    (∑ v : Fin n, ((univ.filter (fun i : ι => center i = v)).biUnion
      (fun i => support (n := n) C (root i))).card) ≤
        Fintype.card ι + (rawMergeGates (n := n) C).card := by
  classical
  let J : Fin n → Finset ι := fun v => univ.filter (fun i => center i = v)
  let S : Fin n → Finset (Fin n) := fun v => univ.filter (fun u => G.Adj v u)
  let U : Fin n → Finset (Fin n) := fun v => (J v).biUnion (fun i => support C (root i))
  let W : Fin n → Finset ℕ := fun v => rawMergesWithin C (S v)
  have hlocal : ∀ v, (U v).card ≤ (J v).card + (W v).card := by
    intro v
    let R := (J v).image root
    have hr : ∀ r ∈ R, r < n + C.gates.length := by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      exact hroot i
    have hl : ∀ r ∈ R, Live (n := n) C r := by
      intro r hr
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      exact hlive i
    have hs : ∀ r ∈ R, support C r ⊆ S v := by
      intro r hr u hu
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hr
      have hiv : center i = v := (mem_filter.mp hi).2
      exact mem_filter.mpr ⟨mem_univ _, by rw [← hiv]; exact hstar i u hu⟩
    have h := live_raw_union_count G C hops hclean (S v) R hr hl hs
    have heq : R.biUnion (support (n := n) C) = U v := by
      ext u
      simp only [R, U, mem_biUnion, mem_image]
      constructor
      · rintro ⟨r, ⟨i, hi, rfl⟩, hu⟩
        exact ⟨i, hi, hu⟩
      · rintro ⟨i, hi, hu⟩
        exact ⟨root i, ⟨i, hi, rfl⟩, hu⟩
    rw [heq] at h
    have hc : R.card ≤ (J v).card := card_image_le
    change (U v).card ≤ (J v).card + (rawMergesWithin C (S v)).card
    omega
  have hdisj : ((univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint W := by
    intro v hv w hw hvw
    apply Finset.disjoint_left.mpr
    intro j hjv hjw
    obtain ⟨hj, hm, hsv⟩ := (mem_rawMergesWithin C (S v) j).mp hjv
    obtain ⟨_, _, hsw⟩ := (mem_rawMergesWithin C (S w) j).mp hjw
    obtain ⟨_, g, a, b, hg, hop, hin, ha, hb, hna, hnb, hwide⟩ := hm
    have heq := shared_wide_support_implies_same_center G hG v w
      (support C (n + j)) hwide
      (fun u hu => (mem_filter.mp (hsv hu)).2)
      (fun u hu => (mem_filter.mp (hsw hu)).2)
    exact hvw heq
  have hW : (∑ v : Fin n, (W v).card) ≤ (rawMergeGates (n := n) C).card := by
    rw [← Finset.card_biUnion hdisj]
    apply card_le_card
    intro j hj
    obtain ⟨v, _, hj⟩ := mem_biUnion.mp hj
    exact (mem_filter.mp hj).1
  have hJ : (∑ v : Fin n, (J v).card) = Fintype.card ι := by
    simpa only [J, Finset.card_univ] using
      sum_center_fibers (univ : Finset ι) center
  change (∑ v : Fin n, (U v).card) ≤ _
  calc
    (∑ v : Fin n, (U v).card) ≤ ∑ v : Fin n, ((J v).card + (W v).card) :=
      sum_le_sum fun v _ => hlocal v
    _ = (∑ v : Fin n, (J v).card) + ∑ v : Fin n, (W v).card := sum_add_distrib
    _ ≤ Fintype.card ι + (rawMergeGates (n := n) C).card := by rw [hJ]; omega

end PEqualNP.MetaComplexity.L1407

#print axioms PEqualNP.MetaComplexity.L1407.circuit_family_union_count
