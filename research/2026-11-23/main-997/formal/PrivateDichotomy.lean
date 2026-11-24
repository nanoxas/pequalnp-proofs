import CutEvaluation

namespace PEqualNP.Research.PrivateDichotomy

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.BoundaryActivation
open PEqualNP.Research.OrCompensation
open PEqualNP.Research.CutEvaluation

/-- Each private class either pays its complete OR quota or contains the
AND branching required to cross the negative input window. -/
theorem private_or_and {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hneg : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      (∀ p ∈ S i, x p = false) → value C x o = false) :
    (S i).card - 1 ≤ (opPart n C GateOp.or (lightAssigned C (S i) z)).card ∨
      k - 1 ≤ (opPart n C GateOp.and (lightAssigned C (S i) z)).card := by
  classical
  let G := lightAssigned C (S i) z
  let W := outsideWide C S z
  let base : ℕ → Bool := fun w => decide (w = z ∨ w ∈ W)
  let v := cutValue n C G base
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have hv : Admissible n C G v := cutValue_admissible n C G base
  have hbound (w : ℕ) (hw : w ∉ G) : v w = base w :=
    cutValue_boundary n C G base w hw
  cases hvo : v o with
  | false =>
    left
    obtain ⟨B, hBG, hBc, hBv, hforce⟩ := admissible_frontier C hG G hgate v hv false
      (n + C.size) {o} (by simpa using hvo) (fun w _ hw => (hgate w hw).2)
    have hBn (w : ℕ) (hw : w ∈ B) : w ∉ G :=
      fun hg => Finset.disjoint_left.mp hBG hw hg
    have hBbase (w : ℕ) (hw : w ∈ B) : base w = false :=
      (hbound w (hBn w hw)).symm.trans (hBv w hw)
    let sample : Fin n → ℕ → Bool := fun p w =>
      base w || value C (fun q => decide (q = p)) w
    let vp : Fin n → ℕ → Bool := fun p => cutValue n C G (sample p)
    have hvp (p : Fin n) : Admissible n C G (vp p) :=
      cutValue_admissible n C G (sample p)
    have hpositive (p : Fin n) (hp : p ∈ S i) : vp p o = true := by
      apply admissible_mono C hG G hgate
        (value C (fun q => decide (q = p))) (vp p)
        (actual_admissible C G hgate _) (hvp p) _ o (hpos p hp)
      intro w hw ht
      have he := cutValue_boundary n C G (sample p) w hw
      change vp p w = sample p w at he
      rw [he]
      simp only [sample, ht, Bool.or_true]
    have hcover : S i ⊆ B.biUnion (cleanLabel C S z i) := by
      intro p hp
      by_contra hpmiss
      have hf : ∀ w ∈ B, vp p w = false := by
        intro w hw
        apply Bool.eq_false_iff.mpr
        intro ht
        have he := cutValue_boundary n C G (sample p) w (hBn w hw)
        change vp p w = sample p w at he
        rw [he] at ht
        have hs : value C (fun q => decide (q = p)) w = true := by
          simpa only [sample, hBbase w hw, Bool.false_or] using ht
        have hspec : ¬ (w = z ∨ w ∈ outsideWide C S z) := by
          exact of_decide_eq_false (hBbase w hw)
        have hc : p ∈ cleanLabel C S z i w := by
          simp only [cleanLabel, ite_eq_right hspec]
          exact Finset.mem_inter.mpr ⟨(mem_support C w p).mpr hs, hp⟩
        exact hpmiss (Finset.mem_biUnion.mpr ⟨w, hw, hc⟩)
      have hout := hforce (vp p) (hvp p) hf o (Finset.mem_singleton_self o)
      rw [hpositive p hp] at hout
      contradiction
    have hc := Finset.card_biUnion_le_card_mul B (cleanLabel C S z i) 1
      (cleanLabel_card_le_one C S z i B hinter hBG)
    have hs := Finset.card_le_card hcover
    have hf := Finset.card_filter_le (opPart n C GateOp.or G) (· < n + C.size)
    simp only [mul_one] at hc
    simp only [Finset.card_singleton, branchOp, Bool.false_eq_true, ite_false] at hBc
    change (S i).card - 1 ≤ (opPart n C GateOp.or G).card
    omega
  | true =>
    right
    by_contra! hsmall
    obtain ⟨B, hBG, hBc, hBv, hforce⟩ := admissible_frontier C hG G hgate v hv true
      (n + C.size) {o} (by simpa using hvo) (fun w _ hw => (hgate w hw).2)
    have hBsmall : B.card < k := by
      have hf := Finset.card_filter_le (opPart n C GateOp.and G) (· < n + C.size)
      simp only [Finset.card_singleton, branchOp, ite_true] at hBc
      change (opPart n C GateOp.and G).card < k - 1 at hsmall
      omega
    let D := B.erase z
    have hDW : D ⊆ W := by
      intro w hw
      obtain ⟨hwz, hwB⟩ := Finset.mem_erase.mp hw
      have hwG : w ∉ G := fun hg => Finset.disjoint_left.mp hBG hwB hg
      have hb : base w = true := (hbound w hwG).symm.trans (hBv w hwB)
      have hs : w = z ∨ w ∈ W := of_decide_eq_true hb
      exact hs.resolve_left hwz
    obtain ⟨U, hUc, hUS, hUactive⟩ := outside_activation_set C S z i hG D hDW
    have hUweight : (Finset.univ.filter (fun q => bit U q = true)).card < k := by
      rw [bit_weight]
      have hdB : D.card ≤ B.card := Finset.card_le_card (Finset.erase_subset z B)
      omega
    have hfalse := hneg (bit U) hUweight (bit_zero_on U (S i) hUS)
    have htrue : value C (bit U) o = true := by
      apply hforce (value C (bit U)) (actual_admissible C G hgate _) _ o
        (Finset.mem_singleton_self o)
      intro w hw
      by_cases hwz : w = z
      · rw [hwz]
        exact hz _
      · exact hUactive w (Finset.mem_erase.mpr ⟨hwz, hw⟩)
    rw [hfalse] at htrue
    contradiction

end PEqualNP.Research.PrivateDichotomy

#print axioms PEqualNP.Research.PrivateDichotomy.private_or_and
