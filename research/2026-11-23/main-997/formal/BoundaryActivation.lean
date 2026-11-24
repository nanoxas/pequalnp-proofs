import OutsideActivation

/-
Selected-outside activation and the boundary of the private-support count.
The cut helpers adapt the checked OutsideActivation argument, which in turn
uses the accepted L-meta-986 cut infrastructure. Apache-2.0.
This module develops a sufficient case of L-meta-997.
-/

namespace PEqualNP.Research.BoundaryActivation

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation

noncomputable def cleanLabel {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) (i : Fin m) (w : ℕ) : Finset (Fin n) := by
  classical
  exact if w = z ∨ w ∈ outsideWide C S z then ∅ else support (n := n) C w ∩ S i

noncomputable def activeOutside {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) (p : Fin n) : Finset ℕ := by
  classical
  exact (outsideWide C S z).filter fun w => p ∈ support (n := n) C w

lemma cleanLabel_card_le_one {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) (i : Fin m) (B : Finset ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hd : Disjoint B (lightAssigned C (S i) z)) :
    ∀ w ∈ B, (cleanLabel C S z i w).card ≤ 1 := by
  classical
  intro w hw
  by_cases hspecial : w = z ∨ w ∈ outsideWide C S z
  · simp [cleanLabel, hspecial]
  rw [show cleanLabel C S z i w = support (n := n) C w ∩ S i from ite_eq_right hspecial]
  have hwz : w ≠ z := fun h => hspecial (Or.inl h)
  have hwW : w ∉ outsideWide C S z := fun h => hspecial (Or.inr h)
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

lemma missed_frontier_special {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) (i : Fin m) (B : Finset ℕ)
    (p : Fin n) (hp : p ∈ S i) (hpnot : p ∉ B.biUnion (cleanLabel C S z i))
    (w : ℕ) (hw : w ∈ B) (ht : value C (fun q => decide (q = p)) w = true) :
    w = z ∨ w ∈ outsideWide C S z := by
  classical
  by_contra hspecial
  have hpw : p ∈ support (n := n) C w := (mem_support C w p).mpr ht
  have hpc : p ∈ cleanLabel C S z i w := by
    simp only [cleanLabel, ite_eq_right hspecial]
    exact Finset.mem_inter.mpr ⟨hpw, hp⟩
  exact hpnot (Finset.mem_biUnion.mpr ⟨w, hw, hpc⟩)

/-- Any chosen collection of outsiders can be activated away from one target
using at most one input per chosen wire. -/
lemma outside_activation_set {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) (i : Fin m)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (D : Finset ℕ) (hD : D ⊆ outsideWide C S z) :
    ∃ U : Finset (Fin n), U.card ≤ D.card ∧ Disjoint U (S i) ∧
      ∀ w ∈ D, value C (bit U) w = true := by
  classical
  have witness (w : {w // w ∈ D}) :
      ∃ q : Fin n, q ∈ support (n := n) C w.val ∧ q ∉ S i := by
    have hnot := (Finset.mem_filter.mp (hD w.property)).2.2.2 i
    by_contra! h
    exact hnot h
  choose q hq using witness
  let U := D.attach.image q
  refine ⟨U, ?_, ?_, ?_⟩
  · calc
      U.card ≤ D.attach.card := Finset.card_image_le
      _ = D.card := Finset.card_attach
  · apply Finset.disjoint_left.mpr
    intro v hv hvS
    obtain ⟨w, _, he⟩ := Finset.mem_image.mp hv
    exact (hq w).2 (he.symm ▸ hvS)
  · intro w hw
    let a : {w // w ∈ D} := ⟨w, hw⟩
    have hqU : q a ∈ U := Finset.mem_image.mpr ⟨a, Finset.mem_attach _ _, rfl⟩
    have hsingle := (mem_support C w (q a)).mp (hq a).1
    apply value_mono C hG (fun v => decide (v = q a)) (bit U) _ w hsingle
    intro v hv
    have he : v = q a := of_decide_eq_true hv
    subst v
    exact decide_eq_true hqU

lemma bit_weight {n : ℕ} (U : Finset (Fin n)) :
    (Finset.univ.filter (fun p => bit U p = true)).card = U.card := by
  classical
  congr 1
  ext p
  simp [bit]

lemma bit_zero_on {n : ℕ} (U T : Finset (Fin n)) (h : Disjoint U T) :
    ∀ p ∈ T, bit U p = false := by
  classical
  intro p hp
  have hn : p ∉ U := fun hu => Finset.disjoint_left.mp h hu hp
  simp [bit, hn]

/-- A negative input activating every outsider supplies the full private
count for one target; its weight is irrelevant to this local cut lemma. -/
lemma private_count_of_activation {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (x : Fin n → Bool) (hfalse : value C x o = false)
    (hactive : ∀ w ∈ outsideWide C S z, value C x w = true) :
    (S i).card - 1 ≤ (lightAssigned C (S i) z).card := by
  classical
  let G := lightAssigned C (S i) z
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
  have hclean := cleanLabel_card_le_one C S z i B hinter hd
  have hcover : (B.biUnion (cleanLabel C S z i)).card < (S i).card := by
    have hc := Finset.card_biUnion_le_card_mul B (cleanLabel C S z i) 1 hclean
    simp only [mul_one] at hc
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have htrue : value C x o = true := by
    apply hcut _ x _ o (Finset.mem_singleton_self _) (hpos p hp)
    intro w hw hv
    rcases missed_frontier_special C S z i B p hp hpnot w hw hv with hwz | hwW
    · rw [hwz]
      exact hz x
    · exact hactive w hwW
  rw [hfalse] at htrue
  contradiction

/-- Paying for every outsider recovers the full private count of one target.
The remaining frontier transfers to the zero input. -/
lemma compensated_private_count {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hzero : value C (fun _ : Fin n => false) o = false) :
    (S i).card - 1 ≤ (lightAssigned C (S i) z).card + (outsideWide C S z).card := by
  classical
  let G := lightAssigned C (S i) z
  let W := outsideWide C S z
  let H := G ∪ W
  by_contra! hsmall
  have hgate : ∀ w ∈ H, n ≤ w ∧ w < n + C.size := by
    intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    · exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG H hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hBG : Disjoint B G := hd.mono_right Finset.subset_union_left
  have hBW : Disjoint B W := hd.mono_right Finset.subset_union_right
  have hBlt : B.card < (S i).card := by
    have hf := Finset.card_filter_le H (· < n + C.size)
    have hu := Finset.card_union_le G W
    simp only [Finset.card_singleton] at hBcard
    change G.card + W.card < (S i).card - 1 at hsmall
    change H.card ≤ G.card + W.card at hu
    omega
  have hclean := cleanLabel_card_le_one C S z i B hinter hBG
  have hcover : (B.biUnion (cleanLabel C S z i)).card < (S i).card := by
    have hc := Finset.card_biUnion_le_card_mul B (cleanLabel C S z i) 1 hclean
    simp only [mul_one] at hc
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have htrue : value C (fun _ : Fin n => false) o = true := by
    apply hcut _ _ _ o (Finset.mem_singleton_self _) (hpos p hp)
    intro w hw hv
    rcases missed_frontier_special C S z i B p hp hpnot w hw hv with hwz | hwW
    · rw [hwz]
      exact hz _
    · exact False.elim (Finset.disjoint_left.mp hBW hw hwW)
  rw [hzero] at htrue
  contradiction

end PEqualNP.Research.BoundaryActivation

#print axioms PEqualNP.Research.BoundaryActivation.outside_activation_set
#print axioms PEqualNP.Research.BoundaryActivation.private_count_of_activation
#print axioms PEqualNP.Research.BoundaryActivation.compensated_private_count
