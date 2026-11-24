import BoundaryRigidity

-- Apache-2.0. This strengthens the checked deficient-cut certificate.
-- It is a supporting result for the exact L-meta-997 problem.
namespace PEqualNP.Research.DeficientSeparation

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.BoundaryActivation

theorem deficient_separated_points {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hneg : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      (∀ p ∈ S i, x p = false) → value C x o = false)
    (hdef : (lightAssigned C (S i) z).card < (S i).card - 1) :
    ∃ M : Finset (Fin n), M ⊆ S i ∧ k + 1 ≤ M.card ∧
      ∀ p ∈ M, k ≤ (activeOutside C S z p).card ∧
        ∀ q : Fin n, q ∉ S i → k - 1 ≤
          (activeOutside C S z p \ activeOutside C S z q).card := by
  classical
  let G := lightAssigned C (S i) z
  let W := outsideWide C S z
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hBc : B.card ≤ G.card + 1 := by
    have hf := Finset.card_filter_le G (· < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let label := cleanLabel C S z i
  let Q := B.biUnion label
  let M := S i \ Q
  have hclean : ∀ w ∈ B, (label w).card ≤ 1 :=
    cleanLabel_card_le_one C S z i B hinter hd
  have hQcard : Q.card ≤ B.card := by
    have hc := Finset.card_biUnion_le_card_mul B label 1 hclean
    simpa only [mul_one] using hc
  have hcover : Q.card < (S i).card := by
    change G.card < (S i).card - 1 at hdef
    omega
  let D (p : Fin n) := B.filter fun w => w ∈ W ∧ p ∈ support (n := n) C w
  have hDsub (p : Fin n) : D p ⊆ W :=
    fun _ hw => (Finset.mem_filter.mp hw).2.1
  have hDlarge (p : Fin n) (hp : p ∈ S i) (hpnot : p ∉ Q) : k ≤ (D p).card := by
    by_contra! hsmall
    obtain ⟨U, hUcard, hUS, hUactive⟩ := outside_activation_set C S z i hG (D p) (hDsub p)
    have hweight : (Finset.univ.filter (fun q => bit U q = true)).card < k := by
      rw [bit_weight]
      omega
    have hfalse := hneg (bit U) hweight (bit_zero_on U (S i) hUS)
    have htrue : value C (bit U) o = true := by
      apply hcut _ _ _ o (Finset.mem_singleton_self _) (hpos p hp)
      intro w hw hv
      rcases missed_frontier_special C S z i B p hp hpnot w hw hv with hwz | hwW
      · rw [hwz]
        exact hz _
      · apply hUactive w
        exact Finset.mem_filter.mpr ⟨hw, hwW, (mem_support C w p).mpr hv⟩
    rw [hfalse] at htrue
    contradiction
  obtain ⟨p₀, hp₀, hp₀not⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have hD₀large := hDlarge p₀ hp₀ hp₀not
  have hD₀B : D p₀ ⊆ B := Finset.filter_subset _ _
  have hQsub : Q ⊆ (B \ D p₀).biUnion label := by
    intro p hp
    obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
    have hwD : w ∉ D p₀ := by
      intro hmem
      have hwW := (Finset.mem_filter.mp hmem).2.1
      have hwW' : w ∈ outsideWide C S z := hwW
      have he : label w = ∅ := by simp [label, cleanLabel, hwW']
      rw [he] at hpw
      exact Finset.notMem_empty p hpw
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwD⟩, hpw⟩
  have hQrest : Q.card ≤ (B \ D p₀).card := by
    have hb := Finset.card_biUnion_le_card_mul (B \ D p₀) label 1
      (fun w hw => hclean w (Finset.mem_sdiff.mp hw).1)
    simp only [mul_one] at hb
    exact (Finset.card_le_card hQsub).trans hb
  have hrest := Finset.card_sdiff_add_card_eq_card hD₀B
  have hMcount := Finset.card_sdiff_add_card_inter (S i) Q
  have hinterQ := Finset.card_le_card
    (Finset.inter_subset_right (s₁ := S i) (s₂ := Q))
  have hMlarge : k + 1 ≤ M.card := by
    change M.card + (S i ∩ Q).card = (S i).card at hMcount
    change G.card < (S i).card - 1 at hdef
    omega
  refine ⟨M, Finset.sdiff_subset, hMlarge, ?_⟩
  intro p hp
  have hpS := (Finset.mem_sdiff.mp hp).1
  have hpnot := (Finset.mem_sdiff.mp hp).2
  have hlarge := hDlarge p hpS hpnot
  have hsub : D p ⊆ activeOutside C S z p := by
    intro w hw
    exact Finset.mem_filter.mpr (Finset.mem_filter.mp hw).2
  refine ⟨hlarge.trans (Finset.card_le_card hsub), ?_⟩
  intro q hqout
  by_contra! hsmall
  let E := activeOutside C S z p \ activeOutside C S z q
  have hEW : E ⊆ outsideWide C S z := by
    intro w hw
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hw).1).1
  obtain ⟨U, hUcard, hUS, hUactive⟩ := outside_activation_set C S z i hG E hEW
  let V := insert q U
  have hVcard : V.card < k := by
    have hc := Finset.card_insert_le q U
    change V.card ≤ U.card + 1 at hc
    change E.card < k - 1 at hsmall
    omega
  have hVS : Disjoint V (S i) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    rcases Finset.mem_insert.mp hv with rfl | hvU
    · exact hqout hvS
    · exact Finset.disjoint_left.mp hUS hvU hvS
  have hfalse : value C (bit V) o = false := by
    apply hneg (bit V)
    · rwa [bit_weight]
    · exact bit_zero_on V (S i) hVS
  have htrue : value C (bit V) o = true := by
    apply hcut _ _ _ o (Finset.mem_singleton_self _) (hpos p hpS)
    intro w hw hv
    rcases missed_frontier_special C S z i B p hpS hpnot w hw hv with hwz | hwW
    · rw [hwz]
      exact hz _
    · have hwp : w ∈ activeOutside C S z p :=
        Finset.mem_filter.mpr ⟨hwW, (mem_support C w p).mpr hv⟩
      by_cases hwq : w ∈ activeOutside C S z q
      · have hqvalue := (mem_support C w q).mp (Finset.mem_filter.mp hwq).2
        apply value_mono C hG (fun v => decide (v = q)) (bit V) _ w hqvalue
        intro v hvq
        have he : v = q := of_decide_eq_true hvq
        subst v
        exact decide_eq_true (Finset.mem_insert_self q U)
      · have hwE : w ∈ E := Finset.mem_sdiff.mpr ⟨hwp, hwq⟩
        apply value_mono C hG (bit U) (bit V) _ w (hUactive w hwE)
        intro v hvU
        exact decide_eq_true (Finset.mem_insert_of_mem (of_decide_eq_true hvU))
  rw [hfalse] at htrue
  contradiction

end PEqualNP.Research.DeficientSeparation

#print axioms PEqualNP.Research.DeficientSeparation.deficient_separated_points
