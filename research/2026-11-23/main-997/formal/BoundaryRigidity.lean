import BoundaryActivation

/-
A deficient private class leaves many singleton points on its cut. Each
such point activates at least k outsiders. This supplies the sufficient
outside-count range r <= 2*k-2 without rewriting the circuit. Apache-2.0.
-/

namespace PEqualNP.Research.BoundaryActivation

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation

/-- A deficient class has at least k+1 singleton points, each activating at
least k global outsiders. The same cut frontier supplies every point. -/
lemma deficient_popular_points {n m k : ℕ} (C : Circuit)
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
      ∀ p ∈ M, k ≤ (activeOutside C S z p).card := by
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
  exact hlarge.trans (Finset.card_le_card hsub)

/-- A point outside a target that activates k outsiders can be supplemented
by one point for each remaining outsider. If r <= 2*k-2, this is below k. -/
lemma popular_point_count {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hk : 2 ≤ k)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hW : (outsideWide C S z).card ≤ 2 * k - 2)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hneg : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      (∀ p ∈ S i, x p = false) → value C x o = false)
    (p : Fin n) (hpout : p ∉ S i)
    (hpopular : k ≤ (activeOutside C S z p).card) :
    (S i).card - 1 ≤ (lightAssigned C (S i) z).card := by
  classical
  let W := outsideWide C S z
  let A := activeOutside C S z p
  let D := W \ A
  have hA : A ⊆ W := Finset.filter_subset _ _
  have hDA : D.card + A.card = W.card := Finset.card_sdiff_add_card_eq_card hA
  obtain ⟨U, hUcard, hUS, hUactive⟩ :=
    outside_activation_set C S z i hG D Finset.sdiff_subset
  let V := insert p U
  have hVcard : V.card < k := by
    have hv := Finset.card_insert_le p U
    change V.card ≤ U.card + 1 at hv
    change W.card ≤ 2 * k - 2 at hW
    change k ≤ A.card at hpopular
    omega
  have hVS : Disjoint V (S i) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvS
    rcases Finset.mem_insert.mp hv with rfl | hvU
    · exact hpout hvS
    · exact Finset.disjoint_left.mp hUS hvU hvS
  have hfalse : value C (bit V) o = false := by
    apply hneg (bit V)
    · rwa [bit_weight]
    · exact bit_zero_on V (S i) hVS
  apply private_count_of_activation C S z hG hz hinter i o hpos (bit V) hfalse
  intro w hw
  by_cases hwp : p ∈ support (n := n) C w
  · apply value_mono C hG (fun q => decide (q = p)) (bit V) _ w
      ((mem_support C w p).mp hwp)
    intro q hq
    have he : q = p := of_decide_eq_true hq
    subst q
    exact decide_eq_true (Finset.mem_insert_self p U)
  · have hwD : w ∈ D := by
      apply Finset.mem_sdiff.mpr
      refine ⟨hw, ?_⟩
      intro hwA
      exact hwp (Finset.mem_filter.mp hwA).2
    apply value_mono C hG (bit U) (bit V) _ w (hUactive w hwD)
    intro q hq
    exact decide_eq_true (Finset.mem_insert_of_mem (of_decide_eq_true hq))

lemma window_singleton_positive {n k : ℕ} (C : Circuit)
    (S : Finset (Fin n)) (o : ℕ) (hk : 2 ≤ k)
    (hwindow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    ∀ p ∈ S, value C (fun q => decide (q = p)) o = true := by
  classical
  intro p hp
  have hset : Finset.univ.filter (fun q : Fin n => decide (q = p) = true) = {p} := by
    ext q
    simp
  have hweight : (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card < k := by
    rw [hset, Finset.card_singleton]
    omega
  rw [hwindow _ hweight]
  exact decide_eq_true ⟨p, hp, by simp⟩

lemma window_negative {n k : ℕ} (C : Circuit)
    (S : Finset (Fin n)) (o : ℕ)
    (hwindow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      (∀ p ∈ S, x p = false) → value C x o = false := by
  classical
  intro x hx hzero
  rw [hwindow x hx]
  apply decide_eq_false
  rintro ⟨p, hp, hv⟩
  rw [hzero p hp] at hv
  contradiction

/-- In the range r <= 2*k-2, at most one private class is deficient.
Its entire deficit is paid by the r global outsiders. -/
theorem boundary_activation_sum {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (z : ℕ)
    (hk : 2 ≤ k)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hW : (outsideWide C S z).card ≤ 2 * k - 2)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, ((S i).card - 1)) ≤
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card +
        (outsideWide C S z).card := by
  classical
  have hpos (i : Fin m) := window_singleton_positive C (S i) (out i) hk (hwindow i)
  have hneg (i : Fin m) := window_negative C (S i) (out i) (hwindow i)
  have hsumcard : (∑ i : Fin m, (lightAssigned C (S i) z).card) =
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card :=
    (Finset.card_biUnion (lightAssigned_pairwise_disjoint C S z hinter)).symm
  by_cases hall : ∀ i : Fin m, (S i).card - 1 ≤ (lightAssigned C (S i) z).card
  · have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hall i)
    rw [hsumcard] at hsum
    exact hsum.trans (Nat.le_add_right _ _)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    obtain ⟨M, hMS, hMcard, hMpopular⟩ :=
      deficient_popular_points C S z hG hz hinter i (out i) (hpos i) (hneg i) hi
    have hother (j : Fin m) (hji : j ≠ i) :
        (S j).card - 1 ≤ (lightAssigned C (S j) z).card := by
      have hex : ∃ p ∈ M, p ∉ S j := by
        by_contra! hn
        have hsub : M ⊆ S i ∩ S j := fun p hp => Finset.mem_inter.mpr ⟨hMS hp, hn p hp⟩
        have hc := Finset.card_le_card hsub
        have hs := hinter i j hji.symm
        omega
      obtain ⟨p, hp, hpnot⟩ := hex
      exact popular_point_count C S z hk hG hz hinter hW j (out j) (hpos j) (hneg j)
        p hpnot (hMpopular p hp)
    have hzero : value C (fun _ : Fin n => false) (out i) = false := by
      apply hneg i
      · simpa using (show 0 < k by omega)
      · simp
    have hpaid := compensated_private_count C S z hG hz hinter i (out i) (hpos i) hzero
    have hterm (j : Fin m) :
        (S j).card - 1 ≤ (lightAssigned C (S j) z).card +
          (if j = i then (outsideWide C S z).card else 0) := by
      by_cases hji : j = i
      · subst j
        simpa only [ite_true] using hpaid
      · simpa only [ite_eq_right hji, Nat.add_zero] using hother j hji
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun j _ => hterm j)
    simpa only [Finset.sum_add_distrib, hsumcard, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using hsum

end PEqualNP.Research.BoundaryActivation

#print axioms PEqualNP.Research.BoundaryActivation.deficient_popular_points
#print axioms PEqualNP.Research.BoundaryActivation.popular_point_count
#print axioms PEqualNP.Research.BoundaryActivation.boundary_activation_sum
