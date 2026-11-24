import MintermSlack

/-
Research helper for the light-input window. The cut and singleton-support
argument adapts the accepted L-meta-270/L-meta-782 proofs, with the monotone
fan-in-at-most-two helpers reused from L-meta-986 through MintermSlack.
The sources and this adaptation use the Apache-2.0 license.

The exceptional wire is constant true. Frontier wires already true on the
zero input transfer freely before the singleton-support cases are considered.
This file does not claim the complete L-meta-997 statement.
-/

namespace PEqualNP.Research.MintermSlack

open PEqualNP.CircuitLowerBounds

def lightAssigned {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (z : ℕ) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    w ≠ z ∧ support (n := n) C w ⊆ S ∧ 2 ≤ (support (n := n) C w).card

/-- A small cut cannot separate all accepted singleton inputs from all sparse
inputs disjoint from S. Constant-true boundary wires need no chosen input. -/
lemma light_card_assigned {n k c : ℕ} (C : Circuit) (S : Finset (Fin n)) (o z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ S)
    (hsparse : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ S, x q = false) → value C x o = false)
    (hk : c < k) (hc : c + 1 ≤ S.card) :
    c ≤ (lightAssigned C S z).card := by
  classical
  let G := lightAssigned C S z
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega

  let clean (w : ℕ) : Finset (Fin n) :=
    if value C (fun _ : Fin n => false) w = true then ∅
    else if support (n := n) C w ⊆ S then support (n := n) C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hzero : value C (fun _ : Fin n => false) w = true
    · simp [clean, hzero]
    by_cases hs : support (n := n) C w ⊆ S
    · change (if value C (fun _ : Fin n => false) w = true then ∅
        else if support (n := n) C w ⊆ S then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_right hzero, ite_eq_left hs]
      by_contra! hlarge
      have hwz : w ≠ z := by
        intro he
        subst w
        exact hzero (hz (fun _ => false))
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hwz, hs, by omega⟩)
    · simp [clean, hzero, hs]
  have hcover : (B.biUnion clean).card < S.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover

  let D := B.filter fun w =>
    value C (fun _ : Fin n => false) w ≠ true ∧ ¬ support (n := n) C w ⊆ S
  have hout (w : {w // w ∈ D}) :
      ∃ q : Fin n, q ∈ support (n := n) C w.val ∧ q ∉ S := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2.2 h
  choose q hq using hout
  let U := D.attach.image q
  let x : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card < k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ c := hb
    _ < k := hk
  have hxfalse : value C x o = false := by
    apply hsparse x
    · have hset : Finset.univ.filter (fun r => x r = true) = U := by
        ext r
        simp [x]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [x, hnot]
  have hxtrue : value C x o = true := by
    apply hcut (fun r => decide (r = p)) x _ o
      (Finset.mem_singleton_self o) ((ho p).mpr hp)
    intro w hw hv
    by_cases hzero : value C (fun _ : Fin n => false) w = true
    · apply value_mono C hG (fun _ : Fin n => false) x _ w hzero
      intro r hr
      contradiction
    by_cases hs : support (n := n) C w ⊆ S
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_right hzero, ite_eq_left hs, mem_support] using hv⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hzero, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) x _ w
        ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [x, hm]
  simp [hxfalse] at hxtrue

/-- Agreement with OR(S) below weight k pays for min(k,|S|)-1 private wide
singleton-support gates, excluding a specified constant-true wire. -/
theorem light_window_bound {n k : ℕ} (C : Circuit) (S : Finset (Fin n)) (o z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hwindow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    min k S.card - 1 ≤ (lightAssigned C S z).card := by
  classical
  by_cases hsmall : min k S.card ≤ 1
  · have hzero : min k S.card - 1 = 0 := by omega
    simp [hzero]
  have hlarge : 2 ≤ min k S.card := by omega
  have hk : 1 < k := by have := Nat.min_le_left k S.card; omega
  have ho : ∀ p : Fin n, value C (fun q => decide (q = p)) o = true ↔ p ∈ S := by
    intro p
    have hset : Finset.univ.filter (fun q : Fin n => decide (q = p) = true) = {p} := by
      ext q
      simp
    have hweight : (Finset.univ.filter (fun q : Fin n => decide (q = p) = true)).card < k := by
      rw [hset, Finset.card_singleton]
      exact hk
    rw [hwindow (fun q : Fin n => decide (q = p)) hweight]
    simp
  have hsparse : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun q => x q = true)).card < k →
      (∀ q ∈ S, x q = false) → value C x o = false := by
    intro x hx hS
    rw [hwindow x hx]
    have hnone : ¬ ∃ p ∈ S, x p = true := by
      rintro ⟨p, hp, hv⟩
      rw [hS p hp] at hv
      contradiction
    simp [hnone]
  apply light_card_assigned C S o z hG hz ho hsparse
  · have := Nat.min_le_left k S.card
    omega
  · have := Nat.min_le_right k S.card
    omega

lemma lightAssigned_pairwise_disjoint {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint
      (fun i => lightAssigned C (S i) z) := by
  classical
  intro i _ j _ hij
  refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
  rcases (Finset.mem_filter.mp hwi).2 with ⟨_, hi, hwide⟩
  rcases (Finset.mem_filter.mp hwj).2 with ⟨_, hj, _⟩
  have hsub : support (n := n) C w ⊆ S i ∩ S j :=
    fun p hp => Finset.mem_inter.mpr ⟨hi hp, hj hp⟩
  have hle := Finset.card_le_card hsub
  have hsmall := hinter i j hij
  omega

/-- The private light charges sum without overlap for a linear set family. -/
theorem light_window_sum_bound {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hwindow : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, (min k (S i).card - 1)) ≤
      (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card := by
  classical
  calc
    (∑ i : Fin m, (min k (S i).card - 1)) ≤
        ∑ i : Fin m, (lightAssigned C (S i) z).card :=
      Finset.sum_le_sum fun i _ => light_window_bound C (S i) (o i) z hG hz (hwindow i)
    _ = (Finset.univ.biUnion (fun i => lightAssigned C (S i) z)).card :=
      (Finset.card_biUnion (lightAssigned_pairwise_disjoint C S z hinter)).symm

lemma lightAssigned_union_subset {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) :
    Finset.univ.biUnion (fun i => lightAssigned C (S i) z) ⊆
      (Finset.Ico n (n + C.size)).erase z := by
  classical
  intro w hw
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
  have hmem := Finset.mem_filter.mp hi
  exact Finset.mem_erase.mpr ⟨hmem.2.1, hmem.1⟩

end PEqualNP.Research.MintermSlack

#print axioms PEqualNP.Research.MintermSlack.light_window_bound
#print axioms PEqualNP.Research.MintermSlack.light_window_sum_bound
