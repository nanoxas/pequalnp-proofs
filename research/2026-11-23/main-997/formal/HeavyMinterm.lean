import SmallWindow

/-
Complementary heavy/light/minterm accounting for L-meta-997. The heavy OR
and light-output sets adapt the checked SmallWindow argument. The extra
prefix branch count is supplied by MintermSlack, whose evaluation helpers
reuse accepted L-meta-986 under Apache-2.0. The unrestricted target is open.
-/

namespace PEqualNP.Research.HeavyMinterm

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OrPrivateCount
open PEqualNP.Research.HeavyReplacement

noncomputable def lightNontrivial {n m : ℕ}
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => ¬ Disjoint (S i) Y ∧ 2 ≤ (S i).card

noncomputable def nonemptyTargets {n m : ℕ}
    (S : Fin m → Finset (Fin n)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => 0 < (S i).card

/-- Heavy OR charges, large light outputs, prefix AND branches, and the
exceptional wire are disjoint under the same-index replacement interface. -/
theorem heavy_light_minterm_bound {n m k : ℕ} (C D : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Y : Finset (Fin n))
    (u z : ℕ)
    (hsize : D.size = C.size)
    (hG : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hbelow : ∀ (x : Fin n → Bool) (w : ℕ), value D x w = true → value C x w = true)
    (hagrees : ∀ x : Fin n → Bool, (∀ p ∈ Y, x p = true) →
      ∀ w, value D x w = value C x w)
    (hprefix : ∀ (x : Fin n → Bool) (w : ℕ), w < z → value D x w = value C x w)
    (hzfalse : ∀ x : Fin n → Bool, value D x z = false)
    (hzoriginal : value C (fun _ : Fin n => false) z = true)
    (hzgate : z ∈ Finset.Ico n (n + C.size))
    (huz : u < z)
    (hy : value D (bit Y) u = true)
    (hmin : ∀ x : Fin n → Bool, value D x u = true →
      k ≤ (Finset.univ.filter (fun p : Fin n => x p = true)).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - 1 else 0) +
      (lightNontrivial S Y).card + k ≤ C.size := by
  classical
  let H := Finset.univ.filter fun i : Fin m => Disjoint (S i) Y
  let L := Finset.univ.filter fun i : Fin m => ¬ Disjoint (S i) Y ∧ 2 ≤ (S i).card
  let A := H.biUnion fun i => heavyAssigned D Y (S i)
  let B := L.image out
  let E := (branches D (bit Y)).filter (· ≤ u)
  let R := Finset.Ico n (n + C.size)
  have hneg (i : Fin m) : value D (negative (S i)) (out i) = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    have h := hbelow (negative (S i)) (out i) hv
    rw [hout] at h
    simp [negative] at h
  have hpos (i : Fin m) (p : Fin n) (hp : p ∈ S i) :
      value D (baseSamples Y p) (out i) = true := by
    rw [hagrees (baseSamples Y p) (by intro q hq; exact decide_eq_true (Or.inl hq))]
    rw [hout]
    exact decide_eq_true ⟨p, hp, by simp [baseSamples]⟩
  have hd : (H : Set (Fin m)).PairwiseDisjoint (fun i => heavyAssigned D Y (S i)) := by
    intro i hi j hj hij
    have hiY : Disjoint Y (S i) := (Finset.mem_filter.mp hi).2.symm
    have hjY : Disjoint Y (S j) := (Finset.mem_filter.mp hj).2.symm
    refine Finset.disjoint_left.mpr fun w hwi hwj => ?_
    have hai := (Finset.mem_filter.mp hwi).2.2.1
    have haj := (Finset.mem_filter.mp hwj).2.2.1
    have hwide := (Finset.mem_filter.mp hwi).2.2.2
    have hsub : sampleSupport D (baseSamples Y) w ⊆ S i ∩ S j := by
      intro p hp
      exact Finset.mem_inter.mpr
        ⟨sampleSupport_subset D hG Y (S i) hiY w hai hp,
         sampleSupport_subset D hG Y (S j) hjY w haj hp⟩
    have hcard := Finset.card_le_card hsub
    have hsmall := hinter i j hij
    omega
  have hA : (∑ i ∈ H, ((S i).card - 1)) ≤ A.card := by
    calc
      (∑ i ∈ H, ((S i).card - 1)) ≤ ∑ i ∈ H, (heavyAssigned D Y (S i)).card := by
        apply Finset.sum_le_sum
        intro i hi
        exact heavy_or_count D hG Y (S i) (Finset.mem_filter.mp hi).2.symm (out i) (hneg i) (hpos i)
      _ = A.card := (Finset.card_biUnion hd).symm
  have hB : B.card = L.card := by
    exact Finset.card_image_of_injOn (output_injOn_large C S out L hout hinter
      (fun i hi => (Finset.mem_filter.mp hi).2.2))
  have hAfalse : ∀ w ∈ A, value D (bit Y) w = false := by
    intro w hw
    obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw
    have hdis : Disjoint Y (S i) := (Finset.mem_filter.mp hi).2.symm
    have ha := (Finset.mem_filter.mp hwi).2.2.1
    apply Bool.eq_false_iff.mpr
    intro hv
    have hm : value D (negative (S i)) w = true := by
      apply value_mono D hG (bit Y) (negative (S i)) _ w hv
      intro p hp
      apply decide_eq_true
      exact fun hpS => Finset.disjoint_left.mp hdis (of_decide_eq_true hp) hpS
    rw [ha] at hm
    contradiction
  have hBtrue : ∀ w ∈ B, value D (bit Y) w = true := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hhit := (Finset.mem_filter.mp hi).2.1
    obtain ⟨p, hpS, hpY⟩ := Finset.not_disjoint_iff.mp hhit
    rw [hagrees (bit Y) (by intro q hq; exact decide_eq_true hq), hout]
    exact decide_eq_true ⟨p, hpS, decide_eq_true hpY⟩
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro w ha hb
    have h := hBtrue w hb
    rw [hAfalse w ha] at h
    contradiction
  have hAsub : A ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    have h := (Finset.mem_filter.mp hi).1
    simpa only [hsize] using h
  have hBsub : B ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_Ico.mpr (output_gate_of_card C S out hout i (Finset.mem_filter.mp hi).2.2)

  have hEsub : E ⊆ R.erase z := by
    intro w hw
    obtain ⟨hwe, hwu⟩ := Finset.mem_filter.mp hw
    have hgate := (Finset.mem_filter.mp hwe).1
    apply Finset.mem_erase.mpr
    refine ⟨by omega, ?_⟩
    simpa only [hsize] using hgate
  have hAz : z ∉ A := by
    intro hzA
    obtain ⟨i, _, hzi⟩ := Finset.mem_biUnion.mp hzA
    have hwide := (Finset.mem_filter.mp hzi).2.2.2
    have he : sampleSupport D (baseSamples Y) z = ∅ := by
      ext p
      simp [mem_sampleSupport, hzfalse]
    simp [he] at hwide
  have hBz : z ∉ B := by
    intro hzB
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hzB
    have ho := hout i (fun _ => false)
    rw [he, hzoriginal] at ho
    simp at ho
  have hAE : Disjoint A E := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwE
    have hfalse := hAfalse w hwA
    have htrue := (Finset.mem_filter.mp (Finset.mem_filter.mp hwE).1).2.2.2
    rw [hfalse] at htrue
    contradiction
  have hBE : Disjoint B E := by
    apply Finset.disjoint_left.mpr
    intro w hwB hwE
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hwB
    obtain ⟨hwe, hwu⟩ := Finset.mem_filter.mp hwE
    have hempty := (Finset.mem_filter.mp hwe).2.2.1
    have hs : support (n := n) D (out i) = support (n := n) C (out i) := by
      ext p
      simp only [mem_support]
      rw [hprefix _ _ (by omega)]
    rw [hs, output_support_eq C S out hout i] at hempty
    have hlarge := (Finset.mem_filter.mp hi).2.2
    simp [hempty] at hlarge
  have hABE : Disjoint (A ∪ B) E := by
    apply Finset.disjoint_left.mpr
    intro w hw hwE
    rcases Finset.mem_union.mp hw with hwA | hwB
    · exact Finset.disjoint_left.mp hAE hwA hwE
    · exact Finset.disjoint_left.mp hBE hwB hwE
  have hAsub' : A ⊆ R.erase z := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨by intro e; exact hAz (e ▸ hw), hAsub hw⟩
  have hBsub' : B ⊆ R.erase z := by
    intro w hw
    exact Finset.mem_erase.mpr ⟨by intro e; exact hBz (e ▸ hw), hBsub hw⟩
  have hcards : A.card + B.card + E.card ≤ (R.erase z).card := by
    rw [← Finset.card_union_of_disjoint hAB, ← Finset.card_union_of_disjoint hABE]
    exact Finset.card_le_card (Finset.union_subset (Finset.union_subset hAsub' hBsub') hEsub)
  have hremove : (R.erase z).card + 1 = C.size := by
    have h := Finset.card_erase_add_one hzgate
    simpa [R] using h
  have hbranch := minterm_bound D hG (bit Y) u k hy hmin
  change k ≤ E.card + 1 at hbranch
  have hHsum : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - 1 else 0) =
      ∑ i ∈ H, ((S i).card - 1) := by simp [H, Finset.sum_filter]
  have hL : (lightNontrivial S Y).card = L.card := rfl
  rw [hHsum, hL]
  omega

/-- Original-circuit form of the complementary count. Empty and singleton
targets remain in the family and cause no extra counting assumptions. -/
theorem one_not_heavy_minterm_bound {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hk : 2 ≤ Y.card)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - 1 else 0) +
      (lightNontrivial S Y).card + Y.card ≤ C.size := by
  classical
  have hzero : value C (fun _ : Fin n => false) (n + t) = true :=
    hbelow _ (by simpa using (show 0 < Y.card by omega))
  obtain ⟨i0, hit, hop, u, hhead, hlt⟩ :=
    not_of_window_drop C t (bit Y) hgate hnot hzero hfalse
  have hu : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q = i0 := by
    intro q hq
    apply Fin.ext
    exact (hnot q hq).trans hit.symm
  let D := repl0C C.gates i0.val
  have hG := repl0C_gates C.gates i0 hgate hu
  have hy : value D (bit Y) u = true := by
    rw [repl0C_prefix_eq C.gates i0 C.output (bit Y) u hlt]
    have h : value ⟨C.gates, C.output⟩ (bit Y) (n + i0.val) = false := by
      simpa only [hit] using hfalse
    rw [orig_not_value C.gates i0 C.output u hop hhead hlt (bit Y)] at h
    simpa using h
  have hmin : ∀ x : Fin n → Bool, value D x u = true →
      Y.card ≤ (Finset.univ.filter (fun p => x p = true)).card := by
    intro x hx
    by_contra! hsmall
    have hz : value ⟨C.gates, C.output⟩ x (n + i0.val) = true := by
      simpa only [hit] using hbelow x hsmall
    have hv : value ⟨C.gates, C.output⟩ x u = true := by
      rw [← repl0C_prefix_eq C.gates i0 C.output x u hlt]
      exact hx
    rw [orig_not_value C.gates i0 C.output u hop hhead hlt x, hv] at hz
    contradiction
  apply heavy_light_minterm_bound C D S out Y u (n + i0.val)
    (by simp [D, repl0C, Circuit.size]) hG
    (repl0C_le C.gates i0 C.output hgate hu)
    _ (repl0C_prefix_eq C.gates i0 C.output) (repl0C_false C.gates i0)
    (by simpa only [hit] using hzero) _ hlt hy hmin hinter hout
  · intro x hx w
    apply repl0C_above_eq C.gates i0 C.output u hgate hu hop hhead hlt (bit Y) x
      (by simpa only [hit] using hfalse) _ w
    intro p hp
    exact hx p (of_decide_eq_true hp)
  · exact Finset.mem_Ico.mpr ⟨by omega, by
      unfold Circuit.size
      exact Nat.add_lt_add_left i0.isLt n⟩

/-- Exact finite decomposition of the posted weighted sum for k>=2. -/
lemma weighted_sum_decomposition {n m k : ℕ}
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) (hk : 2 ≤ k) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min k (S i).card) =
      (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - 1 else 0) +
      (lightNontrivial S Y).card +
      (∑ i : Fin m, if ¬ Disjoint (S i) Y then min k (S i).card - 2 else 0) +
      (nonemptyTargets S).card := by
  classical
  have hterm (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min k (S i).card) =
      (if Disjoint (S i) Y then (S i).card - 1 else 0) +
      (if ¬ Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0) +
      (if ¬ Disjoint (S i) Y then min k (S i).card - 2 else 0) +
      (if 0 < (S i).card then 1 else 0) := by
    by_cases hd : Disjoint (S i) Y
    · simp only [hd, ite_true, not_true_eq_false, false_and, ite_false, Nat.add_zero]
      split_ifs <;> omega
    · simp only [hd, ite_false, not_false_eq_true, true_and, ite_true, Nat.zero_add]
      by_cases hlarge : 2 ≤ (S i).card
      · have hmin : 2 ≤ min k (S i).card := by omega
        simp only [ite_eq_left hlarge, ite_eq_left (show 0 < (S i).card by omega)]
        omega
      · by_cases hpos : 0 < (S i).card
        · simp only [ite_eq_right hlarge, ite_eq_left hpos]
          omega
        · simp only [ite_eq_right hlarge, ite_eq_right hpos]
          omega
  have hL : (∑ i : Fin m, if ¬ Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0) =
      (lightNontrivial S Y).card := by
    rw [Finset.card_eq_sum_ones]
    simp [lightNontrivial]
  have hP : (∑ i : Fin m, if 0 < (S i).card then 1 else 0) =
      (nonemptyTargets S).card := by
    rw [Finset.card_eq_sum_ones]
    simp [nonemptyTargets]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin m))) (s₂ := Finset.univ)
    rfl (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, hL, hP] using hsum

/-- The complementary sufficient criterion, retaining the empty-target slack. -/
theorem heavy_refund_bound_of_counts {n m k : ℕ}
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) (N R : ℕ)
    (hk : 2 ≤ k)
    (hbase : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - 1 else 0) +
      (lightNontrivial S Y).card + k ≤ N)
    (hlight : (∑ i : Fin m, if ¬ Disjoint (S i) Y then min k (S i).card - 2 else 0) ≤
      R + k + (m - (nonemptyTargets S).card)) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
      N + R + m := by
  rw [weighted_sum_decomposition S Y hk]
  have hP : (nonemptyTargets S).card ≤ m := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin m))
      (fun i => 0 < (S i).card)
    simpa only [nonemptyTargets, Finset.card_univ, Fintype.card_fin] using h
  omega

/-- The original assumptions plus the complementary light-excess condition
prove the exact posted refund inequality. -/
theorem one_not_refund_bound_of_light_excess {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hk : 2 ≤ Y.card)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false)
    (hlight : (∑ i : Fin m, if ¬ Disjoint (S i) Y then min Y.card (S i).card - 2 else 0) ≤
      (refundGates C S Y).card + Y.card + (m - (nonemptyTargets S).card)) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  exact heavy_refund_bound_of_counts S Y C.size (refundGates C S Y).card hk
    (one_not_heavy_minterm_bound C S out t Y hk hgate hnot hinter hout hbelow hfalse) hlight

end PEqualNP.Research.HeavyMinterm

#print axioms PEqualNP.Research.HeavyMinterm.heavy_light_minterm_bound
#print axioms PEqualNP.Research.HeavyMinterm.one_not_heavy_minterm_bound
#print axioms PEqualNP.Research.HeavyMinterm.weighted_sum_decomposition
#print axioms PEqualNP.Research.HeavyMinterm.one_not_refund_bound_of_light_excess
