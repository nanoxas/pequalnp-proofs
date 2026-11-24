import NotWindow

/-
Exact refund predicate and sufficient cases of the L-meta-997 inequality.
The full overlap problem is not claimed. Output validity and distinctness
are stated separately so other charging arguments can reuse them.
-/

namespace PEqualNP.Research.MintermSlack

open PEqualNP.CircuitLowerBounds

lemma output_support_eq {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) (i : Fin m) :
    support (n := n) C (out i) = S i := by
  ext p
  simp only [mem_support]
  rw [hout i (fun q => decide (q = p))]
  simp

lemma output_gate_of_card {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (hcard : 2 ≤ (S i).card) :
    n ≤ out i ∧ out i < n + C.size := by
  apply support_gate C (out i)
  rw [output_support_eq C S out hout i]
  exact hcard

lemma output_ne_of_ne_of_card {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i j : Fin m) (hij : i ≠ j) (hcard : 2 ≤ (S i).card) :
    out i ≠ out j := by
  intro he
  have hsets : S i = S j := by
    rw [← output_support_eq C S out hout i, ← output_support_eq C S out hout j, he]
  have hsmall := hinter i j hij
  rw [← hsets, Finset.inter_self] at hsmall
  omega

lemma output_injOn_large {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (I : Finset (Fin m))
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hlarge : ∀ i ∈ I, 2 ≤ (S i).card) : Set.InjOn out I := by
  intro i hi j _ he
  by_contra hij
  exact output_ne_of_ne_of_card C S out hout hinter i j hij (hlarge i hi) he

/-- The exact two-clause gate predicate from the posted refund count. -/
noncomputable def refundGates {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) : Finset (Fin C.gates.length) := by
  classical
  exact Finset.univ.filter fun g =>
    (∃ i : Fin m, ∀ p : Fin n,
      value C (fun v => decide (v = p)) (n + g.val) = true ↔ p ∈ S i) ∧
    (∃ i : Fin m, Disjoint (S i) Y ∧ ∀ p : Fin n, p ∉ Y →
      (value C (fun v => decide (v ∈ Y ∨ v = p)) (n + g.val) = true ↔ p ∈ S i))

/-- The right-hand side below is copied verbatim from the posted refund
Finset expression, including its guarded-equivalence parentheses. -/
lemma refundGates_eq_posted {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) :
    refundGates C S y = (Finset.univ.filter (fun g : Fin C.gates.length => (∃ i : Fin m, ∀ p : Fin n, (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧ (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y → ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD (n + g) false = true ↔ p ∈ S i)))) := by
  classical
  rfl

noncomputable def heavyNontrivial {n m : ℕ}
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter fun i => Disjoint (S i) Y ∧ 2 ≤ (S i).card

theorem forced_refund_count {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (Y : Finset (Fin n))
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (heavyNontrivial S Y).card ≤ (refundGates C S Y).card := by
  classical
  let H := heavyNontrivial S Y
  have hlarge (i : ↥H) : 2 ≤ (S i.val).card := (Finset.mem_filter.mp i.property).2.2
  have hvalid (i : ↥H) : n ≤ out i.val ∧ out i.val < n + C.size :=
    output_gate_of_card C S out hout i.val (hlarge i)
  let f : ↥H → Fin C.gates.length := fun i =>
    ⟨out i.val - n, by
      have hlo := (hvalid i).1
      have hhi := (hvalid i).2
      unfold Circuit.size at hhi
      omega⟩
  have hwire (i : ↥H) : n + (f i).val = out i.val := by
    have := (hvalid i).1
    change n + (out i.val - n) = out i.val
    omega
  have hf : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    by_contra hij
    have hne := output_ne_of_ne_of_card C S out hout hinter i.val j.val hij (hlarge i)
    apply hne
    rw [← hwire i, ← hwire j, he]
  have hmem (i : ↥H) : f i ∈ refundGates C S Y := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · refine ⟨i.val, ?_⟩
      intro p
      rw [hwire i, ← mem_support, output_support_eq C S out hout i.val]
    · have hdis : Disjoint (S i.val) Y := (Finset.mem_filter.mp i.property).2.1
      refine ⟨i.val, hdis, ?_⟩
      intro p _
      rw [hwire i, hout i.val (fun v => decide (v ∈ Y ∨ v = p))]
      constructor
      · intro ht
        obtain ⟨v, hvS, hv⟩ := of_decide_eq_true ht
        rcases of_decide_eq_true hv with hvY | he
        · exact False.elim (Finset.disjoint_left.mp hdis hvS hvY)
        · subst v
          exact hvS
      · intro hp
        apply decide_eq_true
        exact ⟨p, hp, decide_eq_true (Or.inr rfl)⟩
  have hsubset : Finset.univ.image f ⊆ refundGates C S Y := by
    intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact hmem i
  have hcard : (Finset.univ.image f).card = H.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  rw [← hcard]
  exact Finset.card_le_card hsubset

/-- A purely finite arithmetic criterion. The excess allows large heavy sets
provided the total amount above k+1 is at most k. -/
theorem refund_bound_of_counts {n m k : ℕ}
    (S : Fin m → Finset (Fin n)) (Y : Finset (Fin n)) (N R : ℕ)
    (hk : 2 ≤ k)
    (hbase : (∑ i : Fin m, (min k (S i).card - 1)) + k ≤ N)
    (hrefund : (heavyNontrivial S Y).card ≤ R)
    (hexcess : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - k - 1 else 0) ≤ k) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤ N + R + m := by
  classical
  have hterm (i : Fin m) :
      (if Disjoint (S i) Y then (S i).card else min k (S i).card) ≤
        (min k (S i).card - 1) + 1 +
          (if Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0) +
          (if Disjoint (S i) Y then (S i).card - k - 1 else 0) := by
    by_cases hd : Disjoint (S i) Y
    · by_cases hsmall : (S i).card ≤ k
      · have hm : min k (S i).card = (S i).card := Nat.min_eq_right hsmall
        by_cases hlarge : 2 ≤ (S i).card
        · simp only [ite_eq_left hd, ite_eq_left (And.intro hd hlarge), hm]
          omega
        · have hnot : ¬ (Disjoint (S i) Y ∧ 2 ≤ (S i).card) := fun h => hlarge h.2
          simp only [ite_eq_left hd, ite_eq_right hnot, hm]
          omega
      · have hm : min k (S i).card = k := Nat.min_eq_left (by omega)
        have hlarge : 2 ≤ (S i).card := by omega
        simp only [ite_eq_left hd, ite_eq_left (And.intro hd hlarge), hm]
        omega
    · have hnot : ¬ (Disjoint (S i) Y ∧ 2 ≤ (S i).card) := fun h => hd h.1
      simp only [ite_eq_right hd, ite_eq_right hnot]
      omega
  have hcount : (∑ i : Fin m, if Disjoint (S i) Y ∧ 2 ≤ (S i).card then 1 else 0) =
      (heavyNontrivial S Y).card := by
    rw [Finset.card_eq_sum_ones (heavyNontrivial S Y)]
    simp only [heavyNontrivial, Finset.sum_filter]
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, Nat.mul_one, hcount] at hsum
  omega

/-- A sufficient condition for the exact posted refund inequality. -/
theorem one_not_refund_bound_of_excess {n m : ℕ} (C : Circuit)
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
    (hexcess : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - Y.card - 1 else 0) ≤ Y.card) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  exact refund_bound_of_counts S Y C.size (refundGates C S Y).card hk
    (one_not_window_bound C S out t (bit Y) hk hgate hnot hinter hout hbelow hfalse)
    (forced_refund_count C S out Y hout hinter) hexcess

theorem one_not_refund_bound_of_heavy_size {n m : ℕ} (C : Circuit)
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
    (hsize : ∀ i : Fin m, Disjoint (S i) Y → (S i).card ≤ Y.card + 1) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  apply one_not_refund_bound_of_excess C S out t Y hk hgate hnot hinter hout hbelow hfalse
  have hz : (∑ i : Fin m, if Disjoint (S i) Y then (S i).card - Y.card - 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases hd : Disjoint (S i) Y
    · rw [ite_eq_left hd]
      have := hsize i hd
      omega
    · rw [ite_eq_right hd]
  rw [hz]
  exact Nat.zero_le _

theorem one_not_refund_bound_all_hit {n m : ℕ} (C : Circuit)
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
    (hhit : ∀ i : Fin m, ¬ Disjoint (S i) Y) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  apply one_not_refund_bound_of_heavy_size C S out t Y hk hgate hnot hinter hout hbelow hfalse
  intro i hi
  exact False.elim (hhit i hi)

end PEqualNP.Research.MintermSlack

#print axioms PEqualNP.Research.MintermSlack.refundGates_eq_posted
#print axioms PEqualNP.Research.MintermSlack.forced_refund_count
#print axioms PEqualNP.Research.MintermSlack.one_not_refund_bound_of_excess
#print axioms PEqualNP.Research.MintermSlack.one_not_refund_bound_of_heavy_size
#print axioms PEqualNP.Research.MintermSlack.one_not_refund_bound_all_hit
