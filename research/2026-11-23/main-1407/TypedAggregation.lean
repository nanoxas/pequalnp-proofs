import Common
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace PEqualNP.MetaComplexity.L1407

open PEqualNP.CircuitLowerBounds

/-- Finite port counting with two classes of consuming gates. -/
theorem typed_port_core {α : Type*} [DecidableEq α]
    (A B D : Finset α) (output : α) (children : α → Finset α)
    (hdisjoint : Disjoint A B)
    (hlive : ∀ i ∈ A ∪ B, i ≠ output →
      (∃ j ∈ B, i ∈ children j) ∨ (∃ j ∈ D, i ∈ children j))
    (hB : ∀ j ∈ B, (children j).card ≤ 2)
    (hD : ∀ j ∈ D, (children j).card ≤ 1) :
    A.card ≤ B.card + D.card + 1 := by
  have hsub : A ∪ B ⊆ insert output ((B.biUnion children) ∪ (D.biUnion children)) := by
    intro i hi
    by_cases ho : i = output
    · subst i
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rcases hlive i hi ho with h | h
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr h)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr h)
  have htotal := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisjoint] at htotal
  have htwo : (B.biUnion children).card ≤ B.card * 2 :=
    Finset.card_biUnion_le_card_mul B children 2 hB
  have hone : (D.biUnion children).card ≤ D.card := by
    simpa using Finset.card_biUnion_le_card_mul D children 1 hD
  have hi := Finset.card_insert_le output ((B.biUnion children) ∪ (D.biUnion children))
  have hu := Finset.card_union_le (B.biUnion children) (D.biUnion children)
  omega

/-- A live wire other than the output has a valid live immediate consumer. -/
theorem live_next {n : ℕ} (C : Circuit) (w : ℕ)
    (hlive : Live (n := n) C w) (hne : w ≠ C.output) :
    ∃ j g, C.gates[j]? = some g ∧ w ∈ g.inputs ∧ w < n + j ∧
      Live (n := n) C (n + j) := by
  rcases Relation.ReflTransGen.cases_head hlive with heq | ⟨b, hread, hb⟩
  · exact False.elim (hne heq)
  · obtain ⟨j, g, hg, hbj, hw, hlt⟩ := hread
    subst b
    exact ⟨j, g, hg, hw, hlt, hb⟩

noncomputable def emptyGates {n : ℕ} (C : Circuit) : Finset ℕ := by
  classical
  exact (liveGates (n := n) C).filter (fun j => support (n := n) C (n + j) = ∅)

/-- Valid earlier gate wires of empty support read at this gate. Input wires,
forward references and nonexistent gate indices are excluded explicitly. -/
noncomputable def emptyPorts {n : ℕ} (C : Circuit) (j : ℕ) : Finset ℕ := by
  classical
  exact match C.gates[j]? with
    | none => ∅
    | some g => g.inputs.toFinset.filter
        (fun w => w < n + j ∧ n ≤ w ∧ support (n := n) C w = ∅)

noncomputable def emptyChildren {n : ℕ} (C : Circuit) (j : ℕ) : Finset ℕ :=
  (emptyPorts (n := n) C j).image (fun w => w - n)

@[simp] theorem mem_emptyGates {n : ℕ} (C : Circuit) (j : ℕ) :
    j ∈ emptyGates (n := n) C ↔
      j ∈ liveGates (n := n) C ∧ support (n := n) C (n + j) = ∅ := by
  classical
  simp [emptyGates]

theorem mem_emptyPorts {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (w : ℕ) :
    w ∈ emptyPorts (n := n) C j ↔
      w ∈ g.inputs ∧ w < n + j ∧ n ≤ w ∧ support (n := n) C w = ∅ := by
  classical
  simp [emptyPorts, hg]

theorem emptyPorts_subset_inputs {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : emptyPorts (n := n) C j ⊆ g.inputs.toFinset := by
  intro w hw
  exact List.mem_toFinset.mpr ((mem_emptyPorts C j g hg w).mp hw).1

theorem emptyChildren_card_le {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : (emptyChildren (n := n) C j).card ≤ g.inputs.length := by
  classical
  have h1 : (emptyChildren (n := n) C j).card ≤ (emptyPorts (n := n) C j).card :=
    Finset.card_image_le
  have h2 := Finset.card_le_card (emptyPorts_subset_inputs (n := n) C j g hg)
  have h3 : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le g.inputs
  omega

theorem emptyPorts_of_pair {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hinputs : g.inputs = [a, b])
    (ha : (support (n := n) C a).Nonempty) (hb : (support (n := n) C b).Nonempty) :
    emptyPorts (n := n) C j = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hw, _, _, hzero⟩ := (mem_emptyPorts C j g hg w).mp hw
  rw [hinputs] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ha.ne_empty hzero
  · exact hb.ne_empty hzero

theorem productive_emptyChildren {n : ℕ} (C : Circuit) (j : ℕ)
    (hj : j ∈ productiveGates (n := n) C) : emptyChildren (n := n) C j = ∅ := by
  obtain ⟨_, _, g, a, b, hg, _, hinputs, _, _, ha, hb⟩ := (mem_productiveGates C j).mp hj
  have h := emptyPorts_of_pair C j g a b hg hinputs ha hb
  simp [emptyChildren, h]

theorem rawMerge_emptyChildren {n : ℕ} (C : Circuit) (j : ℕ)
    (hj : j ∈ rawMergeGates (n := n) C) : emptyChildren (n := n) C j = ∅ := by
  obtain ⟨_, _, g, a, b, hg, _, hinputs, _, _, ha, hb, _⟩ := (mem_rawMergeGates C j).mp hj
  have h := emptyPorts_of_pair C j g a b hg hinputs ha hb
  simp [emptyChildren, h]

theorem productive_subset_empty {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hclean : AndBelow G C) : productiveGates (n := n) C ⊆ emptyGates (n := n) C := by
  intro j hj
  obtain ⟨hjlt, hlive, g, a, b, hg, hop, _⟩ := (mem_productiveGates C j).mp hj
  apply (mem_emptyGates C j).mpr
  exact ⟨(mem_liveGates C j).mpr ⟨hjlt, hlive⟩, support_and G C hclean j g hg hop⟩

theorem rawMerge_subset_live_sdiff_empty {n : ℕ} (C : Circuit) :
    rawMergeGates (n := n) C ⊆ liveGates (n := n) C \ emptyGates (n := n) C := by
  intro j hj
  obtain ⟨hjlt, hlive, g, a, b, hg, hop, hinputs, ha, hb, hsa, hsb, hwide⟩ :=
    (mem_rawMergeGates C j).mp hj
  apply Finset.mem_sdiff.mpr
  refine ⟨(mem_liveGates C j).mpr ⟨hjlt, hlive⟩, ?_⟩
  intro he
  have hs := ((mem_emptyGates C j).mp he).2
  rw [hs, Finset.card_empty] at hwide
  omega

/-- Any nonempty-support output has a valid nonempty-support input. Clean AND
outputs have empty support, so the only possible operation here is OR. -/
theorem nonempty_output_port {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hne : support (n := n) C (n + j) ≠ ∅) :
    ∃ a ∈ g.inputs, a < n + j ∧ (support (n := n) C a).Nonempty := by
  rcases (hmono g (List.mem_of_getElem? hg)).1 with hand | hor
  · exact False.elim (hne (support_and G C hclean j g hg hand))
  · obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    obtain ⟨a, ha, hlt, ht⟩ := or_input_true C (oneInput v) j g hg hor
      ((mem_support C (n + j) v).mp hv)
    exact ⟨a, ha, hlt, v, (mem_support C a v).mpr ht⟩

theorem nonempty_output_emptyChildren_le_one {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hne : support (n := n) C (n + j) ≠ ∅) :
    (emptyChildren (n := n) C j).card ≤ 1 := by
  classical
  obtain ⟨a, ha, hlt, hsa⟩ := nonempty_output_port G C hmono hclean j g hg hne
  have hnot : a ∉ emptyPorts (n := n) C j := by
    intro h
    exact hsa.ne_empty ((mem_emptyPorts C j g hg a).mp h).2.2.2
  have hsub : insert a (emptyPorts (n := n) C j) ⊆ g.inputs.toFinset := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact List.mem_toFinset.mpr ha
    · exact emptyPorts_subset_inputs C j g hg hw
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot] at hc
  have hl : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le g.inputs
  have hlen := (hmono g (List.mem_of_getElem? hg)).2
  have hi : (emptyChildren (n := n) C j).card ≤ (emptyPorts (n := n) C j).card :=
    Finset.card_image_le
  omega

/-- A live empty-support gate other than the output is consumed by another
live gate. The consuming empty-port index is the original gate index. -/
theorem live_empty_consumed {n : ℕ} (C : Circuit) (i : ℕ)
    (hi : i ∈ emptyGates (n := n) C) (hne : i ≠ C.output - n) :
    ∃ j ∈ liveGates (n := n) C, i ∈ emptyChildren (n := n) C j := by
  classical
  obtain ⟨hilive, hs⟩ := (mem_emptyGates C i).mp hi
  have hwne : n + i ≠ C.output := by intro h; apply hne; omega
  obtain ⟨j, g, hg, hw, hlt, hjlive⟩ := live_next C (n + i)
    ((mem_liveGates C i).mp hilive).2 hwne
  obtain ⟨hjlt, _⟩ := List.getElem?_eq_some_iff.mp hg
  refine ⟨j, (mem_liveGates C j).mpr ⟨hjlt, hjlive⟩, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨n + i, (mem_emptyPorts C j g hg (n + i)).mpr ⟨hw, hlt, by omega, hs⟩, ?_⟩
  omega

/-- Actual-model typed aggregation, without deleting or normalizing any gate. -/
theorem typed_aggregation_live_bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) :
    2 * (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card ≤
      (liveGates (n := n) C).card + 1 := by
  classical
  let A := productiveGates (n := n) C
  let E := emptyGates (n := n) C
  let L := liveGates (n := n) C
  let W := rawMergeGates (n := n) C
  let B := E \ A
  let D := (L \ E) \ W
  have hAE : A ⊆ E := productive_subset_empty G C hclean
  have hEL : E ⊆ L := fun i hi => ((mem_emptyGates C i).mp hi).1
  have hWL : W ⊆ L \ E := rawMerge_subset_live_sdiff_empty C
  have hAB : Disjoint A B := disjoint_sdiff_self_right
  have hcount := typed_port_core A B D (C.output - n) (emptyChildren (n := n) C) hAB
    (by
      intro i hi hne
      have hiE : i ∈ E := by
        rcases Finset.mem_union.mp hi with hi | hi
        · exact hAE hi
        · exact (Finset.mem_sdiff.mp hi).1
      obtain ⟨j, hj, hij⟩ := live_empty_consumed C i hiE hne
      have hjA : j ∉ A := by
        intro h
        have he := productive_emptyChildren C j h
        rw [he] at hij
        exact Finset.notMem_empty _ hij
      have hjW : j ∉ W := by
        intro h
        have he := rawMerge_emptyChildren C j h
        rw [he] at hij
        exact Finset.notMem_empty _ hij
      by_cases hjE : j ∈ E
      · exact Or.inl ⟨j, Finset.mem_sdiff.mpr ⟨hjE, hjA⟩, hij⟩
      · exact Or.inr ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hj, hjE⟩, hjW⟩, hij⟩)
    (by
      intro j hj
      have hjL : j ∈ L := hEL (Finset.mem_sdiff.mp hj).1
      have hjlt := ((mem_liveGates C j).mp hjL).1
      let g := C.gates[j]'hjlt
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
      exact (emptyChildren_card_le C j g hg).trans ((hmono g (List.mem_of_getElem? hg)).2))
    (by
      intro j hj
      obtain ⟨hjL, hjE⟩ := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1)
      have hjlt := ((mem_liveGates C j).mp hjL).1
      let g := C.gates[j]'hjlt
      have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
      have hne : support (n := n) C (n + j) ≠ ∅ := by
        intro h
        exact hjE ((mem_emptyGates C j).mpr ⟨hjL, h⟩)
      exact nonempty_output_emptyChildren_le_one G C hmono hclean j g hg hne)
  have hB : B.card + A.card = E.card := Finset.card_sdiff_add_card_eq_card hAE
  have hE : (L \ E).card + E.card = L.card := Finset.card_sdiff_add_card_eq_card hEL
  have hD : D.card + W.card = (L \ E).card := Finset.card_sdiff_add_card_eq_card hWL
  change 2 * A.card + W.card ≤ L.card + 1
  omega

theorem typed_aggregation_bound {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hmono : AndOr C) (hclean : AndBelow G C) :
    2 * (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card ≤ C.size + 1 := by
  classical
  have h := typed_aggregation_live_bound G C hmono hclean
  have hsub : liveGates (n := n) C ⊆ Finset.range C.gates.length := Finset.filter_subset _ _
  have hc := Finset.card_le_card hsub
  rw [Finset.card_range] at hc
  change 2 * (productiveGates (n := n) C).card + (rawMergeGates (n := n) C).card ≤ C.gates.length + 1
  omega

end PEqualNP.MetaComplexity.L1407

#print axioms PEqualNP.MetaComplexity.L1407.typed_aggregation_bound
