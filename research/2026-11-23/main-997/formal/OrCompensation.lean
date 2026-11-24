import BoundaryActivation
import OrPrivateCount

/-
OR-only compensation for a private singleton-support class. The proof uses
the checked negative-input OR frontier with target-restricted singleton
samples. It classifies every charged gate into the selected private class
or the global outside class. Apache-2.0.
-/

namespace PEqualNP.Research.OrCompensation

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.OrPrivateCount

noncomputable def opPart (n : ℕ) (C : Circuit) (op : GateOp) (T : Finset ℕ) : Finset ℕ := by
  classical
  exact T.filter fun w => (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = op

def restrictedSingleton {n : ℕ} (T : Finset (Fin n)) (p q : Fin n) : Bool :=
  decide (p ∈ T ∧ q = p)

lemma restrictedSingleton_raw {n : ℕ} (T : Finset (Fin n)) (p : Fin n) :
    (Finset.univ.filter (fun q => restrictedSingleton T q p = true)).card ≤ 1 := by
  classical
  have hs : Finset.univ.filter (fun q => restrictedSingleton T q p = true) ⊆ {p} := by
    intro q hq
    have h : q ∈ T ∧ p = q := of_decide_eq_true (Finset.mem_filter.mp hq).2
    exact Finset.mem_singleton.mpr h.2.symm
  simpa only [Finset.card_singleton] using Finset.card_le_card hs

lemma restricted_support {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (w : ℕ)
    (hzero : value C (fun _ : Fin n => false) w = false) :
    sampleSupport C (restrictedSingleton T) w = support (n := n) C w ∩ T := by
  classical
  ext p
  by_cases hp : p ∈ T
  · have he : restrictedSingleton T p = (fun q => decide (q = p)) := by
      funext q
      simp [restrictedSingleton, hp]
    simp only [mem_sampleSupport, he, Finset.mem_inter, mem_support, hp, and_true]
  · have he : restrictedSingleton T p = (fun _ => false) := by
      funext q
      simp [restrictedSingleton, hp]
    simp only [mem_sampleSupport, he, hzero, Bool.false_eq_true, Finset.mem_inter, hp,
      and_false]

lemma restricted_or_subset {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ) (i : Fin m)
    (hz : value C (fun _ : Fin n => false) z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) :
    orBranches C (fun _ : Fin n => false) (restrictedSingleton (S i)) ⊆
      opPart n C GateOp.or (lightAssigned C (S i) z) ∪
        opPart n C GateOp.or (outsideWide C S z) := by
  classical
  intro w hw
  obtain ⟨hrange, hop, hzero, hwide⟩ := Finset.mem_filter.mp hw
  rw [restricted_support C (S i) w hzero] at hwide
  have hglobal : 2 ≤ (support (n := n) C w).card :=
    hwide.trans (Finset.card_le_card Finset.inter_subset_left)
  have hwz : w ≠ z := by
    intro he
    subst w
    rw [hz] at hzero
    contradiction
  by_cases hown : support (n := n) C w ⊆ S i
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hrange, hwz, hown, hglobal⟩, hop⟩
  · have houtside : ∀ j : Fin m, ¬ support (n := n) C w ⊆ S j := by
      intro j hj
      have hji : j ≠ i := by
        intro he
        subst j
        exact hown hj
      have hsub : support (n := n) C w ∩ S i ⊆ S j ∩ S i := by
        intro p hp
        exact Finset.mem_inter.mpr ⟨hj (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩
      have hc := Finset.card_le_card hsub
      have hs := hinter j i hji
      omega
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hrange, hwz, hglobal, houtside⟩, hop⟩

/-- Singleton positives require OR gates in the selected private class or
the outside class. AND gates contribute no units to this compensation. -/
theorem compensated_or_count {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : value C (fun _ : Fin n => false) z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hzero : value C (fun _ : Fin n => false) o = false) :
    (S i).card - 1 ≤
      (opPart n C GateOp.or (lightAssigned C (S i) z)).card +
        (opPart n C GateOp.or (outsideWide C S z)).card := by
  classical
  have hpositive : ∀ p ∈ S i, value C (restrictedSingleton (S i) p) o = true := by
    intro p hp
    have he : restrictedSingleton (S i) p = (fun q => decide (q = p)) := by
      funext q
      simp [restrictedSingleton, hp]
    rw [he]
    exact hpos p hp
  have hcount := sample_or_count C hG (fun _ : Fin n => false) (restrictedSingleton (S i))
    (fun p _ => restrictedSingleton_raw (S i) p) o hzero (S i) hpositive
  have hsub := Finset.card_le_card (restricted_or_subset C S z i hz hinter)
  have hunion := Finset.card_union_le
    (opPart n C GateOp.or (lightAssigned C (S i) z))
    (opPart n C GateOp.or (outsideWide C S z))
  omega

lemma opPart_partition {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset ℕ) (hT : T ⊆ Finset.Ico n (n + C.size)) :
    (opPart n C GateOp.or T).card + (opPart n C GateOp.and T).card = T.card := by
  classical
  have hsplit : opPart n C GateOp.or T ∪ opPart n C GateOp.and T = T := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with hw | hw
      · exact (Finset.mem_filter.mp hw).1
      · exact (Finset.mem_filter.mp hw).1
    · intro hw
      obtain ⟨hn, hlt⟩ := Finset.mem_Ico.mp (hT hw)
      have hj : w - n < C.gates.length := by unfold Circuit.size at hlt; omega
      have hop : (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and ∨
          (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.or := by
        rw [List.getD_eq_getElem _ _ hj]
        exact (hG _ (List.getElem_mem hj)).1
      rcases hop with ha | ho
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, ha⟩)
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, ho⟩)
  have hdis : Disjoint (opPart n C GateOp.or T) (opPart n C GateOp.and T) := by
    apply Finset.disjoint_left.mpr
    intro w ho ha
    have ho' := (Finset.mem_filter.mp ho).2
    have ha' := (Finset.mem_filter.mp ha).2
    rw [ho'] at ha'
    cases ha'
  rw [← Finset.card_union_of_disjoint hdis, hsplit]

/-- Every private AND decreases the deficit that outside OR gates must pay. -/
theorem compensated_deficit {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : value C (fun _ : Fin n => false) z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hzero : value C (fun _ : Fin n => false) o = false) :
    (S i).card - 1 - (lightAssigned C (S i) z).card ≤
      (opPart n C GateOp.or (outsideWide C S z)).card -
        (opPart n C GateOp.and (lightAssigned C (S i) z)).card := by
  have hcount := compensated_or_count C S z hG hz hinter i o hpos hzero
  have hpart := opPart_partition C hG (lightAssigned C (S i) z)
    (fun _ hw => (Finset.mem_filter.mp hw).1)
  omega

end PEqualNP.Research.OrCompensation

#print axioms PEqualNP.Research.OrCompensation.compensated_or_count
#print axioms PEqualNP.Research.OrCompensation.compensated_deficit
