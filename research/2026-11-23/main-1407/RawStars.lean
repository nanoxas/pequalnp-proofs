import Common

namespace PEqualNP.MetaComplexity.L1407

open PEqualNP.CircuitLowerBounds

/-- A true live wire either has a true raw input, or has a live AND ancestor
whose every input has a true raw input. This statement uses no cleanliness
assumption and follows only valid, earlier references. -/
theorem trace_raw_or_and {n : ℕ} (C : Circuit) (hops : AndOr C)
    (x : Fin n → Bool) :
    ∀ w, Live (n := n) C w → value C x w = true →
      (∃ v ∈ support C w, x v = true) ∨
      ∃ j g, C.gates[j]? = some g ∧ g.op = GateOp.and ∧
        Live (n := n) C (n + j) ∧
        ∀ a ∈ g.inputs, a < n + j ∧ ∃ v ∈ support C a, x v = true := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hlive ht
    by_cases hin : w < n
    · left
      refine ⟨⟨w, hin⟩, ?_, ?_⟩
      · rw [support_input C w hin]
        exact Finset.mem_singleton_self _
      · simpa only [value, wires_input C x w hin] using ht
    · by_cases hout : n + C.gates.length ≤ w
      · simp only [value, wires_oob C x w hout, Bool.false_eq_true] at ht
      · have hjlt : w - n < C.gates.length := by omega
        let j := w - n
        let g := C.gates[j]'hjlt
        have hw : w = n + j := by omega
        have hg : C.gates[j]? = some g := List.getElem?_eq_getElem hjlt
        have hgj := (hops g (List.mem_of_getElem? hg)).1
        rw [hw] at hlive ht
        rcases hgj with hand | hor
        · have hall := and_inputs_true C x j g hg hand ht
          by_cases hraw : ∀ a ∈ g.inputs, ∃ v ∈ support C a, x v = true
          · right
            exact ⟨j, g, hg, hand, hlive, fun a ha => ⟨(hall a ha).1, hraw a ha⟩⟩
          · have hex : ∃ a, a ∈ g.inputs ∧ ¬ ∃ v ∈ support C a, x v = true := by
              by_contra hnot
              apply hraw
              intro a ha
              by_contra hn
              exact hnot ⟨a, ha, hn⟩
            obtain ⟨a, ha, hnot⟩ := hex
            have halt := (hall a ha).1
            have halive := live_input_of_gate C j g hg hlive a ha halt
            rcases ih a (by omega) halive (hall a ha).2 with h | h
            · exact False.elim (hnot h)
            · exact Or.inr h
        · obtain ⟨a, ha, halt, hat⟩ := or_input_true C x j g hg hor ht
          have halive := live_input_of_gate C j g hg hlive a ha halt
          rcases ih a (by omega) halive hat with h | h
          · left
            obtain ⟨v, hv, hxv⟩ := h
            refine ⟨v, ?_, hxv⟩
            rw [hw, mem_support]
            exact or_true_of_input C (oneInput v) j g hg hor a ha halt
              ((mem_support C a v).mp hv)
          · exact Or.inr h

/-- A clean AND cannot have an empty input list. -/
theorem and_inputs_ne_nil {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hclean : AndBelow G C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) : g.inputs ≠ [] := by
  intro hnil
  have ht : value C (fun _ : Fin n => false) (n + j) = true :=
    and_true_of_inputs C (fun _ => false) j g hg hop (by simp [hnil])
  exact not_edgeOn_false G (hclean j g hg hop _ ht)

/-- If every input of a clean AND has a raw witness, fan-in at most two
forces exactly two valid, nonempty input supports. -/
theorem raw_and_binary {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C) (x : Fin n → Bool)
    (j : ℕ) (g : Gate) (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and)
    (hraw : ∀ a ∈ g.inputs, a < n + j ∧ ∃ v ∈ support C a, x v = true) :
    ∃ a b, g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (∃ u ∈ support C a, x u = true) ∧ (∃ v ∈ support C b, x v = true) := by
  have hlen := (hops g (List.mem_of_getElem? hg)).2
  have hn := and_inputs_ne_nil G C hclean j g hg hop
  generalize heq : g.inputs = ins at hraw hlen hn ⊢
  cases ins with
  | nil => exact False.elim (hn rfl)
  | cons a tail =>
    cases tail with
    | nil =>
      obtain ⟨halt, v, hv, hxv⟩ := hraw a (by simp)
      have ht : value C (oneInput v) (n + j) = true := by
        apply and_true_of_inputs C (oneInput v) j g hg hop
        intro w hw
        rw [heq] at hw
        have hwa : w = a := by simpa using hw
        subst w
        exact ⟨halt, (mem_support C a v).mp hv⟩
      exact False.elim (not_edgeOn_one G v (hclean j g hg hop _ ht))
    | cons b rest =>
      cases rest with
      | nil =>
        exact ⟨a, b, rfl, (hraw a (by simp)).1, (hraw b (by simp)).1,
          (hraw a (by simp)).2, (hraw b (by simp)).2⟩
      | cons c cs => simp at hlen

def pairInput {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun w => decide (w = u ∨ w = v)

@[simp] theorem pairInput_true_iff {n : ℕ} (u v w : Fin n) :
    pairInput u v w = true ↔ w = u ∨ w = v := by simp [pairInput]

theorem edgeOn_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    EdgeOn G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput_true_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ hab)
    · exact hab
    · exact hab.symm
    · exact False.elim (G.loopless.irrefl _ hab)
  · intro huv
    exact ⟨u, v, huv, by simp, by simp⟩

/-- Every pair from the two raw supports of a clean binary AND is an edge. -/
theorem and_raw_cross_adj {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C)
    (j : ℕ) (g : Gate) (a b : ℕ)
    (hg : C.gates[j]? = some g) (hop : g.op = GateOp.and) (hins : g.inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j)
    (u v : Fin n) (hu : u ∈ support C a) (hv : v ∈ support C b) : G.Adj u v := by
  have hmono_u : ∀ w, oneInput u w = true → pairInput u v w = true := by
    intro w hw
    simp only [oneInput, decide_eq_true_eq] at hw
    subst w
    simp
  have hmono_v : ∀ w, oneInput v w = true → pairInput u v w = true := by
    intro w hw
    simp only [oneInput, decide_eq_true_eq] at hw
    subst w
    simp
  have hat := wires_mono C hops (oneInput u) (pairInput u v) hmono_u a
    ((mem_support C a u).mp hu)
  have hbt := wires_mono C hops (oneInput v) (pairInput u v) hmono_v b
    ((mem_support C b v).mp hv)
  have ht : value C (pairInput u v) (n + j) = true := by
    apply and_true_of_inputs C (pairInput u v) j g hg hop
    intro w hw
    rw [hins] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨ha, hat⟩
    · exact ⟨hb, hbt⟩
  exact (edgeOn_pair_iff G u v).mp (hclean j g hg hop _ ht)

/-- A productive gate comes with a nonempty complete bipartite raw profile. -/
theorem productive_biclique {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hops : AndOr C) (hclean : AndBelow G C) (j : ℕ) (hj : Productive (n := n) C j) :
    ∃ g a b, C.gates[j]? = some g ∧ g.op = GateOp.and ∧ g.inputs = [a, b] ∧
      a < n + j ∧ b < n + j ∧
      (support (n := n) C a).Nonempty ∧ (support (n := n) C b).Nonempty ∧
      ∀ u ∈ support C a, ∀ v ∈ support C b, G.Adj u v := by
  obtain ⟨hlive, g, a, b, hg, hop, hins, ha, hb, hsa, hsb⟩ := hj
  exact ⟨g, a, b, hg, hop, hins, ha, hb, hsa, hsb,
    fun u hu v hv => and_raw_cross_adj G C hops hclean j g a b hg hop hins ha hb u v hu hv⟩

/-- Every graph edge crosses the two raw supports of a productive live AND. -/
theorem edge_covered_by_productive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hops : AndOr C) (hclean : AndBelow G C)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeOn G x))
    (u v : Fin n) (huv : G.Adj u v) :
    ∃ j g a b, Productive (n := n) C j ∧ C.gates[j]? = some g ∧
      g.op = GateOp.and ∧ g.inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      ((u ∈ support C a ∧ v ∈ support C b) ∨
       (v ∈ support C a ∧ u ∈ support C b)) := by
  classical
  have hout : value C (pairInput u v) C.output = true := by
    change C.eval (List.ofFn (pairInput u v)) = true
    rw [hfun]
    exact decide_eq_true ((edgeOn_pair_iff G u v).mpr huv)
  have hsout := support_output G C hfun
  rcases trace_raw_or_and C hops (pairInput u v) C.output (live_output C) hout with h | h
  · obtain ⟨w, hw, hwt⟩ := h
    rw [hsout] at hw
    exact False.elim (Finset.notMem_empty w hw)
  · obtain ⟨j, g, hg, hop, hlive, hraw⟩ := h
    obtain ⟨a, b, hins, ha, hb, ⟨p, hp, hpt⟩, ⟨q, hq, hqt⟩⟩ :=
      raw_and_binary G C hops hclean (pairInput u v) j g hg hop hraw
    have hpq := and_raw_cross_adj G C hops hclean j g a b hg hop hins ha hb p q hp hq
    refine ⟨j, g, a, b, ⟨hlive, g, a, b, hg, hop, hins, ha, hb, ⟨p, hp⟩, ⟨q, hq⟩⟩,
      hg, hop, hins, ha, hb, ?_⟩
    simp only [pairInput_true_iff] at hpt hqt
    rcases hpt with rfl | rfl <;> rcases hqt with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ hpq)
    · exact Or.inl ⟨hp, hq⟩
    · exact Or.inr ⟨hp, hq⟩
    · exact False.elim (G.loopless.irrefl _ hpq)

end PEqualNP.MetaComplexity.L1407
