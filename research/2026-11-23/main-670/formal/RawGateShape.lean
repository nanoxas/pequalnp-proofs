import DegreeThreeShape

/-!
# Raw-operand gate restrictions for the strengthened L-meta-670 search

Research helper, not the official single-file artifact. The previous three
checked modules are unchanged. The pivotal graph facts are finite kernel
evaluations; the transfer from those facts to readers uses actual circuit semantics.
-/

namespace PEqualNP.Research.L670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers

def neighborA : Fin 9 → Fin 9 := ![1, 0, 1, 2, 0, 0, 1, 2, 3]
def neighborB : Fin 9 → Fin 9 := ![4, 2, 3, 4, 3, 7, 8, 5, 5]

def pairInput (i j : Fin 9) : Fin 9 → Bool := fun p => decide (p = i ∨ p = j)

def pivotNeighbor (i j : Fin 9) (b : Bool) : Fin 9 :=
  bif b then
    (bif target9 (pairInput i j) then j
      else bif target9 (pairInput j (neighborA i)) then neighborB i else neighborA i)
  else if neighborA i = j then neighborB i else neighborA i

def pivotInput (i j : Fin 9) (b : Bool) : Fin 9 → Bool :=
  fun p => decide (p = pivotNeighbor i j b) || (b && decide (p = j))

/-- The 144 explicit pivotal rows: fixing any other raw input to either value leaves i
essential. These are finite graph facts, not circuit enumeration. -/
theorem pivot_input_facts (i j : Fin 9) (b : Bool) (hij : i ≠ j) :
    pivotInput i j b j = b ∧
      target9 (Function.update (pivotInput i j b) i false) = false ∧
      target9 (Function.update (pivotInput i j b) i true) = true := by
  have h : ∀ i j : Fin 9, ∀ b : Bool, i ≠ j →
      pivotInput i j b j = b ∧
        target9 (Function.update (pivotInput i j b) i false) = false ∧
        target9 (Function.update (pivotInput i j b) i true) = true := by decide
  exact h i j b hij

/-- A raw AND/OR gate with two distinct raw operands cannot be the sole reader of either
operand. This lemma has no lower-bound or leastness premise. -/
theorem raw_binary_second_reader (gs : List Gate) (o : ℕ) (hcl : CleanL 9 gs)
    (hev : ∀ x : Fin 9 → Bool, vl gs x o = target9 x)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (i j : Fin 9) (hij : i ≠ j)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : g.inputs = [(i : ℕ), (j : ℕ)] ∨ g.inputs = [(j : ℕ), (i : ℕ)]) :
    ∃ q, q ≠ p ∧ Reads gs q i := by
  by_contra hcomp
  have hsole : ∀ q, Reads gs q i → q = p := by
    intro q hq
    by_contra hqp
    exact hcomp ⟨q, hqp, hq⟩
  let x := pivotInput i j (fixBit g)
  obtain ⟨hxj, hlo, hhi⟩ := pivot_input_facts i j (fixBit g) hij
  have hjval : ∀ b : Bool, vl gs (Function.update x i b) j = fixBit g := by
    intro b
    rw [vl_input gs _ j j.isLt, Function.update_of_ne (Ne.symm hij)]
    exact hxj
  have hgval : ∀ b : Bool, vl gs (Function.update x i b) (9 + p) = fixBit g := by
    intro b
    rw [vl_gate gs hcl _ p g hg]
    rcases hop with hop | hop <;> rcases hin with hin | hin <;>
      simp [hop, hin, GateOp.eval, hjval b, fixBit]
  have he := sole_reader_agree gs hcl i p hsole
    (Function.update x i false) (Function.update x i true)
    (fun q hqi => by simp [Function.update_of_ne hqi])
    ((hgval false).trans (hgval true).symm) o (target9_output_not_input gs o hev i)
  rw [hev, hev, hlo, hhi] at he
  cases he

theorem raw_or_both_second_readers (gs : List Gate) (o : ℕ) (hcl : CleanL 9 gs)
    (hev : ∀ x : Fin 9 → Bool, vl gs x o = target9 x)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (i j : Fin 9) (hij : i ≠ j)
    (hop : g.op = GateOp.or)
    (hin : g.inputs = [(i : ℕ), (j : ℕ)] ∨ g.inputs = [(j : ℕ), (i : ℕ)]) :
    (∃ q, q ≠ p ∧ Reads gs q i) ∧ (∃ r, r ≠ p ∧ Reads gs r j) := by
  refine ⟨raw_binary_second_reader gs o hcl hev p g hg i j hij (Or.inr hop) hin, ?_⟩
  exact raw_binary_second_reader gs o hcl hev p g hg j i hij.symm (Or.inr hop)
    (hin.elim Or.inr Or.inl)

/-- Repeated raw operands give an alias and cannot occur in a least circuit. -/
theorem no_repeated_raw_gate (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (i : Fin 9)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : g.inputs = [(i : ℕ), (i : ℕ)]) : False := by
  apply L.no_alias target9_nonconstant p (List.getElem?_eq_some_iff.1 hg).1 i (by omega)
  intro x
  rw [vl_gate gs L.hcl x p g hg, hin]
  rcases hop with hand | hor
  · simp [hand, GateOp.eval]
  · simp [hor, GateOp.eval]

theorem input_degree_classes (i : Fin 9) : Special i ∨ DegreeThree i := by
  have h : ∀ i : Fin 9,
      (i = 4 ∨ i = 6 ∨ i = 7) ∨ (i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 8) := by
    decide
  exact h i

/-- No gate of a least size-at-most-14 circuit can be an AND of two raw operands. -/
theorem no_raw_and
    (h8 : ¬ HasCircuitSize 8 target8 12)
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (p : ℕ) (g : Gate) (hg : gs[p]? = some g) (i j : Fin 9)
    (hop : g.op = GateOp.and)
    (hin : g.inputs = [(i : ℕ), (j : ℕ)] ∨ g.inputs = [(j : ℕ), (i : ℕ)]) : False := by
  by_cases hij : i = j
  · subst j
    exact no_repeated_raw_gate gs o L p g hg i (Or.inl hop) (hin.elim id id)
  · have hip : (i : ℕ) ∈ g.inputs := by
      rcases hin with hin | hin <;> simp [hin]
    rcases input_degree_classes i with hspecial | hcore
    · have hor := special_reader_is_or h8 gs o L hs i hspecial p g hg hip
      rw [hop] at hor
      cases hor
    · obtain ⟨q, hqp, hq⟩ := raw_binary_second_reader gs o L.hcl L.hev p g hg i j hij
        (Or.inl hop) hin
      have hor := degree_three_companion_forces_or h517 gs o L hs i hcore p q
        (Ne.symm hqp) g hg hip hq
      rw [hop] at hor
      cases hor

theorem first_gate_not_and
    (h8 : ¬ HasCircuitSize 8 target8 12)
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (g : Gate) (hg : gs[0]? = some g) : g.op ≠ GateOp.and := by
  intro hop
  rcases L.hcl 0 g hg with ⟨hnot, _⟩ | ⟨_, a, b, ha, hb, hin⟩
  · rw [hop] at hnot; cases hnot
  · exact no_raw_and h8 h517 gs o L hs 0 g hg ⟨a, by omega⟩ ⟨b, by omega⟩ hop (Or.inl hin)

#print axioms pivot_input_facts
#print axioms raw_binary_second_reader
#print axioms raw_or_both_second_readers
#print axioms no_repeated_raw_gate
#print axioms no_raw_and
#print axioms first_gate_not_and

end PEqualNP.Research.L670
