import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ext
import PEqualNP.Defs

#check Nat.add_comm

theorem generic_bitvec_absorption (a b : BitVec 256) : a &&& (a ||| b) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem generic_finset_card (s : Finset Nat) (n : Nat) : (insert n s).card ≤ s.card + 1 := by
  by_cases h : n ∈ s
  · simp [h]
  · simp [h]

theorem generic_arithmetic (a b c : Nat) (h₁ : a + b ≤ c + 1) (h₂ : b ≥ 2) : a < c := by
  omega

theorem generic_membership (a b c : Nat) (h : a = b ∨ a = c) : a ∈ ([b,c] : List Nat) := by
  aesop

#print axioms generic_bitvec_absorption
#print axioms generic_finset_card
#print axioms generic_arithmetic
#print axioms generic_membership
