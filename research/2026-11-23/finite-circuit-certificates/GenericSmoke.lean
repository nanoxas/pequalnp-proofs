import GenericCore

/- Target-neutral interface check: two-input XOR with at most two NOT gates.
   This uses a different arity and NOT budget from the five-input generator. -/
namespace PEqualNP.FiniteCircuitCertificates.GenericSmoke

open PEqualNP.CircuitLowerBounds
open PEqualNP.FiniteCircuitCertificates.Generic

-- Keep the finite count computation independent of classical decisions.
local instance gateOpDecidableEq : DecidableEq GateOp := by
  intro a b
  cases a <;> cases b
  case mod.mod m n => exact decidable_of_iff (m = n) (by simp)
  all_goals first | exact isTrue rfl | exact isFalse (by intro h; cases h)

def xorRaw : List Sig := [
  (0x3333333333333333333333333333333333333333333333333333333333333333,
   0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa),
  (0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
   0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)]

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
theorem xor_lower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (notBudget : C.gates.countP (fun g => decide (g.op = GateOp.not)) ≤ 2)
    (correct : ∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = evalT 6 x) :
    3 < C.gates.length := by
  exact cost_countP (n := 2) 6 xorRaw 3 2 rfl
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by intro t; fin_cases t <;> decide +kernel) C legal notBudget correct

theorem xor_upper :
    ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.gates.length = 4 ∧
      C.gates.countP (fun g => decide (g.op = GateOp.not)) = 1 ∧
      ∀ x : Fin 2 → Bool, C.eval (List.ofFn x) = evalT 6 x := by
  refine ⟨⟨[⟨.or,[0,1]⟩,⟨.and,[0,1]⟩,⟨.not,[3]⟩,⟨.and,[2,4]⟩],5⟩,
    ?_,rfl,rfl,?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel

end PEqualNP.FiniteCircuitCertificates.GenericSmoke

#print axioms PEqualNP.FiniteCircuitCertificates.Generic.cost
#print axioms PEqualNP.FiniteCircuitCertificates.Generic.cost_countP
#print axioms PEqualNP.FiniteCircuitCertificates.Generic.cost_oneNot
#print axioms PEqualNP.FiniteCircuitCertificates.GenericSmoke.xor_lower
#print axioms PEqualNP.FiniteCircuitCertificates.GenericSmoke.xor_upper
