import PEqualNP.Defs.AndCountCircuit

/-!
Generic monotonicity, matching the third child of the L-meta-909 reduction.
The fuel induction follows the monotonicity lemmas in the checked public
L_meta_635 proof (PEqualNP.Outside.L_meta_635_aux), retaining its public
project attribution. This proof does not assume WellFormed because the
evaluator itself ignores non-earlier gate references.
-/

namespace PEqualNP.Research.AndCountMonotonicity

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

theorem eval_monotone :
    ∀ (n : ℕ) (C : AndCountCircuit n) (U V : Finset (Fin n)),
      U ⊆ V → C.eval U = true → C.eval V = true := by
  intro n C U V hUV hU
  have hfuel : ∀ (d : ℕ) (i : Fin C.size),
      C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
    intro d
    induction d with
    | zero =>
        intro i hi
        simp [gateValFuel] at hi
    | succ d ih =>
        intro i hi
        simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
        have hside (B : Finset (Fin n)) (F : Finset (Fin C.size))
            (hs : sideTrue U B F i (C.gateValFuel U d) = true) :
            sideTrue V B F i (C.gateValFuel V d) = true := by
          simp only [sideTrue, decide_eq_true_eq] at hs ⊢
          rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
          · exact Or.inl ⟨v, hvB, hUV hvU⟩
          · exact Or.inr ⟨j, hjF, hji, ih j hvj⟩
        exact ⟨hside _ _ hi.1, hside _ _ hi.2⟩
  simp only [eval, decide_eq_true_eq] at hU ⊢
  rcases hU with ⟨v, hvOut, hvU⟩ | ⟨i, hiOut, hi⟩
  · exact Or.inl ⟨v, hvOut, hUV hvU⟩
  · exact Or.inr ⟨i, hiOut, hfuel C.size i hi⟩

#print axioms eval_monotone

end PEqualNP.Research.AndCountMonotonicity
