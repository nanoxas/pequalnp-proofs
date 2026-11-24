import PEqualNP.MetaComplexity.Helpers.ReadersPat

/-!
# Conditional structural reduction for the prescribed first gate in L-meta-670

This is a research helper, not the official single-file submission. The eight-input
lower bound is an explicit premise with exactly the statement of accepted L-meta-1007.

The cleaner prefix argument and the concrete cleaning proof adapt the public Apache-2.0
helpers `ExchangeElim.elim_prefix` and `Parity3.clean_of`. The sole-reader proof adapts
`Parity3.single_reader`, replacing its parity-specific all-input dependence premise by
the explicit graph-function witnesses used here. All circuit semantics are the public
definitions, including the false value of unavailable wires.
-/

namespace PEqualNP.Research.L670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def target9 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def target8 (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 0 && x 4) ||
  (x 1 && x 5) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 6) ||
  (x 5 && x 7) || (x 7 && x 4)

def firstGate : Gate := ⟨GateOp.and, [4, 6]⟩

theorem target9_nonconstant : ∃ x y, target9 x ≠ target9 y := by
  refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
  decide

theorem target9_zero4_nonconstant : ∃ x y : Fin 9 → Bool,
    target9 (Function.update x 4 false) ≠ target9 (Function.update y 4 false) := by
  refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
  decide

/-- The cleaner only appends gates to its existing emitted prefix. -/
theorem emitted_prefix (n : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, ∃ t, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList ++ t, ?_⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ht]
    simp [elimStep]

/-- Cleaning emits AND(4,6) unchanged and retains it as gate zero. -/
theorem clean_first_gate (gs : List Gate) (h0 : gs[0]? = some firstGate) :
    (elim 9 gs (idStats 9, [])).2[0]? = some firstGate := by
  cases gs with
  | nil => simp at h0
  | cons g gs =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst g
    obtain ⟨t, ht⟩ := emitted_prefix 9 gs (elimStep 9 (idStats 9, []) firstGate)
    change (elim 9 gs (elimStep 9 (idStats 9, []) firstGate)).2[0]? = _
    rw [ht]
    have he : (elimStep 9 (idStats 9, []) firstGate).2 = [firstGate] := by rfl
    rw [he]
    rfl

/-- A concrete first-gate-preserving version of `Parity3.clean_of`. -/
theorem clean_preserving_first (C : Circuit) (hok : FanInTwo C)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target9 x)
    (h0 : C.gates[0]? = some firstGate) :
    ∃ gs o, CleanL 9 gs ∧ gs.length ≤ C.size ∧
      (∀ x : Fin 9 → Bool, vl gs x o = target9 x) ∧ gs[0]? = some firstGate := by
  have hok' : ∀ g ∈ C.gates, Ok g := hok
  set acc := elim 9 C.gates (idStats 9, []) with hacc
  have hinv : ∀ y : Fin 9 → Bool,
      Inv 9 (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim 9 _ (by simp) C.gates _ _ hok' (inv_id 9 y)
  have hval : ∀ y : Fin 9 → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) =
        target9 y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := target9_nonconstant
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_, ?_⟩
    · exact clean_elim 9 (List.ofFn fun _ : Fin 9 => false) (by simp) C.gates _ _ hok'
        (inv_id 9 _) (by intro p g hp; simp at hp)
    · have hlen := elim_len 9 C.gates (idStats 9, [])
      rw [← hacc] at hlen
      simpa [Circuit.size] using hlen
    · intro y
      have hv := hval y
      rw [hst] at hv
      exact hv
    · exact clean_first_gate C.gates h0

/-- If AND(i,k) is the only reader of i, fixing k=false erases dependence on i.
No validity or cleanliness premise is needed for the remaining gates. -/
theorem sole_first_and_agree {n : ℕ} (gs : List Gate) (o : ℕ) (i k : Fin n)
    (hik : k ≠ i) (h0 : gs[0]? = some ⟨GateOp.and, [(i : ℕ), (k : ℕ)]⟩)
    (hoi : o ≠ i)
    (hno : ∀ q g, gs[q]? = some g → q ≠ 0 → (i : ℕ) ∉ g.inputs)
    (x : Fin n → Bool) (hk : x k = false) :
    vl gs (Function.update x i true) o = vl gs (Function.update x i false) o := by
  cases gs with
  | nil => simp at h0
  | cons g post =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    subst g
    have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
      intro g hg
      obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
      exact hno (q + 1) g (by simpa using hq) (by omega)
    have hgate : ∀ b : Bool,
        GateOp.and.eval ([((i : ℕ)), ((k : ℕ))].map
          (fun a => (List.ofFn (Function.update x i b)).getD a false)) = false := by
      intro b
      simp [GateOp.eval, Function.update_of_ne hik, hk]
    change (wiresFrom post (List.ofFn (Function.update x i true) ++
      [GateOp.and.eval ([((i : ℕ)), ((k : ℕ))].map
        (fun a => (List.ofFn (Function.update x i true)).getD a false))])).getD o false =
      (wiresFrom post (List.ofFn (Function.update x i false) ++
      [GateOp.and.eval ([((i : ℕ)), ((k : ℕ))].map
        (fun a => (List.ofFn (Function.update x i false)).getD a false))])).getD o false
    rw [hgate true, hgate false]
    apply agree_except i post _ _ hno' (by simp) ?_ o hoi
    intro j hj
    by_cases hjn : j = n
    · subst j
      rw [getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp)]
    · rw [getD_snoc_ne _ _ _ _ (by simpa using hjn),
        getD_snoc_ne _ _ _ _ (by simpa using hjn)]
      by_cases hlt : j < n
      · rw [getD_ofFn n _ false ⟨j, hlt⟩, getD_ofFn n _ false ⟨j, hlt⟩]
        rw [Function.update_of_ne (fun e => hj (congrArg Fin.val e)),
          Function.update_of_ne (fun e => hj (congrArg Fin.val e))]
      · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

/-- The explicit {0}/{0,4} pair forces another reader of input 4. -/
theorem second_reader (gs : List Gate) (o : ℕ)
    (hev : ∀ x : Fin 9 → Bool, vl gs x o = target9 x)
    (h0 : gs[0]? = some firstGate) : ∃ q, q ≠ 0 ∧ Reads gs q 4 := by
  have hoi : o ≠ 4 := by
    intro ho
    have he := hev (fun p => decide (p = 4))
    rw [ho, vl_input gs _ 4 (by decide)] at he
    simp [target9] at he
  by_contra hsecond
  have hno : ∀ q g, gs[q]? = some g → q ≠ 0 → 4 ∉ g.inputs := by
    intro q g hq hq0 hread
    exact hsecond ⟨q, hq0, g, hq, hread⟩
  have he := sole_first_and_agree gs o (4 : Fin 9) (6 : Fin 9) (by decide)
    h0 hoi hno (fun p => decide (p = 0)) (by decide)
  rw [hev, hev] at he
  simp [target9] at he

/-- Relabel the unused fixed input 4 to raw input 0, reducing arity at no gate cost. -/
theorem restrict_to_eight (s : ℕ)
    (h : HasCircuitSize 9 (fun x => target9 (Function.update x 4 false)) s) :
    HasCircuitSize 8 target8 s := by
  let π : Fin 9 → Fin 8 := ![0, 1, 2, 3, 0, 4, 5, 6, 7]
  have hp := PEqualNP.MetaComplexity.Helpers.PermInputs.relabel_size π _ s h
  have he : (fun x : Fin 8 → Bool =>
      target9 (Function.update (x ∘ π) 4 false)) = target8 := by
    funext x
    simp [target9, target8, π, Function.comp_def]
  rwa [he] at hp

/-- The same accepted eight-input bound already rules out a global size-13 circuit. -/
theorem no_global_thirteen (h8 : ¬ HasCircuitSize 8 target8 12) :
    ¬ HasCircuitSize 9 target9 13 := by
  intro h13
  obtain ⟨gs, o, L, hlen⟩ := exists_least 9 target9 13 target9_nonconstant h13
  have hd : Dep target9 (4 : Fin 9) := by
    refine ⟨(fun p => decide (p = 0)), ?_⟩
    decide
  have hnc : ∀ b : Bool, ∃ x y : Fin 9 → Bool,
      target9 (Function.update x 4 b) ≠ target9 (Function.update y 4 b) := by
    intro b
    refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
    cases b <;> decide
  obtain ⟨q, hq⟩ := L.dep_read (4 : Fin 9) hd hnc
  have hdrop := L.save (4 : Fin 9) false target9_zero4_nonconstant {q} (by
    intro p hp
    have he : p = q := by simpa using hp
    subst p
    exact rc_input false hq)
  obtain ⟨s, hsave, hrestricted⟩ := hdrop
  have hsmall := restrict_to_eight s hrestricted
  obtain ⟨D, hd, hds, hde⟩ := hsmall
  have hcard : ({q} : Finset ℕ).card = 1 := Finset.card_singleton q
  rw [hcard] at hsave
  exact h8 ⟨D, hd, by omega, hde⟩

/-- A no-14 hypothesis makes any cleaned size-at-most-15 witness globally least. -/
theorem least_of_no_fourteen (h14 : ¬ HasCircuitSize 9 target9 14)
    (gs : List Gate) (o : ℕ) (hcl : CleanL 9 gs) (hs : gs.length ≤ 15)
    (hev : ∀ x : Fin 9 → Bool, vl gs x o = target9 x) : Least 9 target9 gs o := by
  refine ⟨hcl, hev, ?_⟩
  intro gs' o' hcl' hev'
  by_contra hlt
  have hs' : gs'.length ≤ 14 := by omega
  apply h14
  obtain ⟨C, hc, hsize, he⟩ := has_of_clean 9 gs' o' hcl'
  exact ⟨C, hc, hsize.trans hs', fun x => (he x).trans (hev' x)⟩

/-- The smallest conditional bridge: the accepted eight-input lower bound and global
no-14 imply no size-at-most-15 circuit beginning with AND(4,6). -/
theorem no_first_and46_of_no_fourteen
    (h8 : ¬ HasCircuitSize 8 target8 12)
    (h14 : ¬ HasCircuitSize 9 target9 14)
    (C : Circuit) (hok : FanInTwo C) (hs : C.size ≤ 15)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target9 x)
    (h0 : C.gates[0]? = some firstGate) : False := by
  obtain ⟨gs, o, hcl, hsize, he, hfirst⟩ := clean_preserving_first C hok hev h0
  have h15 : gs.length ≤ 15 := hsize.trans hs
  have L := least_of_no_fourteen h14 gs o hcl h15 he
  obtain ⟨q, hq0, hq⟩ := second_reader gs o he hfirst
  have hp : Reads gs 0 4 := ⟨firstGate, hfirst, by simp [firstGate]⟩
  have hc : IsC 8 gs (4 : Fin 9) false (9 + 0) :=
    isC_reader hcl (4 : Fin 9) 0 firstGate hfirst (by simp [firstGate]) false
      (Or.inr (by simp [fixBit, firstGate]))
  obtain ⟨s, hsave, hrestricted⟩ := L.third (4 : Fin 9) false
    target9_zero4_nonconstant 0 q (Ne.symm hq0) hp hq hc
  have hsmall := restrict_to_eight s hrestricted
  obtain ⟨D, hd, hds, hde⟩ := hsmall
  exact h8 ⟨D, hd, by omega, hde⟩

/-- A prescribed-first size-15 witness would imply a global size-14 witness. -/
theorem first_and46_implies_fourteen (h8 : ¬ HasCircuitSize 8 target8 12)
    (C : Circuit) (hok : FanInTwo C) (hs : C.size ≤ 15)
    (hev : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = target9 x)
    (h0 : C.gates[0]? = some firstGate) : HasCircuitSize 9 target9 14 := by
  by_contra h14
  exact no_first_and46_of_no_fourteen h8 h14 C hok hs hev h0

#print axioms clean_first_gate
#print axioms sole_first_and_agree
#print axioms second_reader
#print axioms restrict_to_eight
#print axioms no_global_thirteen
#print axioms no_first_and46_of_no_fourteen
#print axioms first_and46_implies_fourteen

end PEqualNP.Research.L670
