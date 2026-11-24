import FirstGateReduction

/-!
# Necessary reader shape of a global size-14 witness for L-meta-670

Research helper, not the final official artifact. The exact accepted L-meta-1007
lower bound remains an explicit premise. The checked reader-elimination helpers
are used without changing their hypotheses.
-/

namespace PEqualNP.Research.L670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.PermInputs

def Special (i : Fin 9) : Prop := i = 4 ∨ i = 6 ∨ i = 7

instance (i : Fin 9) : Decidable (Special i) :=
  inferInstanceAs (Decidable (i = 4 ∨ i = 6 ∨ i = 7))

theorem special_dep (i : Fin 9) (hi : Special i) : Dep target9 i := by
  rcases hi with rfl | rfl | rfl
  · refine ⟨(fun p => decide (p = 0)), ?_⟩; decide
  · refine ⟨(fun p => decide (p = 1)), ?_⟩; decide
  · refine ⟨(fun p => decide (p = 2)), ?_⟩; decide

theorem special_restriction_nonconstant (i : Fin 9) (hi : Special i) (b : Bool) :
    ∃ x y : Fin 9 → Bool,
      target9 (Function.update x i b) ≠ target9 (Function.update y i b) := by
  refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
  rcases hi with rfl | rfl | rfl <;> cases b <;> decide

/-- The exact deletion maps from the finite graph audit, implemented as input relabelings. -/
theorem special_restrict_to_eight (i : Fin 9) (hi : Special i) (s : ℕ)
    (h : HasCircuitSize 9 (fun x => target9 (Function.update x i false)) s) :
    HasCircuitSize 8 target8 s := by
  rcases hi with rfl | rfl | rfl
  · exact restrict_to_eight s h
  · let π : Fin 9 → Fin 8 := ![1, 0, 4, 7, 5, 2, 0, 6, 3]
    have hp := relabel_size π _ s h
    have he : (fun x : Fin 8 → Bool =>
        target9 (Function.update (x ∘ π) 6 false)) = target8 := by
      funext x
      simp [target9, target8, π, Function.comp_def, Bool.and_comm,
        Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
    rwa [he] at hp
  · let π : Fin 9 → Fin 8 := ![1, 2, 3, 7, 5, 0, 6, 0, 4]
    have hp := relabel_size π _ s h
    have he : (fun x : Fin 8 → Bool =>
        target9 (Function.update (x ∘ π) 7 false)) = target8 := by
      funext x
      simp [target9, target8, π, Function.comp_def, Bool.and_comm,
        Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
    rwa [he] at hp

theorem no_two_drop (h8 : ¬ HasCircuitSize 8 target8 12)
    (i : Fin 9) (hi : Special i) (s : ℕ) (hs : s ≤ 14) :
    ¬ Drop target9 i false 2 s := by
  rintro ⟨s', hsave, hc⟩
  obtain ⟨C, hok, hsize, hev⟩ := special_restrict_to_eight i hi s' hc
  exact h8 ⟨C, hok, by omega, hev⟩

/-- Every special input has exactly one actual reader in a least size-at-most-14 circuit. -/
theorem special_unique_reader (h8 : ¬ HasCircuitSize 8 target8 12)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : Special i) : ∃! p, Reads gs p i := by
  obtain ⟨p, hp⟩ := L.dep_read i (special_dep i hi) (special_restriction_nonconstant i hi)
  refine ⟨p, hp, ?_⟩
  intro q hq
  by_contra hqp
  exact no_two_drop h8 i hi gs.length hs
    (L.save2 i false (special_restriction_nonconstant i hi false)
      q p hqp (rc_input false hq) (rc_input false hp))

/-- Such a reader cannot be AND or NOT: its constant restriction has a later reader,
so the original reader and that successor would both disappear. -/
theorem special_reader_is_or (h8 : ¬ HasCircuitSize 8 target8 12)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : Special i) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (hip : (i : ℕ) ∈ g.inputs) : g.op = GateOp.or := by
  by_contra hor
  have hfix : g.op = GateOp.not ∨ false = fixBit g := by
    rcases L.hcl p g hg with ⟨hop, _⟩ | ⟨hop, _⟩
    · exact Or.inl hop
    · rcases hop with hand | hor'
      · exact Or.inr (by simp [fixBit, hand])
      · exact False.elim (hor hor')
  have hp : Reads gs p i := ⟨g, hg, hip⟩
  have hc := isC_reader L.hcl i p g hg hip false hfix
  obtain ⟨q, hpq, _, hqrc⟩ := L.next i false
    (special_restriction_nonconstant i hi false) p (reads_len hp) hc
  exact no_two_drop h8 i hi gs.length hs
    (L.save2 i false (special_restriction_nonconstant i hi false)
      p q (Nat.ne_of_lt hpq) (rc_input false hp) hqrc)

/-- If only gate p reads input i, equal values at p and all other inputs force equal
values at every wire except i. The proof uses actual valid earlier reads. -/
theorem sole_reader_agree {n : ℕ} (gs : List Gate) (hcl : CleanL n gs)
    (i : Fin n) (p : ℕ) (hsole : ∀ q, Reads gs q i → q = p)
    (x y : Fin n → Bool) (hinput : ∀ j, j ≠ i → x j = y j)
    (hgate : vl gs x (n + p) = vl gs y (n + p)) :
    ∀ w : ℕ, w ≠ (i : ℕ) → vl gs x w = vl gs y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwi
    by_cases hraw : w < n
    · rw [vl_input gs x w hraw, vl_input gs y w hraw]
      exact hinput ⟨w, hraw⟩ (fun e => hwi (congrArg Fin.val e))
    · obtain ⟨q, rfl⟩ : ∃ q, w = n + q := ⟨w - n, by omega⟩
      by_cases hqp : q = p
      · subst q; exact hgate
      · cases hq : gs[q]? with
        | none =>
          have hlen : gs.length ≤ q := List.getElem?_eq_none_iff.1 hq
          rw [vl_beyond gs x _ (by omega), vl_beyond gs y _ (by omega)]
        | some g =>
          rw [vl_gate gs hcl x q g hq, vl_gate gs hcl y q g hq]
          congr 1
          apply List.map_congr_left
          intro a ha
          apply ih a ((hcl q g hq).lt a ha)
          intro hai
          apply hqp
          exact hsole q ⟨g, hq, hai ▸ ha⟩

def obstructionNeighbor (i j : Fin 9) : Fin 9 :=
  if i = 4 then (if j = 1 ∨ j = 5 then 3 else 0)
  else if i = 6 then (if j = 0 ∨ j = 2 then 8 else 1)
  else (if j = 1 ∨ j = 3 then 5 else 2)

def obstructionInput (i j : Fin 9) : Fin 9 → Bool :=
  fun p => decide (p = j ∨ p = obstructionNeighbor i j)

/-- Twenty-four explicit graph obstructions to a sole OR(i,j) reader with j raw.
This finite fact is kernel evaluated; it does not enumerate circuits. -/
theorem raw_or_obstruction (i j : Fin 9) (hi : Special i) (hji : j ≠ i) :
    obstructionInput i j j = true ∧
      target9 (Function.update (obstructionInput i j) i false) ≠
        target9 (Function.update (obstructionInput i j) i true) := by
  have h : ∀ i j : Fin 9, Special i → j ≠ i →
      obstructionInput i j j = true ∧
        target9 (Function.update (obstructionInput i j) i false) ≠
          target9 (Function.update (obstructionInput i j) i true) := by decide
  exact h i j hi hji

theorem target9_singleton (i : Fin 9) : target9 (fun p => decide (p = i)) = false := by
  have h : ∀ i : Fin 9, target9 (fun p => decide (p = i)) = false := by decide
  exact h i

theorem target9_output_not_input (gs : List Gate) (o : ℕ)
    (hev : ∀ x : Fin 9 → Bool, vl gs x o = target9 x) (i : Fin 9) : o ≠ i := by
  intro ho
  have he := hev (fun p => decide (p = i))
  rw [ho, vl_input gs _ i i.isLt, target9_singleton i] at he
  simp at he

/-- All parts of the special-reader shape used by the narrowed SAT model. -/
def NarrowReader (gs : List Gate) (i : Fin 9) : Prop :=
  ∃ p g w, gs[p]? = some g ∧ g.op = GateOp.or ∧
    (g.inputs = [(i : ℕ), w] ∨ g.inputs = [w, (i : ℕ)]) ∧
    9 ≤ w ∧ w < 9 + p ∧ (∀ q, Reads gs q i ↔ q = p)

theorem special_narrow_reader (h8 : ¬ HasCircuitSize 8 target8 12)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : Special i) : NarrowReader gs i := by
  obtain ⟨p, hp, huniq⟩ := special_unique_reader h8 gs o L hs i hi
  obtain ⟨g, hg, hip⟩ := hp
  have hp : Reads gs p i := ⟨g, hg, hip⟩
  have hop := special_reader_is_or h8 gs o L hs i hi p g hg hip
  rcases gate_cases gs L.hcl p g hg i hip with ⟨hnot, _⟩ | ⟨w, hin, hsem⟩
  · rw [hop] at hnot; cases hnot
  · rcases hsem with ⟨hand, _⟩ | ⟨_, hsem⟩
    · rw [hop] at hand; cases hand
    · have hmem : w ∈ g.inputs := by
        rcases hin with hin | hin <;> simp [hin]
      have hwlt : w < 9 + p := (L.hcl p g hg).lt w hmem
      have hwne : w ≠ (i : ℕ) := by
        intro he
        apply L.no_alias target9_nonconstant p (reads_len hp) i (by omega)
        intro x
        rw [hsem x, he, Bool.or_self]
      have hwge : 9 ≤ w := by
        by_contra hn
        have hraw : w < 9 := by omega
        let j : Fin 9 := ⟨w, hraw⟩
        have hji : j ≠ i := fun he => hwne (congrArg Fin.val he)
        obtain ⟨hxj, hdiff⟩ := raw_or_obstruction i j hi hji
        let x := obstructionInput i j
        have hgate : vl gs (Function.update x i false) (9 + p) =
            vl gs (Function.update x i true) (9 + p) := by
          rw [hsem, hsem, vl_input gs _ w hraw, vl_input gs _ w hraw]
          have hv : ∀ b, Function.update x i b ⟨w, hraw⟩ = true := by
            intro b
            rw [Function.update_of_ne hji]
            exact hxj
          rw [hv false, hv true, Bool.or_true, Bool.or_true]
        have he := sole_reader_agree gs L.hcl i p huniq
          (Function.update x i false) (Function.update x i true)
          (fun q hqi => by simp [Function.update_of_ne hqi]) hgate o
          (target9_output_not_input gs o L.hev i)
        rw [L.hev, L.hev] at he
        exact hdiff he
      refine ⟨p, g, w, hg, hop, hin, hwge, hwlt, ?_⟩
      intro q
      exact ⟨huniq q, fun he => he ▸ hp⟩

theorem narrow_reader_not_first (gs : List Gate) (i : Fin 9)
    (h : NarrowReader gs i) : ¬ Reads gs 0 i := by
  obtain ⟨p, _, w, _, _, _, hw, hwp, huniq⟩ := h
  intro hread
  have hp : 0 = p := (huniq 0).1 hread
  omega

/-- Any global size-14 witness yields one globally least clean witness with all three
special reader conditions simultaneously. The final output is the last gate. -/
theorem exists_narrow_fourteen (h8 : ¬ HasCircuitSize 8 target8 12)
    (h14 : HasCircuitSize 9 target9 14) :
    ∃ gs o, Least 9 target9 gs o ∧ gs.length = 14 ∧ o = 22 ∧
      (∀ i, Special i → NarrowReader gs i) ∧
      (∀ i, Special i → ¬ Reads gs 0 i) := by
  obtain ⟨gs, o, L, hlen⟩ := exists_least 9 target9 14 target9_nonconstant h14
  have hlen' : gs.length = 14 := by
    by_contra hne
    have hsmall : gs.length ≤ 13 := by omega
    apply no_global_thirteen h8
    obtain ⟨C, hc, hsize, he⟩ := has_of_clean 9 gs o L.hcl
    exact ⟨C, hc, hsize.trans hsmall, fun x => (he x).trans (L.hev x)⟩
  have hout : o = 22 := by
    by_contra hno
    obtain ⟨q, hq, hread⟩ := L.live target9_nonconstant 13 (by omega) (by omega)
    have := reads_len hread
    omega
  have hnarrow : ∀ i, Special i → NarrowReader gs i :=
    fun i hi => special_narrow_reader h8 gs o L hlen i hi
  exact ⟨gs, o, L, hlen', hout, hnarrow,
    fun i hi => narrow_reader_not_first gs i (hnarrow i hi)⟩

#print axioms special_restrict_to_eight
#print axioms special_unique_reader
#print axioms special_reader_is_or
#print axioms sole_reader_agree
#print axioms raw_or_obstruction
#print axioms special_narrow_reader
#print axioms exists_narrow_fourteen

end PEqualNP.Research.L670
