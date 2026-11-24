import ReaderShape

/-!
# Degree-three reader constraints for the global L-meta-670 size-14 search

Research helper, not the official single-file artifact. The exact accepted
L-meta-517 theorem is an explicit premise. All graph relabelings and the
essential-leaf step are proved here against the public circuit semantics.
The checked FirstGateReduction and ReaderShape modules remain unchanged.
-/

namespace PEqualNP.Research.L670

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers PEqualNP.MetaComplexity.Helpers.Readers
open PEqualNP.MetaComplexity.Helpers.PermInputs

/-- Exactly the function in the accepted L-meta-517 theorem, in its original term order. -/
def theta7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1)

/-- The theta graph with one new leaf 7 adjacent to vertex 2. -/
def thetaLeaf8 (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 1) || (x 0 && x 3) || (x 3 && x 4) ||
  (x 4 && x 1) || (x 0 && x 5) || (x 5 && x 6) || (x 6 && x 1) || (x 2 && x 7)

theorem thetaLeaf_nonconstant : ∃ x y, thetaLeaf8 x ≠ thetaLeaf8 y := by
  refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 2)), ?_⟩
  decide

theorem thetaLeaf_dep : Dep thetaLeaf8 (7 : Fin 8) := by
  refine ⟨(fun p => decide (p = 2)), ?_⟩
  decide

theorem thetaLeaf_restriction_nonconstant (b : Bool) : ∃ x y : Fin 8 → Bool,
    thetaLeaf8 (Function.update x 7 b) ≠ thetaLeaf8 (Function.update y 7 b) := by
  refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 2)), ?_⟩
  cases b <;> decide

theorem remove_theta_leaf (s : ℕ)
    (h : HasCircuitSize 8 (fun x => thetaLeaf8 (Function.update x 7 false)) s) :
    HasCircuitSize 7 theta7 s := by
  let π : Fin 8 → Fin 7 := ![0, 1, 2, 3, 4, 5, 6, 0]
  have hp := relabel_size π _ s h
  have he : (fun x : Fin 7 → Bool =>
      thetaLeaf8 (Function.update (x ∘ π) 7 false)) = theta7 := by
    funext x
    simp [thetaLeaf8, theta7, π, Function.comp_def]
  rwa [he] at hp

/-- Adding the essential leaf increases the accepted theta lower bound by one gate. -/
theorem theta_leaf_lower_bound
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (s : ℕ) (h : HasCircuitSize 8 thetaLeaf8 s) : 12 ≤ s := by
  obtain ⟨gs, o, L, hlen⟩ := exists_least 8 thetaLeaf8 s thetaLeaf_nonconstant h
  obtain ⟨p, hp⟩ := L.dep_read (7 : Fin 8) thetaLeaf_dep thetaLeaf_restriction_nonconstant
  have hdrop := L.save (7 : Fin 8) false (thetaLeaf_restriction_nonconstant false) {p} (by
    intro q hq
    have he : q = p := by simpa using hq
    subst q
    exact rc_input false hp)
  obtain ⟨t, hsave, ht⟩ := hdrop
  rw [Finset.card_singleton] at hsave
  have htheta := h517 t (remove_theta_leaf t ht)
  omega

def DegreeThree (i : Fin 9) : Prop :=
  i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 5 ∨ i = 8

def thetaLeafMap (i : Fin 9) : Fin 9 → Fin 8 :=
  if i = 0 then ![0, 3, 0, 2, 7, 6, 4, 5, 1]
  else if i = 1 then ![4, 0, 5, 0, 3, 1, 7, 6, 2]
  else if i = 2 then ![0, 3, 0, 6, 5, 2, 4, 7, 1]
  else if i = 3 then ![2, 0, 3, 0, 7, 1, 5, 4, 6]
  else if i = 5 then ![3, 0, 2, 1, 4, 0, 5, 7, 6]
  else ![0, 2, 1, 4, 3, 5, 7, 6, 0]

/-- All six degree-three zero restrictions are exactly the same theta-plus-leaf function. -/
theorem degree_three_restrict_to_leaf (i : Fin 9) (hi : DegreeThree i) (s : ℕ)
    (h : HasCircuitSize 9 (fun x => target9 (Function.update x i false)) s) :
    HasCircuitSize 8 thetaLeaf8 s := by
  have hp := relabel_size (thetaLeafMap i) _ s h
  have he : (fun x : Fin 8 → Bool =>
      target9 (Function.update (x ∘ thetaLeafMap i) i false)) = thetaLeaf8 := by
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      funext x <;>
      simp [target9, thetaLeaf8, thetaLeafMap, Function.comp_def, Bool.and_comm,
        Bool.or_comm, Bool.or_left_comm, Bool.or_assoc]
  rwa [he] at hp

theorem degree_three_zero_lower_bound
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (i : Fin 9) (hi : DegreeThree i) (s : ℕ)
    (h : HasCircuitSize 9 (fun x => target9 (Function.update x i false)) s) : 12 ≤ s :=
  theta_leaf_lower_bound h517 s (degree_three_restrict_to_leaf i hi s h)

theorem degree_three_dep (i : Fin 9) (hi : DegreeThree i) : Dep target9 i := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨(fun p => decide (p = 1)), ?_⟩; decide
  · refine ⟨(fun p => decide (p = 0)), ?_⟩; decide
  · refine ⟨(fun p => decide (p = 1)), ?_⟩; decide
  · refine ⟨(fun p => decide (p = 2)), ?_⟩; decide
  · refine ⟨(fun p => decide (p = 0)), ?_⟩; decide
  · refine ⟨(fun p => decide (p = 3)), ?_⟩; decide

theorem degree_three_restriction_nonconstant (i : Fin 9) (hi : DegreeThree i) (b : Bool) :
    ∃ x y : Fin 9 → Bool,
      target9 (Function.update x i b) ≠ target9 (Function.update y i b) := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨(fun _ => false), (fun p => decide (p = 1 ∨ p = 2)), ?_⟩
    cases b <;> decide
  · refine ⟨(fun _ => false), (fun p => decide (p = 2 ∨ p = 3)), ?_⟩
    cases b <;> decide
  · refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
    cases b <;> decide
  · refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
    cases b <;> decide
  · refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
    cases b <;> decide
  · refine ⟨(fun _ => false), (fun p => decide (p = 0 ∨ p = 1)), ?_⟩
    cases b <;> decide

theorem no_three_drop
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (i : Fin 9) (hi : DegreeThree i) (s : ℕ) (hs : s ≤ 14) :
    ¬ Drop target9 i false 3 s := by
  rintro ⟨t, hsave, ht⟩
  have hbound := degree_three_zero_lower_bound h517 i hi t ht
  omega

noncomputable def readerSet (gs : List Gate) (w : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range gs.length).filter (fun p => Reads gs p w)

theorem mem_readerSet (gs : List Gate) (w p : ℕ) : p ∈ readerSet gs w ↔ Reads gs p w := by
  classical
  simp only [readerSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨reads_len h, h⟩⟩

/-- Every degree-three raw input has at most two actual reader gates. -/
theorem degree_three_reader_count
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : DegreeThree i) : (readerSet gs i).card ≤ 2 := by
  by_contra h
  obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
    Finset.two_lt_card_iff.1 (by omega : 2 < (readerSet gs i).card)
  have hd := L.save3 i false (degree_three_restriction_nonconstant i hi false)
    p q r hpq hpr hqr
    (rc_input false ((mem_readerSet gs i p).1 hp))
    (rc_input false ((mem_readerSet gs i q).1 hq))
    (rc_input false ((mem_readerSet gs i r).1 hr))
  exact no_three_drop h517 i hi gs.length hs hd

/-- With two readers, either reader must be OR. An AND/NOT would pay a third gate. -/
theorem degree_three_companion_forces_or
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : DegreeThree i) (p q : ℕ) (hpq : p ≠ q)
    (g : Gate) (hg : gs[p]? = some g) (hip : (i : ℕ) ∈ g.inputs)
    (hq : Reads gs q i) : g.op = GateOp.or := by
  by_contra hor
  have hfix : g.op = GateOp.not ∨ false = fixBit g := by
    rcases L.hcl p g hg with ⟨hop, _⟩ | ⟨hop, _⟩
    · exact Or.inl hop
    · rcases hop with hand | hor'
      · exact Or.inr (by simp [fixBit, hand])
      · exact False.elim (hor hor')
  have hc := isC_reader L.hcl i p g hg hip false hfix
  exact no_three_drop h517 i hi gs.length hs
    (L.third i false (degree_three_restriction_nonconstant i hi false)
      p q hpq ⟨g, hg, hip⟩ hq hc)

theorem degree_three_two_readers_or
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : DegreeThree i) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (hip : (i : ℕ) ∈ gp.inputs) (hiq : (i : ℕ) ∈ gq.inputs) :
    gp.op = GateOp.or ∧ gq.op = GateOp.or :=
  ⟨degree_three_companion_forces_or h517 gs o L hs i hi p q hpq gp hp hip ⟨gq, hq, hiq⟩,
   degree_three_companion_forces_or h517 gs o L hs i hi q p hpq.symm gq hq hiq ⟨gp, hp, hip⟩⟩

/-- An AND/NOT reader of a degree-three input has exactly one actual successor reader.
The companion lemma already implies that it is the sole reader of the raw input. -/
theorem degree_three_and_not_unique_successor
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : DegreeThree i) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (hip : (i : ℕ) ∈ g.inputs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.not) :
    ∃! q, Reads gs q (9 + p) := by
  have hfix : g.op = GateOp.not ∨ false = fixBit g := by
    rcases hop with hand | hnot
    · exact Or.inr (by simp [fixBit, hand])
    · exact Or.inl hnot
  have hc := isC_reader L.hcl i p g hg hip false hfix
  have hp : Reads gs p i := ⟨g, hg, hip⟩
  obtain ⟨q, hpq, hq, hqrc⟩ := L.next i false
    (degree_three_restriction_nonconstant i hi false) p (reads_len hp) hc
  refine ⟨q, hq, ?_⟩
  intro r hr
  by_contra hrq
  have hpr : p < r := by
    have := reads_lt L.hcl hr
    omega
  exact no_three_drop h517 i hi gs.length hs
    (L.save3 i false (degree_three_restriction_nonconstant i hi false)
      p q r (Nat.ne_of_lt hpq) (Nat.ne_of_lt hpr) (Ne.symm hrq)
      (rc_input false hp) hqrc (rc_of_reads hr hc))

/-- A convenience form recording that the degree-three reader family is nonempty. -/
theorem degree_three_reader_range
    (h517 : ∀ s : ℕ, HasCircuitSize 7 theta7 s → 11 ≤ s)
    (gs : List Gate) (o : ℕ) (L : Least 9 target9 gs o) (hs : gs.length ≤ 14)
    (i : Fin 9) (hi : DegreeThree i) :
    1 ≤ (readerSet gs i).card ∧ (readerSet gs i).card ≤ 2 := by
  obtain ⟨p, hp⟩ := L.dep_read i (degree_three_dep i hi) (degree_three_restriction_nonconstant i hi)
  refine ⟨?_, degree_three_reader_count h517 gs o L hs i hi⟩
  exact Finset.one_le_card.2 ⟨p, (mem_readerSet gs i p).2 hp⟩

#print axioms theta_leaf_lower_bound
#print axioms degree_three_restrict_to_leaf
#print axioms degree_three_zero_lower_bound
#print axioms degree_three_reader_count
#print axioms degree_three_two_readers_or
#print axioms degree_three_and_not_unique_successor
#print axioms degree_three_reader_range

end PEqualNP.Research.L670
