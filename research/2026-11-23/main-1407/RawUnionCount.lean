import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Lean.Elab.Tactic.Omega

/-!
The raw OR count for L-meta-1407. This is a counting argument on labels of
an existing DAG. A wide label has at least two elements. Such a label either
continues an earlier label, or joins two earlier labels at a charged gate.
Tracing a finite frontier backward pays at most one extra frontier wire at
each charged gate, even when predecessor cones are shared. Unary support
continuations carry no charge, which keeps aggregation gates separate.
-/

namespace PEqualNP.MetaComplexity.L1407

open Finset

variable {α : Type*} [DecidableEq α]
variable (charge : ℕ → Prop) [DecidablePred charge]

/-- Wide gates whose complete raw support lies in the specified set. -/
def rawWideGates (F : ℕ → Finset α) (n k : ℕ) (S : Finset α) : Finset ℕ :=
  (range k).filter (fun j => charge j ∧ 2 ≤ (F (n + j)).card ∧ F (n + j) ⊆ S)

theorem mem_rawWideGates (F : ℕ → Finset α) (n k j : ℕ) (S : Finset α) :
    j ∈ rawWideGates charge F n k S ↔
      j < k ∧ charge j ∧ 2 ≤ (F (n + j)).card ∧ F (n + j) ⊆ S := by
  simp only [rawWideGates, mem_filter, mem_range]

theorem rawWideGates_mono (F : ℕ → Finset α) (n : ℕ) {k l : ℕ}
    (S : Finset α) (hkl : k ≤ l) :
    rawWideGates charge F n k S ⊆ rawWideGates charge F n l S := by
  intro j hj
  obtain ⟨hj, hc, hwide, hsub⟩ := (mem_rawWideGates charge F n k j S).mp hj
  exact (mem_rawWideGates charge F n l j S).mpr ⟨by omega, hc, hwide, hsub⟩

theorem rawWideGates_succ_of_wide (F : ℕ → Finset α) (n k : ℕ) (S : Finset α)
    (hc : charge k) (hwide : 2 ≤ (F (n + k)).card) (hsub : F (n + k) ⊆ S) :
    rawWideGates charge F n (k + 1) S = insert k (rawWideGates charge F n k S) := by
  ext j
  simp only [mem_rawWideGates, mem_insert]
  constructor
  · rintro ⟨hj, hjc, hw, hs⟩
    by_cases h : j = k
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hjc, hw, hs⟩
  · rintro (rfl | ⟨hj, hjc, hw, hs⟩)
    · exact ⟨by omega, hc, hwide, hsub⟩
    · exact ⟨by omega, hjc, hw, hs⟩

theorem rawWideGates_card_succ (F : ℕ → Finset α) (n k : ℕ) (S : Finset α)
    (hc : charge k) (hwide : 2 ≤ (F (n + k)).card) (hsub : F (n + k) ⊆ S) :
    (rawWideGates charge F n (k + 1) S).card =
      (rawWideGates charge F n k S).card + 1 := by
  rw [rawWideGates_succ_of_wide charge F n k S hc hwide hsub, card_insert_of_notMem]
  simp only [mem_rawWideGates, lt_self_iff_false, false_and, not_false_eq_true]

theorem card_biUnion_le_card_of_small {β : Type*} [DecidableEq β]
    (R : Finset β) (F : β → Finset α) (h : ∀ r ∈ R, (F r).card ≤ 1) :
    (R.biUnion F).card ≤ R.card := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert a R ha ih =>
    have har : (F a).card ≤ 1 := h a (mem_insert_self _ _)
    have hr : (R.biUnion F).card ≤ R.card :=
      ih (fun r hr => h r (mem_insert_of_mem hr))
    rw [biUnion_insert, card_insert_of_notMem ha]
    have hu := card_union_le (F a) (R.biUnion F)
    omega

/-- A finite family of raw supports can have no more distinct inputs than
its root count plus the number of wide union gates in their common region.
Unary gates, empty supports and reused predecessors cost no extra unit. -/
theorem raw_union_count
    (F : ℕ → Finset α) (n : ℕ) (S : Finset α)
    (hinput : ∀ i < n, (F i).card ≤ 1) (k : ℕ) :
    (∀ j < k, 2 ≤ (F (n + j)).card →
      (∃ a : ℕ, a < n + j ∧ F (n + j) = F a) ∨
      (charge j ∧ ∃ a b : ℕ, a < n + j ∧ b < n + j ∧ F (n + j) = F a ∪ F b)) →
    ∀ R : Finset ℕ,
      (∀ r ∈ R, r < n + k) →
      (∀ r ∈ R, F r ⊆ S) →
      (R.biUnion F).card ≤ R.card + (rawWideGates charge F n k S).card := by
  induction k with
  | zero =>
    intro _ R hR _
    simpa [rawWideGates] using
      card_biUnion_le_card_of_small R F (fun r hr => hinput r (by simpa using hR r hr))
  | succ k ih =>
    intro hgate R hR hsub
    have hgate' : ∀ j < k, 2 ≤ (F (n + j)).card →
        (∃ a : ℕ, a < n + j ∧ F (n + j) = F a) ∨
        (charge j ∧ ∃ a b : ℕ, a < n + j ∧ b < n + j ∧ F (n + j) = F a ∪ F b) :=
      fun j hj hw => hgate j (by omega) hw
    have hwmono : (rawWideGates charge F n k S).card ≤
        (rawWideGates charge F n (k + 1) S).card :=
      card_le_card (rawWideGates_mono charge F n S (by omega))
    by_cases htop : n + k ∈ R
    · let E := R.erase (n + k)
      have hE : ∀ r ∈ E, r < n + k := by
        intro r hr
        obtain ⟨hne, hmem⟩ := mem_erase.mp hr
        have := hR r hmem
        omega
      have hEsub : ∀ r ∈ E, F r ⊆ S :=
        fun r hr => hsub r (mem_of_mem_erase hr)
      have hEcard : E.card + 1 = R.card := card_erase_add_one htop
      have hRunion : R.biUnion F = F (n + k) ∪ E.biUnion F := by
        rw [← insert_erase htop, biUnion_insert]
      by_cases hwide : 2 ≤ (F (n + k)).card
      · rcases hgate k (by omega) hwide with ⟨a, ha, heq⟩ | ⟨hc, a, b, ha, hb, hab⟩
        · let Q := insert a E
          have hQ : ∀ r ∈ Q, r < n + k := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · exact ha
            · exact hE r hr
          have hQsub : ∀ r ∈ Q, F r ⊆ S := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · rw [← heq]
              exact hsub (n + k) htop
            · exact hEsub r hr
          have hQunion : Q.biUnion F = R.biUnion F := by
            rw [hRunion, heq]
            exact biUnion_insert
          have hQcard : Q.card ≤ R.card := by
            have h1 := card_insert_le a E
            change (insert a E).card ≤ R.card
            omega
          have hbound := ih hgate' Q hQ hQsub
          rw [hQunion] at hbound
          omega
        · let Q := insert a (insert b E)
          have hQ : ∀ r ∈ Q, r < n + k := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · exact ha
            · rcases mem_insert.mp hr with rfl | hr
              · exact hb
              · exact hE r hr
          have habsub : F a ⊆ S ∧ F b ⊆ S := by
            apply union_subset_iff.mp
            rw [← hab]
            exact hsub (n + k) htop
          have hQsub : ∀ r ∈ Q, F r ⊆ S := by
            intro r hr
            rcases mem_insert.mp hr with rfl | hr
            · exact habsub.1
            · rcases mem_insert.mp hr with rfl | hr
              · exact habsub.2
              · exact hEsub r hr
          have hQunion : Q.biUnion F = R.biUnion F := by
            rw [hRunion, hab]
            simp only [Q, biUnion_insert, union_assoc]
          have hQcard : Q.card ≤ R.card + 1 := by
            have h1 := card_insert_le a (insert b E)
            have h2 := card_insert_le b E
            change (insert a (insert b E)).card ≤ R.card + 1
            omega
          have hbound := ih hgate' Q hQ hQsub
          rw [hQunion] at hbound
          have hwcard := rawWideGates_card_succ charge F n k S hc hwide (hsub (n + k) htop)
          omega
      · have hsmall : (F (n + k)).card ≤ 1 := by omega
        have hbound := ih hgate' E hE hEsub
        rw [hRunion]
        have hu := card_union_le (F (n + k)) (E.biUnion F)
        omega
    · have hR' : ∀ r ∈ R, r < n + k := by
        intro r hr
        have hne : r ≠ n + k := by rintro rfl; exact htop hr
        have := hR r hr
        omega
      have hbound := ih hgate' R hR' hsub
      omega

end PEqualNP.MetaComplexity.L1407

#print axioms PEqualNP.MetaComplexity.L1407.raw_union_count
