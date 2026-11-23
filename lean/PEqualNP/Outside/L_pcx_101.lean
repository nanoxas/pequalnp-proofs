import Mathlib.Data.Finset.Card
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_101

open PEqualNP.ProofComplexity

def resolution_check {V : Type} [DecidableEq V] (w : ℕ) (acc : List (Clause V)) :
    List (ℕ × ℕ × V) → Bool
  | [] => decide ((∅ : Clause V) ∈ acc)
  | (i, j, v) :: steps =>
    match acc[i]?, acc[j]? with
    | some C, some D =>
      let R := C.erase (v, true) ∪ D.erase (v, false)
      if (v, true) ∈ C ∧ (v, false) ∈ D ∧ R.card ≤ w then
        resolution_check w (R :: acc) steps
      else false
    | _, _ => false

lemma resolution_bases {V : Type} [DecidableEq V] (F : Set (Clause V)) (base : List (Clause V))
    (hb : ∀ C ∈ base, C ∈ F) : IsDerivation F base := by
  induction base with
  | nil => exact .nil
  | cons C cs ih =>
    exact .ax (ih (fun D hD => hb D (List.mem_cons_of_mem _ hD))) (hb C List.mem_cons_self)

lemma resolution_check_sound {V : Type} [DecidableEq V] (F : Set (Clause V)) (w : ℕ)
    (acc : List (Clause V)) (steps : List (ℕ × ℕ × V)) (hd : IsDerivation F acc)
    (hw : ∀ C ∈ acc, C.card ≤ w) (hc : resolution_check w acc steps = true) :
    ∃ π, IsRefutation F π ∧ ∀ C ∈ π, C.card ≤ w := by
  induction steps generalizing acc with
  | nil =>
    exact ⟨acc, ⟨hd, of_decide_eq_true hc⟩, hw⟩
  | cons s steps ih =>
    obtain ⟨i, j, v⟩ := s
    cases hi : acc[i]? with
    | none => simp [resolution_check, hi] at hc
    | some C =>
      cases hj : acc[j]? with
      | none => simp [resolution_check, hi, hj] at hc
      | some D =>
        let R := C.erase (v, true) ∪ D.erase (v, false)
        simp only [resolution_check, hi, hj] at hc
        change (if (v, true) ∈ C ∧ (v, false) ∈ D ∧ R.card ≤ w then
          resolution_check w (R :: acc) steps else false) = true at hc
        by_cases h : (v, true) ∈ C ∧ (v, false) ∈ D ∧ R.card ≤ w
        · rw [ite_eq_left h] at hc
          have hC : C ∈ acc := List.mem_of_getElem? hi
          have hD : D ∈ acc := List.mem_of_getElem? hj
          have hr : IsResolvent C D R := ⟨v, h.1, h.2.1, rfl⟩
          refine ih (R :: acc) (.res hd hC hD hr) ?_ hc
          intro E hE
          rcases List.mem_cons.mp hE with rfl | he
          · exact h.2.2
          · exact hw E he
        · rw [ite_eq_right h] at hc
          contradiction

theorem resolution_certificate {V : Type} [DecidableEq V] (F : Set (Clause V)) (w : ℕ)
    (base : List (Clause V)) (steps : List (ℕ × ℕ × V))
    (hb : ∀ C ∈ base, C ∈ F) (hw : ∀ C ∈ base, C.card ≤ w)
    (hc : resolution_check w base steps = true) :
    ∃ π, IsRefutation F π ∧ ∀ C ∈ π, C.card ≤ w :=
  resolution_check_sound F w base steps (resolution_bases F base hb) hw hc

private lemma narrow_resolvent_sound {V : Type} [DecidableEq V] (a : V → Bool) {C D R : Clause V}
    (h : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) : ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := h
  obtain ⟨l, hl, hal⟩ := hC
  obtain ⟨l', hl', hal'⟩ := hD
  by_cases h : l = (v, true)
  · subst l
    refine ⟨l', Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hl'⟩), hal'⟩
    rintro rfl
    simp_all
  · exact ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hl⟩), hal⟩

lemma narrow_sound {V : Type} [DecidableEq V] (a : V → Bool) {F : Set (Clause V)}
    {π : List (Clause V)} {w : ℕ} (der : IsDerivation F π)
    (axs : ∀ C ∈ F, C.card ≤ w → ClauseSat a C) (bounded : ∀ C ∈ π, C.card ≤ w) :
    ∀ C ∈ π, ClauseSat a C := by
  induction der with
  | nil =>
    intro C hC
    simp at hC
  | ax _ ha ih =>
    intro C hC
    rcases List.mem_cons.mp hC with rfl | ht
    · exact axs _ ha (bounded _ (by simp))
    · exact ih (fun D hD => bounded D (List.mem_cons_of_mem _ hD)) C ht
  | res _ hC hD hr ih =>
    have tail := ih (fun D hD => bounded D (List.mem_cons_of_mem _ hD))
    intro E hE
    rcases List.mem_cons.mp hE with rfl | ht
    · exact narrow_resolvent_sound a hr (tail _ hC) (tail _ hD)
    · exact tail E ht

lemma no_narrow_cover_refutation {n k w : ℕ} (edges : List (Fin n × Fin n))
    (F : Set (Clause (Fin n)))
    (hF : F = {C | ∃ e ∈ edges, C = {(e.1, true), (e.2, true)}} ∪
      {C | ∃ S : Finset (Fin n), S.card = k ∧ C = S.image (fun v => (v, false))})
    (hw : w < k) :
    ¬ ∃ π, IsRefutation F π ∧ ∀ C ∈ π, C.card ≤ w := by
  rintro ⟨π, ⟨der, emp⟩, bound⟩
  have hsat : ∀ C ∈ F, C.card ≤ w → ClauseSat (fun _ => true) C := by
    intro C hC hc
    rw [hF] at hC
    rcases hC with ⟨e, _, rfl⟩ | ⟨S, hsize, rfl⟩
    · exact ⟨(e.1,true), by simp, rfl⟩
    · have hinj : Function.Injective (fun v : Fin n => (v, false)) :=
        fun _ _ h => congrArg Prod.fst h
      rw [Finset.card_image_of_injective _ hinj, hsize] at hc
      exact (Nat.not_le_of_lt hw hc).elim
  obtain ⟨l, hl, _⟩ := narrow_sound (fun _ => true) der hsat bound ∅ emp
  simp at hl

def edges10 : List (Fin 10 × Fin 10) := [
    (0,1), (1,2), (2,3), (3,4), (4,0), (0,5),
    (1,6), (2,7), (3,8), (4,9), (5,7), (7,9),
    (9,6), (6,8), (8,5)]

def negatives10 : List (Finset (Fin 10)) := [
    {0,1,2,3,4,5}, {0,2,3,4,5,6}, {0,2,3,5,6,9}, {0,2,3,5,8,9},
    {1,2,3,5,6,9}, {1,2,3,5,8,9}, {1,2,3,4,5,6}, {0,1,2,3,5,6},
    {0,2,3,6,7,8}, {0,2,3,5,6,7}, {2,3,4,5,6,7}, {1,2,3,4,7,8},
    {1,2,3,7,8,9}, {2,3,5,6,7,8}, {0,2,3,4,7,8}, {0,2,3,4,8,9},
    {2,3,4,5,8,9}, {2,3,4,5,6,8}, {0,1,2,3,8,9}, {0,2,3,6,8,9},
    {0,2,4,5,8,9}, {1,2,4,5,8,9}, {1,2,4,7,8,9}, {2,4,6,7,8,9},
    {2,4,5,6,7,8}, {2,4,5,6,8,9}, {0,2,4,6,7,8}, {1,2,4,6,7,8},
    {0,1,3,4,6,7}, {0,1,3,4,7,8}, {1,3,4,5,7,9}, {1,3,4,5,6,7},
    {1,3,6,7,8,9}, {1,3,5,6,7,9}, {1,3,4,7,8,9}, {0,1,3,7,8,9}]

def bases10 : List (Clause (Fin 10)) :=
  ((edges10.map (fun e : Fin 10 × Fin 10 => {(e.1,true),(e.2,true)})) ++
    negatives10.map (fun S : Finset (Fin 10) => S.image (fun v => (v,false)))).reverse

def steps10 : List (ℕ × ℕ × Fin 10) := [
    (44,35,1), (0,35,6), (39,35,6), (0,35,8), (45,2,4), (0,1,9),
    (43,37,6), (0,37,8), (54,37,4), (0,37,0), (48,2,9), (0,1,6),
    (62,6,0), (0,1,1), (50,41,8), (0,41,5), (62,41,4), (0,43,0),
    (63,2,0), (0,1,5), (61,44,4), (0,44,9), (67,49,0), (0,45,5),
    (68,2,1), (0,1,6), (63,6,6), (0,1,8), (68,14,5), (0,1,7),
    (69,51,7), (0,51,9), (70,51,9), (0,51,6), (79,2,0), (0,1,5),
    (80,53,1), (0,53,6), (84,57,4), (0,71,0), (85,2,0), (0,1,5),
    (83,6,4), (0,1,9), (94,59,0), (0,59,1), (90,59,1), (0,59,6),
    (88,2,5), (0,1,7), (89,61,7), (0,61,9), (102,61,0), (0,61,1),
    (94,2,5), (0,1,7), (94,6,9), (0,1,6), (105,14,3), (0,1,4),
    (102,30,3), (0,1,8), (99,69,6), (0,69,8), (102,69,9), (0,69,6),
    (111,2,0), (0,1,5), (104,71,8), (0,71,5), (116,71,4), (0,71,0),
    (109,2,6), (0,1,8), (115,6,4), (0,1,9), (125,0,1), (0,49,2),
    (121,48,2), (0,1,7), (128,18,2), (0,1,3)]

lemma axiomMember10 (F : Set (Clause (Fin 10)))
    (hF : F = {C | ∃ e ∈ edges10, C = {(e.1,true),(e.2,true)}} ∪
      {C | ∃ S : Finset (Fin 10), S.card = 6 ∧ C = S.image (fun v => (v,false))}) :
    ∀ C ∈ bases10, C ∈ F := by
  intro C hC
  rw [hF]
  rw [bases10,List.mem_reverse,List.mem_append] at hC
  rcases hC with hp | hn
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact Or.inl ⟨e,he,rfl⟩
  · obtain ⟨S,hs,rfl⟩ := List.mem_map.mp hn
    have hc : negatives10.all (fun A => decide (A.card = 6)) = true := by decide
    exact Or.inr ⟨S,of_decide_eq_true (List.all_eq_true.mp hc S hs),rfl⟩

set_option maxRecDepth 16384 in
lemma axiomWidth10 : ∀ C ∈ bases10, C.card ≤ 6 := by
  have hc : bases10.all (fun C => decide (C.card ≤ 6)) = true := by decide
  exact fun C h => of_decide_eq_true (List.all_eq_true.mp hc C h)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
lemma calculation10 : resolution_check 6 bases10 steps10 = true := by decide

def edges11 : List (Fin 11 × Fin 11) := [
    (0,9), (0,10), (1,4), (1,8), (2,5), (2,10),
    (3,6), (3,7), (4,8), (4,10), (5,8), (5,9),
    (6,7), (6,10), (7,9), (8,9)]

def negatives11 : List (Finset (Fin 11)) := [
    {0,1,3,4,5,7,8}, {1,3,4,5,7,8,10}, {0,1,3,5,7,8,10}, {1,3,5,7,8,9,10},
    {0,1,4,5,6,7,8}, {1,4,5,6,7,8,10}, {0,1,5,6,7,8,10}, {1,5,6,7,8,9,10},
    {0,2,3,4,5,7,8}, {0,3,4,5,7,8,10}, {0,2,4,5,6,7,8}, {0,4,5,6,7,8,10},
    {3,4,5,7,8,9,10}, {4,5,6,7,8,9,10}, {1,2,3,4,5,7,9}, {1,2,4,5,6,7,9},
    {1,3,4,5,7,9,10}, {1,4,5,6,7,9,10}, {3,4,5,6,7,8,9}, {2,4,5,6,7,8,9},
    {0,4,5,6,7,8,9}, {0,5,6,7,8,9,10}, {1,2,3,4,5,6,9}, {1,3,4,5,6,9,10},
    {1,2,3,5,6,8,9}, {1,3,5,6,8,9,10}, {2,3,4,5,6,8,9}, {3,4,5,6,8,9,10},
    {0,2,3,4,6,8,9}, {2,3,4,6,8,9,10}, {0,2,4,6,7,8,9}, {2,4,6,7,8,9,10},
    {2,3,4,7,8,9,10}, {1,2,3,6,8,9,10}, {1,2,3,7,8,9,10}, {1,2,6,7,8,9,10}]

def bases11 : List (Clause (Fin 11)) :=
  ((edges11.map (fun e : Fin 11 × Fin 11 => {(e.1,true),(e.2,true)})) ++
    negatives11.map (fun S : Finset (Fin 11) => S.image (fun v => (v,false)))).reverse

def steps11 : List (ℕ × ℕ × Fin 11) := [
    (50,35,0), (0,35,10), (53,35,0), (0,35,9), (46,2,4), (0,1,10),
    (56,37,0), (0,37,10), (59,37,0), (0,37,9), (52,2,4), (0,1,10),
    (57,6,3), (0,1,6), (60,41,2), (0,41,10), (62,41,2), (0,41,10),
    (63,2,3), (0,1,6), (65,46,3), (0,45,6), (67,45,3), (0,45,6),
    (75,2,0), (0,1,9), (76,6,0), (0,1,10), (77,14,1), (0,1,4),
    (75,51,3), (0,51,6), (77,51,3), (0,51,6), (80,2,2), (0,1,10),
    (74,53,6), (0,60,10), (84,54,2), (0,61,10), (85,2,3), (0,1,6),
    (90,6,1), (0,1,8), (86,59,4), (0,59,10), (95,74,1), (0,69,4),
    (98,2,0), (0,1,10), (99,82,1), (0,74,4), (97,0,3), (0,5,6),
    (92,4,6), (0,1,10), (99,12,4), (0,1,8), (94,28,8), (0,1,9),
    (106,73,2), (0,73,10), (101,74,6), (0,82,7), (102,2,6), (0,1,10),
    (112,77,2), (0,77,10), (107,78,6), (0,101,7), (108,2,6), (0,1,10),
    (115,6,4), (0,1,8), (120,83,2), (0,83,10), (125,86,1), (0,85,4),
    (120,2,4), (0,1,10), (119,88,6), (0,104,7), (131,12,1), (0,1,4),
    (122,4,6), (0,1,10), (134,12,1), (0,1,8), (132,0,3), (0,31,7),
    (127,30,7), (0,1,9), (142,99,0), (0,99,10), (144,99,0), (0,99,10),
    (140,2,3), (0,1,7), (137,104,6), (0,102,7), (144,106,3), (0,105,7),
    (147,2,3), (0,1,6), (142,6,6), (0,1,10), (150,114,3), (0,129,7),
    (147,0,6), (0,85,7), (157,6,2), (0,1,5), (158,6,2), (0,1,10),
    (161,116,2), (0,125,5), (163,117,2), (0,149,5), (157,2,6), (0,1,7),
    (164,122,3), (0,121,7), (166,132,3), (0,151,7), (171,2,2), (0,1,5),
    (171,6,3), (0,1,6), (177,0,1), (0,17,4), (172,16,4), (0,1,10),
    (173,42,5), (0,1,8), (174,42,5), (0,1,9)]

lemma axiomMember11 (F : Set (Clause (Fin 11)))
    (hF : F = {C | ∃ e ∈ edges11, C = {(e.1,true),(e.2,true)}} ∪
      {C | ∃ S : Finset (Fin 11), S.card = 7 ∧ C = S.image (fun v => (v,false))}) :
    ∀ C ∈ bases11, C ∈ F := by
  intro C hC
  rw [hF]
  rw [bases11,List.mem_reverse,List.mem_append] at hC
  rcases hC with hp | hn
  · obtain ⟨e,he,rfl⟩ := List.mem_map.mp hp
    exact Or.inl ⟨e,he,rfl⟩
  · obtain ⟨S,hs,rfl⟩ := List.mem_map.mp hn
    have hc : negatives11.all (fun A => decide (A.card = 7)) = true := by decide
    exact Or.inr ⟨S,of_decide_eq_true (List.all_eq_true.mp hc S hs),rfl⟩

set_option maxRecDepth 16384 in
lemma axiomWidth11 : ∀ C ∈ bases11, C.card ≤ 7 := by
  have hc : bases11.all (fun C => decide (C.card ≤ 7)) = true := by decide
  exact fun C h => of_decide_eq_true (List.all_eq_true.mp hc C h)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
lemma calculation11 : resolution_check 7 bases11 steps11 = true := by decide

end PEqualNP.Outside.L_pcx_101

open PEqualNP.Outside.L_pcx_101

theorem PEqualNP.Outside.L_pcx_101 : (∀ F1 : Set (PEqualNP.ProofComplexity.Clause (Fin 10)), F1 = {Ca1 | ∃ ea1 ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)), Ca1 = {(ea1.1, true), (ea1.2, true)}} ∪ {Cb1 | ∃ Sb1 : Finset (Fin 10), Sb1.card = 6 ∧ Cb1 = Sb1.image (fun vb1 : Fin 10 => (vb1, false))} → (∃ πa1, PEqualNP.ProofComplexity.IsRefutation F1 πa1 ∧ ∀ Da1 ∈ πa1, Da1.card ≤ 6) ∧ ¬ ∃ πb1, PEqualNP.ProofComplexity.IsRefutation F1 πb1 ∧ ∀ Db1 ∈ πb1, Db1.card ≤ 5) ∧ (∀ F2 : Set (PEqualNP.ProofComplexity.Clause (Fin 11)), F2 = {Ca2 | ∃ ea2 ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)), Ca2 = {(ea2.1, true), (ea2.2, true)}} ∪ {Cb2 | ∃ Sb2 : Finset (Fin 11), Sb2.card = 7 ∧ Cb2 = Sb2.image (fun vb2 : Fin 11 => (vb2, false))} → (∃ πa2, PEqualNP.ProofComplexity.IsRefutation F2 πa2 ∧ ∀ Da2 ∈ πa2, Da2.card ≤ 7) ∧ ¬ ∃ πb2, PEqualNP.ProofComplexity.IsRefutation F2 πb2 ∧ ∀ Db2 ∈ πb2, Db2.card ≤ 6) := by
  constructor
  · intro F hF
    exact ⟨resolution_certificate F 6 bases10 steps10 (axiomMember10 F hF) axiomWidth10 calculation10,
      no_narrow_cover_refutation edges10 F hF (by decide)⟩
  · intro F hF
    exact ⟨resolution_certificate F 7 bases11 steps11 (axiomMember11 F hF) axiomWidth11 calculation11,
      no_narrow_cover_refutation edges11 F hF (by decide)⟩
