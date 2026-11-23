import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith

/-
Local research lemma. This file is not a project submission and has no task lease.
It describes the exact positivity support of the few-NOT maximin recurrence.
-/

namespace LadderSupport

lemma foldr_max_pos_iff (f : ℕ → ℕ) (l : List ℕ) :
    0 < l.foldr (fun j acc => max acc (f j)) 0 ↔ ∃ j ∈ l, 0 < f j := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, List.mem_cons]
    rw [show (0 < max (l.foldr (fun j acc => max acc (f j)) 0) (f a)) ↔
        (0 < l.foldr (fun j acc => max acc (f j)) 0 ∨ 0 < f a) by omega, ih]
    constructor
    · rintro (⟨j, hj, hp⟩ | hp)
      · exact ⟨j, Or.inr hj, hp⟩
      · exact ⟨a, Or.inl rfl, hp⟩
    · rintro ⟨j, rfl | hj, hp⟩
      · exact Or.inr hp
      · exact Or.inl ⟨j, hj, hp⟩

theorem positivity_iff
    (G : ℕ → ℕ → ℕ → ℕ) (H : ℕ)
    (hbase : ∀ b K, 0 < G 0 b K ↔ 0 < K ∧ b < H)
    (hstep : ∀ t b K,
      G (t + 1) b K = (List.range (K + 1)).foldr
        (fun j acc => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) :
    ∀ t b K, 0 < G t b K ↔ 2 ^ t ≤ K ∧ b + 2 ^ t ≤ H := by
  intro t
  induction t with
  | zero =>
    intro b K
    rw [hbase]
    simp only [pow_zero]
    omega
  | succ t ih =>
    intro b K
    rw [hstep, foldr_max_pos_iff]
    simp only [List.mem_range]
    constructor
    · rintro ⟨j, hj, hp⟩
      have hp₁ : 0 < G t (b + j) (K - j) := by omega
      have hp₂ : 0 < G t b j := by omega
      have hr := (ih (b + j) (K - j)).mp hp₁
      have hl := (ih b j).mp hp₂
      rw [pow_succ]
      omega
    · rintro ⟨hK, hH⟩
      rw [pow_succ] at hK hH
      refine ⟨2 ^ t, by omega, ?_⟩
      have hp₁ : 0 < G t (b + 2 ^ t) (K - 2 ^ t) :=
        (ih (b + 2 ^ t) (K - 2 ^ t)).mpr ⟨by omega, by omega⟩
      have hp₂ : 0 < G t b (2 ^ t) :=
        (ih b (2 ^ t)).mpr ⟨le_rfl, by omega⟩
      omega

lemma base_coefficient_pos_iff (q b : ℕ) (hq : 0 < q) :
    0 < (q ^ 2 + q + 1) -
      (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1)) ↔
    b < q + 1 := by
  by_cases hb : b = 0
  · subst b
    simp
  · simp only [ite_eq_right hb]
    have hcut : 0 < (q ^ 2 + q + 1) - min (q ^ 2 + q + 1) (b * q + 1) ↔
        b * q + 1 < q ^ 2 + q + 1 := by omega
    rw [hcut]
    constructor
    · intro h
      by_contra h'
      have hmul : (q + 1) * q ≤ b * q := Nat.mul_le_mul_right q (by omega)
      nlinarith
    · intro h
      have hmul : b * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
      nlinarith

theorem ladder_positivity_iff
    (q : ℕ) (hq : 0 < q) (G : ℕ → ℕ → ℕ → ℕ)
    (hbase : ∀ b K,
      G 0 b K = ((q ^ 2 + q + 1) -
        (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (hstep : ∀ t b K,
      G (t + 1) b K = (List.range (K + 1)).foldr
        (fun j acc => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) :
    ∀ t b K, 0 < G t b K ↔ 2 ^ t ≤ K ∧ b + 2 ^ t ≤ q + 1 := by
  apply positivity_iff G (q + 1) _ hstep
  intro b K
  rw [hbase]
  constructor
  · intro h
    have hcoefficient := Nat.pos_of_mul_pos_right h
    have hwidth := Nat.pos_of_mul_pos_left h
    exact ⟨by omega, (base_coefficient_pos_iff q b hq).mp hcoefficient⟩
  · rintro ⟨hK, hb⟩
    exact Nat.mul_pos ((base_coefficient_pos_iff q b hq).mpr hb) (by omega)

theorem ladder_zero_iff
    (q : ℕ) (hq : 0 < q) (G : ℕ → ℕ → ℕ → ℕ)
    (hbase : ∀ b K,
      G 0 b K = ((q ^ 2 + q + 1) -
        (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (hstep : ∀ t b K,
      G (t + 1) b K = (List.range (K + 1)).foldr
        (fun j acc => max acc (min (G t (b + j) (K - j)) (G t b j))) 0)
    (t b K : ℕ) :
    G t b K = 0 ↔ K < 2 ^ t ∨ q + 1 < b + 2 ^ t := by
  have h := ladder_positivity_iff q hq G hbase hstep t b K
  omega

theorem ladder_zero_of_too_many_leaves
    (q : ℕ) (hq : 0 < q) (G : ℕ → ℕ → ℕ → ℕ)
    (hbase : ∀ b K,
      G 0 b K = ((q ^ 2 + q + 1) -
        (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (hstep : ∀ t b K,
      G (t + 1) b K = (List.range (K + 1)).foldr
        (fun j acc => max acc (min (G t (b + j) (K - j)) (G t b j))) 0)
    (s : ℕ) (hs : q + 1 < 2 ^ s) :
    G s 0 (q ^ 2 + q + 1) = 0 := by
  apply (ladder_zero_iff q hq G hbase hstep s 0 (q ^ 2 + q + 1)).mpr
  exact Or.inr (by simpa using hs)

theorem ladder_root_zero_iff
    (q : ℕ) (hq : 0 < q) (G : ℕ → ℕ → ℕ → ℕ)
    (hbase : ∀ b K,
      G 0 b K = ((q ^ 2 + q + 1) -
        (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (hstep : ∀ t b K,
      G (t + 1) b K = (List.range (K + 1)).foldr
        (fun j acc => max acc (min (G t (b + j) (K - j)) (G t b j))) 0)
    (s : ℕ) :
    G s 0 (q ^ 2 + q + 1) = 0 ↔ q + 1 < 2 ^ s := by
  rw [ladder_zero_iff q hq G hbase hstep]
  omega

end LadderSupport
