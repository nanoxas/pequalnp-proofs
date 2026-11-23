import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.List.Sort

namespace PEqualNP.Outside.L_gct_224

def extendFun {n : ℕ} (a : Fin (n + 1)) (t : Fin n → Fin n) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases a (fun i => if (t i).succ = a then 0 else (t i).succ)

lemma extendFun_eq {n : ℕ} (a : Fin (n+1)) (t : Equiv.Perm (Fin n)) :
    (Equiv.Perm.decomposeFin.symm (a,t) : Fin (n+1) → Fin (n+1)) = extendFun a t := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [extendFun]
  · simp [extendFun, Equiv.swap_apply_def, Fin.succ_ne_zero]

def allFun : (n : ℕ) → List (Fin n → Fin n)
  | 0 => [id]
  | n+1 => (List.finRange (n+1)).flatMap (fun a => (allFun n).map (extendFun a))

lemma sumFlat {α β : Type} (l : List α) (g : α → List β) (f : β → ℂ) :
    ((l.flatMap g).map f).sum = (l.map (fun a => ((g a).map f).sum)).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

lemma foldFun (n : ℕ) (f : (Fin n → Fin n) → ℂ) : ∑ t : Equiv.Perm (Fin n), f t = ((allFun n).map f).sum := by
  induction n with
  | zero => simp [allFun]
  | succ n ih =>
    rw [← Equiv.Perm.decomposeFin.symm.sum_comp, Fintype.sum_prod_type, Fin.sum_univ_def]
    simp only [allFun, sumFlat, List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    simp only [extendFun_eq]
    exact ih (fun t => f (extendFun a t))

def disp (t : Fin 6 → Fin 6) : List (Fin 6) := (List.ofFn fun i => i-t i).insertionSort (· ≤ ·)

noncomputable def mon (w : Fin 6 → ℂ) (l : List (Fin 6)) := (l.map w).prod

lemma disp_ok (t : Fin 6 → Fin 6) (w : Fin 6 → ℂ) : (∏ i : Fin 6, w (i-t i)) = mon w (disp t) := by
  rw [← Fin.prod_ofFn]
  unfold mon disp
  rw [show List.ofFn (fun i => w (i-t i)) = (List.ofFn (fun i => i-t i)).map w from List.map_ofFn.symm]
  exact ((List.perm_insertionSort (· ≤ ·) (List.ofFn fun i => i-t i)).map w).prod_eq.symm

noncomputable def evalGroups (w : Fin 6 → ℂ) (rows : List (List (Fin 6) × ℕ)) : ℂ :=
  (rows.map (fun x => x.2 • mon w x.1)).sum

def expandGroups (rows : List (List (Fin 6) × ℕ)) := rows.flatMap (fun x => List.replicate x.2 x.1)

lemma eval_expand (w : Fin 6 → ℂ) (rows : List (List (Fin 6) × ℕ)) :
    ((expandGroups rows).map (mon w)).sum = evalGroups w rows := by
  simp [evalGroups, expandGroups, sumFlat]

def bitGroup (d : ℕ) (l : List (Fin 6)) : Bool :=
  !(l.getD (5 - d / 3) 0).val.testBit (d % 3)

def sortGroups : ℕ → List (List (Fin 6)) → List (List (Fin 6))
  | 0, l => l
  | _+1, [] => []
  | d+1, x :: xs =>
    sortGroups d ((x :: xs).filter (bitGroup d)) ++
    sortGroups d ((x :: xs).filter fun k => !(bitGroup d k))

lemma sortGroups_perm (d) (l) : (sortGroups d l).Perm l := by
  induction d generalizing l with
  | zero => exact List.Perm.refl _
  | succ d ih =>
    cases l with
    | nil => exact List.Perm.refl _
    | cons x xs =>
      exact ((ih _).append (ih _)).trans (List.filter_append_perm (bitGroup d) (x :: xs))

def coeffGroups : List (List (Fin 6) × ℕ) :=
  [ ([0,0,0,0,0,0], 1),
    ([0,0,0,0,1,5], 6),
    ([0,0,0,0,2,4], 6),
    ([0,0,0,0,3,3], 3),
    ([0,0,0,1,1,4], 6),
    ([0,0,0,1,2,3], 12),
    ([0,0,0,2,2,2], 2),
    ([0,0,0,2,5,5], 6),
    ([0,0,0,3,4,5], 12),
    ([0,0,0,4,4,4], 2),
    ([0,0,1,1,1,3], 6),
    ([0,0,1,1,2,2], 9),
    ([0,0,1,1,5,5], 9),
    ([0,0,1,2,4,5], 24),
    ([0,0,1,3,3,5], 12),
    ([0,0,1,3,4,4], 18),
    ([0,0,2,2,3,5], 18),
    ([0,0,2,2,4,4], 9),
    ([0,0,2,3,3,4], 12),
    ([0,0,3,3,3,3], 3),
    ([0,0,3,5,5,5], 6),
    ([0,0,4,4,5,5], 9),
    ([0,1,1,1,1,2], 6),
    ([0,1,1,1,4,5], 12),
    ([0,1,1,2,3,5], 24),
    ([0,1,1,2,4,4], 12),
    ([0,1,1,3,3,4], 18),
    ([0,1,2,2,2,5], 12),
    ([0,1,2,2,3,4], 24),
    ([0,1,2,3,3,3], 12),
    ([0,1,2,5,5,5], 12),
    ([0,1,3,4,5,5], 24),
    ([0,1,4,4,4,5], 12),
    ([0,2,2,2,2,4], 6),
    ([0,2,2,2,3,3], 6),
    ([0,2,2,4,5,5], 12),
    ([0,2,3,3,5,5], 18),
    ([0,2,3,4,4,5], 24),
    ([0,2,4,4,4,4], 6),
    ([0,3,3,3,4,5], 12),
    ([0,3,3,4,4,4], 6),
    ([0,4,5,5,5,5], 6),
    ([1,1,1,1,1,1], 1),
    ([1,1,1,1,3,5], 6),
    ([1,1,1,1,4,4], 3),
    ([1,1,1,2,2,5], 6),
    ([1,1,1,2,3,4], 12),
    ([1,1,1,3,3,3], 2),
    ([1,1,1,5,5,5], 2),
    ([1,1,2,2,2,4], 6),
    ([1,1,2,2,3,3], 9),
    ([1,1,2,4,5,5], 18),
    ([1,1,3,3,5,5], 9),
    ([1,1,3,4,4,5], 12),
    ([1,1,4,4,4,4], 3),
    ([1,2,2,2,2,3], 6),
    ([1,2,2,3,5,5], 12),
    ([1,2,2,4,4,5], 18),
    ([1,2,3,3,4,5], 24),
    ([1,2,3,4,4,4], 12),
    ([1,3,3,3,3,5], 6),
    ([1,3,3,3,4,4], 6),
    ([1,3,5,5,5,5], 6),
    ([1,4,4,5,5,5], 6),
    ([2,2,2,2,2,2], 1),
    ([2,2,2,2,5,5], 3),
    ([2,2,2,3,4,5], 12),
    ([2,2,2,4,4,4], 2),
    ([2,2,3,3,3,5], 6),
    ([2,2,3,3,4,4], 9),
    ([2,2,5,5,5,5], 3),
    ([2,3,3,3,3,4], 6),
    ([2,3,4,5,5,5], 12),
    ([2,4,4,4,5,5], 6),
    ([3,3,3,3,3,3], 1),
    ([3,3,3,5,5,5], 2),
    ([3,3,4,4,5,5], 9),
    ([3,4,4,4,4,5], 6),
    ([4,4,4,4,4,4], 1),
    ([5,5,5,5,5,5], 1) ]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 16000 in
lemma coeffGroups_ok : sortGroups 18 ((allFun 6).map disp) = expandGroups coeffGroups := by decide +kernel

noncomputable def circ (a b c d e f : ℂ) : ℂ :=
  a^6 + 6 * a^4 * b * f + 6 * a^4 * c * e + 3 * a^4 * d^2 + 6 * a^3 * b^2 * e + 12 * a^3 * b * c * d + 2 * a^3 * c^3 + 6 * a^3 * c * f^2 + 12 * a^3 * d * e * f + 2 * a^3 * e^3 + 6 * a^2 * b^3 * d + 9 * a^2 * b^2 * c^2 + 9 * a^2 * b^2 * f^2 + 24 * a^2 * b * c * e * f + 12 * a^2 * b * d^2 * f + 18 * a^2 * b * d * e^2 + 18 * a^2 * c^2 * d * f + 9 * a^2 * c^2 * e^2 + 12 * a^2 * c * d^2 * e + 3 * a^2 * d^4 + 6 * a^2 * d * f^3 + 9 * a^2 * e^2 * f^2 + 6 * a * b^4 * c + 12 * a * b^3 * e * f + 24 * a * b^2 * c * d * f + 12 * a * b^2 * c * e^2 + 18 * a * b^2 * d^2 * e + 12 * a * b * c^3 * f + 24 * a * b * c^2 * d * e + 12 * a * b * c * d^3 + 12 * a * b * c * f^3 + 24 * a * b * d * e * f^2 + 12 * a * b * e^3 * f + 6 * a * c^4 * e + 6 * a * c^3 * d^2 + 12 * a * c^2 * e * f^2 + 18 * a * c * d^2 * f^2 + 24 * a * c * d * e^2 * f + 6 * a * c * e^4 + 12 * a * d^3 * e * f + 6 * a * d^2 * e^3 + 6 * a * e * f^4 + b^6 + 6 * b^4 * d * f + 3 * b^4 * e^2 + 6 * b^3 * c^2 * f + 12 * b^3 * c * d * e + 2 * b^3 * d^3 + 2 * b^3 * f^3 + 6 * b^2 * c^3 * e + 9 * b^2 * c^2 * d^2 + 18 * b^2 * c * e * f^2 + 9 * b^2 * d^2 * f^2 + 12 * b^2 * d * e^2 * f + 3 * b^2 * e^4 + 6 * b * c^4 * d + 12 * b * c^2 * d * f^2 + 18 * b * c^2 * e^2 * f + 24 * b * c * d^2 * e * f + 12 * b * c * d * e^3 + 6 * b * d^4 * f + 6 * b * d^3 * e^2 + 6 * b * d * f^4 + 6 * b * e^2 * f^3 + c^6 + 3 * c^4 * f^2 + 12 * c^3 * d * e * f + 2 * c^3 * e^3 + 6 * c^2 * d^3 * f + 9 * c^2 * d^2 * e^2 + 3 * c^2 * f^4 + 6 * c * d^4 * e + 12 * c * d * e * f^3 + 6 * c * e^3 * f^2 + d^6 + 2 * d^3 * f^3 + 9 * d^2 * e^2 * f^2 + 6 * d * e^4 * f + e^6 + f^6


set_option maxHeartbeats 2000000 in
set_option maxRecDepth 16000 in
lemma eval_coeff (w : Fin 6 → ℂ) : evalGroups w coeffGroups = circ (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) := by
  simp only [evalGroups, coeffGroups, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mon, List.prod_cons, List.prod_nil, nsmul_eq_mul, Nat.cast_ofNat, circ]
  ring

lemma circ_eq (w : Fin 6 → ℂ) :
    Matrix.permanent (Matrix.of fun (i j : Fin 6) => w (j-i)) = circ (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) := by
  simp only [Matrix.permanent, Matrix.of_apply]
  rw [foldFun 6 (fun t => ∏ i, w (i-t i))]
  simp only [disp_ok]
  change (List.map ((mon w) ∘ disp) (allFun 6)).sum = _
  rw [← List.map_map]
  calc
    _ = ((sortGroups 18 ((allFun 6).map disp)).map (mon w)).sum := ((sortGroups_perm 18 _).map (mon w)).sum_eq.symm
    _ = _ := by rw [coeffGroups_ok, eval_expand, eval_coeff]

noncomputable def cc1 (a b c d e f : ℂ) : ℂ :=
  a + b + c + d + e + f

noncomputable def cc2 (a b c d e f : ℂ) : ℂ :=
  5 * a^2 + 8 * a * b + 8 * a * c + 8 * a * d + 8 * a * e + 8 * a * f + 5 * b^2 + 8 * b * c + 8 * b * d + 8 * b * e + 8 * b * f + 5 * c^2 + 8 * c * d + 8 * c * e + 8 * c * f + 5 * d^2 + 8 * d * e + 8 * d * f + 5 * e^2 + 8 * e * f + 5 * f^2

noncomputable def cc3 (a b c d e f : ℂ) : ℂ :=
  5 * a^3 + 9 * a^2 * b + 9 * a^2 * c + 9 * a^2 * d + 9 * a^2 * e + 9 * a^2 * f + 9 * a * b^2 + 15 * a * b * c + 15 * a * b * d + 15 * a * b * e + 15 * a * b * f + 9 * a * c^2 + 15 * a * c * d + 15 * a * c * e + 15 * a * c * f + 9 * a * d^2 + 15 * a * d * e + 15 * a * d * f + 9 * a * e^2 + 15 * a * e * f + 9 * a * f^2 + 5 * b^3 + 9 * b^2 * c + 9 * b^2 * d + 9 * b^2 * e + 9 * b^2 * f + 9 * b * c^2 + 15 * b * c * d + 15 * b * c * e + 15 * b * c * f + 9 * b * d^2 + 15 * b * d * e + 15 * b * d * f + 9 * b * e^2 + 15 * b * e * f + 9 * b * f^2 + 5 * c^3 + 9 * c^2 * d + 9 * c^2 * e + 9 * c^2 * f + 9 * c * d^2 + 15 * c * d * e + 15 * c * d * f + 9 * c * e^2 + 15 * c * e * f + 9 * c * f^2 + 5 * d^3 + 9 * d^2 * e + 9 * d^2 * f + 9 * d * e^2 + 15 * d * e * f + 9 * d * f^2 + 5 * e^3 + 9 * e^2 * f + 9 * e * f^2 + 5 * f^3

noncomputable def cc4 (a b c d e f : ℂ) : ℂ :=
  5 * a^4 + 8 * a^3 * b + 8 * a^3 * c + 8 * a^3 * d + 8 * a^3 * e + 8 * a^3 * f + 9 * a^2 * b^2 + 16 * a^2 * b * c + 16 * a^2 * b * d + 16 * a^2 * b * e + 18 * a^2 * b * f + 9 * a^2 * c^2 + 16 * a^2 * c * d + 18 * a^2 * c * e + 16 * a^2 * c * f + 10 * a^2 * d^2 + 16 * a^2 * d * e + 16 * a^2 * d * f + 9 * a^2 * e^2 + 16 * a^2 * e * f + 9 * a^2 * f^2 + 8 * a * b^3 + 18 * a * b^2 * c + 16 * a * b^2 * d + 16 * a * b^2 * e + 16 * a * b^2 * f + 16 * a * b * c^2 + 28 * a * b * c * d + 24 * a * b * c * e + 28 * a * b * c * f + 16 * a * b * d^2 + 32 * a * b * d * e + 24 * a * b * d * f + 16 * a * b * e^2 + 28 * a * b * e * f + 16 * a * b * f^2 + 8 * a * c^3 + 16 * a * c^2 * d + 18 * a * c^2 * e + 16 * a * c^2 * f + 16 * a * c * d^2 + 24 * a * c * d * e + 32 * a * c * d * f + 18 * a * c * e^2 + 24 * a * c * e * f + 16 * a * c * f^2 + 8 * a * d^3 + 16 * a * d^2 * e + 16 * a * d^2 * f + 16 * a * d * e^2 + 28 * a * d * e * f + 16 * a * d * f^2 + 8 * a * e^3 + 16 * a * e^2 * f + 18 * a * e * f^2 + 8 * a * f^3 + 5 * b^4 + 8 * b^3 * c + 8 * b^3 * d + 8 * b^3 * e + 8 * b^3 * f + 9 * b^2 * c^2 + 16 * b^2 * c * d + 16 * b^2 * c * e + 16 * b^2 * c * f + 9 * b^2 * d^2 + 16 * b^2 * d * e + 18 * b^2 * d * f + 10 * b^2 * e^2 + 16 * b^2 * e * f + 9 * b^2 * f^2 + 8 * b * c^3 + 18 * b * c^2 * d + 16 * b * c^2 * e + 16 * b * c^2 * f + 16 * b * c * d^2 + 28 * b * c * d * e + 24 * b * c * d * f + 16 * b * c * e^2 + 32 * b * c * e * f + 16 * b * c * f^2 + 8 * b * d^3 + 16 * b * d^2 * e + 18 * b * d^2 * f + 16 * b * d * e^2 + 24 * b * d * e * f + 18 * b * d * f^2 + 8 * b * e^3 + 16 * b * e^2 * f + 16 * b * e * f^2 + 8 * b * f^3 + 5 * c^4 + 8 * c^3 * d + 8 * c^3 * e + 8 * c^3 * f + 9 * c^2 * d^2 + 16 * c^2 * d * e + 16 * c^2 * d * f + 9 * c^2 * e^2 + 16 * c^2 * e * f + 10 * c^2 * f^2 + 8 * c * d^3 + 18 * c * d^2 * e + 16 * c * d^2 * f + 16 * c * d * e^2 + 28 * c * d * e * f + 16 * c * d * f^2 + 8 * c * e^3 + 16 * c * e^2 * f + 16 * c * e * f^2 + 8 * c * f^3 + 5 * d^4 + 8 * d^3 * e + 8 * d^3 * f + 9 * d^2 * e^2 + 16 * d^2 * e * f + 9 * d^2 * f^2 + 8 * d * e^3 + 18 * d * e^2 * f + 16 * d * e * f^2 + 8 * d * f^3 + 5 * e^4 + 8 * e^3 * f + 9 * e^2 * f^2 + 8 * e * f^3 + 5 * f^4

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8000 in
noncomputable def cc5 (a b c d e f : ℂ) : ℂ :=
  a^5 + a^4 * b + a^4 * c + a^4 * d + a^4 * e + a^4 * f + a^3 * b^2 + 2 * a^3 * b * c + 2 * a^3 * b * d + 2 * a^3 * b * e + 4 * a^3 * b * f + a^3 * c^2 + 2 * a^3 * c * d + 4 * a^3 * c * e + 2 * a^3 * c * f + 2 * a^3 * d^2 + 2 * a^3 * d * e + 2 * a^3 * d * f + a^3 * e^2 + 2 * a^3 * e * f + a^3 * f^2 + a^2 * b^3 + 3 * a^2 * b^2 * c + 3 * a^2 * b^2 * d + 3 * a^2 * b^2 * e + 3 * a^2 * b^2 * f + 3 * a^2 * b * c^2 + 6 * a^2 * b * c * d + 4 * a^2 * b * c * e + 4 * a^2 * b * c * f + 2 * a^2 * b * d^2 + 6 * a^2 * b * d * e + 4 * a^2 * b * d * f + 3 * a^2 * b * e^2 + 4 * a^2 * b * e * f + 3 * a^2 * b * f^2 + a^2 * c^3 + 3 * a^2 * c^2 * d + 3 * a^2 * c^2 * e + 3 * a^2 * c^2 * f + 2 * a^2 * c * d^2 + 4 * a^2 * c * d * e + 6 * a^2 * c * d * f + 3 * a^2 * c * e^2 + 4 * a^2 * c * e * f + 3 * a^2 * c * f^2 + 2 * a^2 * d^3 + 2 * a^2 * d^2 * e + 2 * a^2 * d^2 * f + 3 * a^2 * d * e^2 + 6 * a^2 * d * e * f + 3 * a^2 * d * f^2 + a^2 * e^3 + 3 * a^2 * e^2 * f + 3 * a^2 * e * f^2 + a^2 * f^3 + a * b^4 + 4 * a * b^3 * c + 2 * a * b^3 * d + 2 * a * b^3 * e + 2 * a * b^3 * f + 3 * a * b^2 * c^2 + 4 * a * b^2 * c * d + 4 * a * b^2 * c * e + 4 * a * b^2 * c * f + 3 * a * b^2 * d^2 + 6 * a * b^2 * d * e + 4 * a * b^2 * d * f + 2 * a * b^2 * e^2 + 6 * a * b^2 * e * f + 3 * a * b^2 * f^2 + 2 * a * b * c^3 + 4 * a * b * c^2 * d + 4 * a * b * c^2 * e + 6 * a * b * c^2 * f + 6 * a * b * c * d^2 + 8 * a * b * c * d * e + 8 * a * b * c * d * f + 4 * a * b * c * e^2 + 8 * a * b * c * e * f + 6 * a * b * c * f^2 + 2 * a * b * d^3 + 6 * a * b * d^2 * e + 4 * a * b * d^2 * f + 6 * a * b * d * e^2 + 8 * a * b * d * e * f + 4 * a * b * d * f^2 + 2 * a * b * e^3 + 6 * a * b * e^2 * f + 4 * a * b * e * f^2 + 2 * a * b * f^3 + a * c^4 + 2 * a * c^3 * d + 4 * a * c^3 * e + 2 * a * c^3 * f + 3 * a * c^2 * d^2 + 4 * a * c^2 * d * e + 6 * a * c^2 * d * f + 3 * a * c^2 * e^2 + 4 * a * c^2 * e * f + 2 * a * c^2 * f^2 + 2 * a * c * d^3 + 4 * a * c * d^2 * e + 6 * a * c * d^2 * f + 4 * a * c * d * e^2 + 8 * a * c * d * e * f + 6 * a * c * d * f^2 + 4 * a * c * e^3 + 4 * a * c * e^2 * f + 4 * a * c * e * f^2 + 2 * a * c * f^3 + a * d^4 + 2 * a * d^3 * e + 2 * a * d^3 * f + 3 * a * d^2 * e^2 + 6 * a * d^2 * e * f + 3 * a * d^2 * f^2 + 2 * a * d * e^3 + 4 * a * d * e^2 * f + 4 * a * d * e * f^2 + 2 * a * d * f^3 + a * e^4 + 2 * a * e^3 * f + 3 * a * e^2 * f^2 + 4 * a * e * f^3 + a * f^4 + b^5 + b^4 * c + b^4 * d + b^4 * e + b^4 * f + b^3 * c^2 + 2 * b^3 * c * d + 2 * b^3 * c * e + 2 * b^3 * c * f + b^3 * d^2 + 2 * b^3 * d * e + 4 * b^3 * d * f + 2 * b^3 * e^2 + 2 * b^3 * e * f + b^3 * f^2 + b^2 * c^3 + 3 * b^2 * c^2 * d + 3 * b^2 * c^2 * e + 3 * b^2 * c^2 * f + 3 * b^2 * c * d^2 + 6 * b^2 * c * d * e + 4 * b^2 * c * d * f + 2 * b^2 * c * e^2 + 6 * b^2 * c * e * f + 3 * b^2 * c * f^2 + b^2 * d^3 + 3 * b^2 * d^2 * e + 3 * b^2 * d^2 * f + 2 * b^2 * d * e^2 + 4 * b^2 * d * e * f + 3 * b^2 * d * f^2 + 2 * b^2 * e^3 + 2 * b^2 * e^2 * f + 3 * b^2 * e * f^2 + b^2 * f^3 + b * c^4 + 4 * b * c^3 * d + 2 * b * c^3 * e + 2 * b * c^3 * f + 3 * b * c^2 * d^2 + 4 * b * c^2 * d * e + 4 * b * c^2 * d * f + 3 * b * c^2 * e^2 + 6 * b * c^2 * e * f + 2 * b * c^2 * f^2 + 2 * b * c * d^3 + 4 * b * c * d^2 * e + 4 * b * c * d^2 * f + 6 * b * c * d * e^2 + 8 * b * c * d * e * f + 4 * b * c * d * f^2 + 2 * b * c * e^3 + 6 * b * c * e^2 * f + 6 * b * c * e * f^2 + 2 * b * c * f^3 + b * d^4 + 2 * b * d^3 * e + 4 * b * d^3 * f + 3 * b * d^2 * e^2 + 4 * b * d^2 * e * f + 3 * b * d^2 * f^2 + 2 * b * d * e^3 + 4 * b * d * e^2 * f + 4 * b * d * e * f^2 + 4 * b * d * f^3 + b * e^4 + 2 * b * e^3 * f + 3 * b * e^2 * f^2 + 2 * b * e * f^3 + b * f^4 + c^5 + c^4 * d + c^4 * e + c^4 * f + c^3 * d^2 + 2 * c^3 * d * e + 2 * c^3 * d * f + c^3 * e^2 + 2 * c^3 * e * f + 2 * c^3 * f^2 + c^2 * d^3 + 3 * c^2 * d^2 * e + 3 * c^2 * d^2 * f + 3 * c^2 * d * e^2 + 6 * c^2 * d * e * f + 2 * c^2 * d * f^2 + c^2 * e^3 + 3 * c^2 * e^2 * f + 2 * c^2 * e * f^2 + 2 * c^2 * f^3 + c * d^4 + 4 * c * d^3 * e + 2 * c * d^3 * f + 3 * c * d^2 * e^2 + 4 * c * d^2 * e * f + 3 * c * d^2 * f^2 + 2 * c * d * e^3 + 4 * c * d * e^2 * f + 6 * c * d * e * f^2 + 2 * c * d * f^3 + c * e^4 + 2 * c * e^3 * f + 3 * c * e^2 * f^2 + 2 * c * e * f^3 + c * f^4 + d^5 + d^4 * e + d^4 * f + d^3 * e^2 + 2 * d^3 * e * f + d^3 * f^2 + d^2 * e^3 + 3 * d^2 * e^2 * f + 3 * d^2 * e * f^2 + d^2 * f^3 + d * e^4 + 4 * d * e^3 * f + 3 * d * e^2 * f^2 + 2 * d * e * f^3 + d * f^4 + e^5 + e^4 * f + e^3 * f^2 + e^2 * f^3 + e * f^4 + f^5

noncomputable def cc6 (a b c d e f : ℂ) : ℂ :=
  a^6 + 6 * a^4 * b * f + 6 * a^4 * c * e + 3 * a^4 * d^2 + 6 * a^3 * b^2 * e + 12 * a^3 * b * c * d + 2 * a^3 * c^3 + 6 * a^3 * c * f^2 + 12 * a^3 * d * e * f + 2 * a^3 * e^3 + 6 * a^2 * b^3 * d + 9 * a^2 * b^2 * c^2 + 9 * a^2 * b^2 * f^2 + 24 * a^2 * b * c * e * f + 12 * a^2 * b * d^2 * f + 18 * a^2 * b * d * e^2 + 18 * a^2 * c^2 * d * f + 9 * a^2 * c^2 * e^2 + 12 * a^2 * c * d^2 * e + 3 * a^2 * d^4 + 6 * a^2 * d * f^3 + 9 * a^2 * e^2 * f^2 + 6 * a * b^4 * c + 12 * a * b^3 * e * f + 24 * a * b^2 * c * d * f + 12 * a * b^2 * c * e^2 + 18 * a * b^2 * d^2 * e + 12 * a * b * c^3 * f + 24 * a * b * c^2 * d * e + 12 * a * b * c * d^3 + 12 * a * b * c * f^3 + 24 * a * b * d * e * f^2 + 12 * a * b * e^3 * f + 6 * a * c^4 * e + 6 * a * c^3 * d^2 + 12 * a * c^2 * e * f^2 + 18 * a * c * d^2 * f^2 + 24 * a * c * d * e^2 * f + 6 * a * c * e^4 + 12 * a * d^3 * e * f + 6 * a * d^2 * e^3 + 6 * a * e * f^4 + b^6 + 6 * b^4 * d * f + 3 * b^4 * e^2 + 6 * b^3 * c^2 * f + 12 * b^3 * c * d * e + 2 * b^3 * d^3 + 2 * b^3 * f^3 + 6 * b^2 * c^3 * e + 9 * b^2 * c^2 * d^2 + 18 * b^2 * c * e * f^2 + 9 * b^2 * d^2 * f^2 + 12 * b^2 * d * e^2 * f + 3 * b^2 * e^4 + 6 * b * c^4 * d + 12 * b * c^2 * d * f^2 + 18 * b * c^2 * e^2 * f + 24 * b * c * d^2 * e * f + 12 * b * c * d * e^3 + 6 * b * d^4 * f + 6 * b * d^3 * e^2 + 6 * b * d * f^4 + 6 * b * e^2 * f^3 + c^6 + 3 * c^4 * f^2 + 12 * c^3 * d * e * f + 2 * c^3 * e^3 + 6 * c^2 * d^3 * f + 9 * c^2 * d^2 * e^2 + 3 * c^2 * f^4 + 6 * c * d^4 * e + 12 * c * d * e * f^3 + 6 * c * e^3 * f^2 + d^6 + 2 * d^3 * f^3 + 9 * d^2 * e^2 * f^2 + 6 * d * e^4 * f + e^6 + f^6
set_option maxHeartbeats 30000000 in
set_option maxRecDepth 24000 in
lemma circ_shift (a b c d e f t : ℂ) : circ (1+t*a) (1+t*b) (1+t*c) (1+t*d) (1+t*e) (1+t*f) = 720 + 720 * t^1 * cc1 a b c d e f + 72 * t^2 * cc2 a b c d e f + 24 * t^3 * cc3 a b c d e f + 6 * t^4 * cc4 a b c d e f + 6 * t^5 * cc5 a b c d e f + 1 * t^6 * cc6 a b c d e f := by
  unfold circ cc1 cc2 cc3 cc4 cc5 cc6
  ring

lemma vanishing (a b c d e f : ℂ) (h : ∀ t : ℂ, 720 + 720 * t^1 * a + 72 * t^2 * b + 24 * t^3 * c + 6 * t^4 * d + 6 * t^5 * e + 1 * t^6 * f = 720) : a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 := by
  have h1 := h (1)
  have h2 := h (-1)
  have h3 := h (2)
  have h4 := h (-2)
  have h5 := h (3)
  have h6 := h (-3)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (1/960 : ℂ) * h1 + (-1/960 : ℂ) * h2 + (-1/4800 : ℂ) * h3 + (1/4800 : ℂ) * h4 + (1/43200 : ℂ) * h5 + (-1/43200 : ℂ) * h6
  · linear_combination (1/96 : ℂ) * h1 + (1/96 : ℂ) * h2 + (-1/960 : ℂ) * h3 + (-1/960 : ℂ) * h4 + (1/12960 : ℂ) * h5 + (1/12960 : ℂ) * h6
  · linear_combination (-13/1152 : ℂ) * h1 + (13/1152 : ℂ) * h2 + (1/144 : ℂ) * h3 + (-1/144 : ℂ) * h4 + (-1/1152 : ℂ) * h5 + (1/1152 : ℂ) * h6
  · linear_combination (-13/288 : ℂ) * h1 + (-13/288 : ℂ) * h2 + (1/72 : ℂ) * h3 + (1/72 : ℂ) * h4 + (-1/864 : ℂ) * h5 + (-1/864 : ℂ) * h6
  · linear_combination (1/288 : ℂ) * h1 + (-1/288 : ℂ) * h2 + (-1/360 : ℂ) * h3 + (1/360 : ℂ) * h4 + (1/1440 : ℂ) * h5 + (-1/1440 : ℂ) * h6
  · linear_combination (1/48 : ℂ) * h1 + (1/48 : ℂ) * h2 + (-1/120 : ℂ) * h3 + (-1/120 : ℂ) * h4 + (1/720 : ℂ) * h5 + (1/720 : ℂ) * h6
noncomputable def q2 (a b c d : ℂ) : ℂ :=
  a^2 + a * b + b^2 + c^2 + c * d + d^2

noncomputable def q3 (a b c d : ℂ) : ℂ :=
  -a^2 * b - a * b^2 - c^2 * d - c * d^2

noncomputable def q4 (a b c d : ℂ) : ℂ :=
  3 * a^4 + 6 * a^3 * b + 10 * a^2 * b^2 + 4 * a^2 * b * c - 6 * a^2 * b * d - 8 * a^2 * c^2 - 6 * a^2 * c * d - 3 * a^2 * d^2 + 8 * a * b^3 + 8 * a * b^2 * c - 4 * a * b^2 * d - 4 * a * b * c^2 - 4 * a * b * c * d - 6 * a * b * d^2 - 4 * a * c^2 * d - 6 * a * c * d^2 + 4 * b^4 + 4 * b^2 * c^2 - 4 * b^2 * c * d - 8 * b^2 * d^2 + 8 * b * c^2 * d + 4 * b * c * d^2 + 4 * c^4 + 8 * c^3 * d + 10 * c^2 * d^2 + 6 * c * d^3 + 3 * d^4

noncomputable def q5 (a b c d : ℂ) : ℂ :=
  -a^4 * b - 2 * a^4 * c - 3 * a^3 * b^2 - 6 * a^3 * b * c - 2 * a^3 * b * d + 2 * a^3 * c * d + 3 * a^3 * d^2 - 4 * a^2 * b^3 - 4 * a^2 * b^2 * c - a^2 * b^2 * d + 2 * a^2 * b * c^2 + 8 * a^2 * b * c * d + 6 * a^2 * b * d^2 + 5 * a^2 * c^2 * d + 6 * a^2 * c * d^2 + 3 * a^2 * d^3 - 2 * a * b^4 + 2 * a * b^2 * c^2 + 6 * a * b^2 * c * d + 5 * a * b^2 * d^2 + 6 * a * b * c^2 * d + 8 * a * b * c * d^2 + 2 * a * b * d^3 - a * c^2 * d^2 - 2 * a * c * d^3 + 2 * b^2 * c^2 * d + 2 * b^2 * c * d^2 - 4 * b * c^2 * d^2 - 6 * b * c * d^3 - 2 * b * d^4 - 2 * c^4 * d - 4 * c^3 * d^2 - 3 * c^2 * d^3 - c * d^4

noncomputable def q6 (a b c d : ℂ) : ℂ :=
  3 * a^4 * b^2 + 12 * a^4 * b * c + 12 * a^4 * b * d + 9 * a^4 * c^2 + 12 * a^4 * c * d + 6 * a^4 * d^2 + 12 * a^3 * b^3 + 42 * a^3 * b^2 * c + 36 * a^3 * b^2 * d + 30 * a^3 * b * c^2 + 24 * a^3 * b * c * d - 6 * a^3 * b * d^2 - 12 * a^3 * c^2 * d - 18 * a^3 * c * d^2 + 18 * a^2 * b^4 + 48 * a^2 * b^3 * c + 36 * a^2 * b^3 * d + 30 * a^2 * b^2 * c^2 - 12 * a^2 * b^2 * c * d - 33 * a^2 * b^2 * d^2 - 24 * a^2 * b * c^3 - 84 * a^2 * b * c^2 * d - 78 * a^2 * b * c * d^2 - 18 * a^2 * b * d^3 - 12 * a^2 * c^4 - 36 * a^2 * c^3 * d - 33 * a^2 * c^2 * d^2 - 6 * a^2 * c * d^3 + 6 * a^2 * d^4 + 12 * a * b^5 + 24 * a * b^4 * c + 12 * a * b^4 * d - 48 * a * b^3 * c * d - 36 * a * b^3 * d^2 - 48 * a * b^2 * c^3 - 120 * a * b^2 * c^2 * d - 84 * a * b^2 * c * d^2 - 12 * a * b^2 * d^3 - 24 * a * b * c^4 - 48 * a * b * c^3 * d - 12 * a * b * c^2 * d^2 + 24 * a * b * c * d^3 + 12 * a * b * d^4 + 12 * a * c^4 * d + 36 * a * c^3 * d^2 + 36 * a * c^2 * d^3 + 12 * a * c * d^4 + 4 * b^6 - 24 * b^4 * c * d - 12 * b^4 * d^2 - 32 * b^3 * c^3 - 48 * b^3 * c^2 * d - 24 * b^3 * c * d^2 + 30 * b^2 * c^2 * d^2 + 30 * b^2 * c * d^3 + 9 * b^2 * d^4 + 24 * b * c^4 * d + 48 * b * c^3 * d^2 + 42 * b * c^2 * d^3 + 12 * b * c * d^4 + 4 * c^6 + 12 * c^5 * d + 18 * c^4 * d^2 + 12 * c^3 * d^3 + 3 * c^2 * d^4
lemma qq2 (a b c d : ℂ) : cc2 a b c d (-a-b) (-c-d) = (2 : ℂ) * q2 a b c d := by
  unfold cc2 q2
  ring

lemma qq3 (a b c d : ℂ) : cc3 a b c d (-a-b) (-c-d) = (3 : ℂ) * q3 a b c d := by
  unfold cc3 q3
  ring

lemma qq4 (a b c d : ℂ) : cc4 a b c d (-a-b) (-c-d) = (1 : ℂ) * q4 a b c d := by
  unfold cc4 q4
  ring

lemma qq5 (a b c d : ℂ) : cc5 a b c d (-a-b) (-c-d) = (2 : ℂ) * q5 a b c d := by
  unfold cc5 q5
  ring

lemma qq6 (a b c d : ℂ) : cc6 a b c d (-a-b) (-c-d) = (2 : ℂ) * q6 a b c d := by
  unfold cc6 q6
  ring

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
lemma eliminate4 (a b c d : ℂ) (h2 : q2 a b c d = 0) (h3 : q3 a b c d = 0) (h4 : q4 a b c d = 0) (h5 : q5 a b c d = 0) (h6 : q6 a b c d = 0) : d = 0 := by
  have hz : d^8 = 0 := by
    unfold q2 q3 q4 q5 q6 at *
    linear_combination
      ((531423609350075038677779686435848 * a^3 * b^2 * d + 80112497459561825708572338255033 * a^3 * b * c^2 - 932979769377521940756919780419 * a^3 * b * d^2 - 862636616089334741592301933992064 * a^3 * c^3 - 130457310052629876386534026926849 * a^3 * c^2 * d - 50008838630107466072087559213117 * a^3 * c * d^2 + 207386584634670440658604678599174 * a^3 * d^3 + 3462769724660887730077063308050 * a^2 * b^4 + 681482284743533741242121846627874 * a^2 * b^3 * c + 251961320160749844703648169130658 * a^2 * b^3 * d + 70438385723280144147646152191228 * a^2 * b^2 * c^2 - 980723911113423864520735617417790 * a^2 * b^2 * c * d + 2129544076958972848843985830135761 * a^2 * b^2 * d^2 + 1272278418595289445244069331980708 * a^2 * b * c^3 - 1229441778274548574242790128282094 * a^2 * b * c^2 * d + 3670492699843735191960488243049970 * a^2 * b * c * d^2 + 1372830480625027633333322598843612 * a^2 * b * d^3 - 188004567029490301987272330039380 * a^2 * c^4 + 951146785164426848568707303874622 * a^2 * c^3 * d + 2208304876755207251865650391447008 * a^2 * c^2 * d^2 + 1519889395000023919595361722863980 * a^2 * c * d^3 + 568915648026197884372235176843374 * a^2 * d^4 + 256348455270053724187472728299388 * a * b^5 + 1249399244634087248242807376670832 * a * b^4 * c + 471067420927165843322262505117302 * a * b^4 * d - 183483090227236738479588235092741 * a * b^3 * c^2 - 2669417431416289558628963048157456 * a * b^3 * c * d - 5482983435494179837048131857079362 * a * b^2 * c^2 * d + 936477003831278387223179304542870 * a * b^2 * d^3 - 445376032019965458016866351618120 * a * b * c^4 - 1135296650278498986366309097886090 * a * b * c^3 * d - 256082339373210901055649553241614 * a * b * c^2 * d^2 + 1121181811693196784698105517859758 * a * b * c * d^3 + 671335327370306961868368541893789 * a * b * d^4 + 314144678098755327879245312394560 * a * c^5 + 1446245395817979665086729065254769 * a * c^4 * d + 3142436765553760033112252606244201 * a * c^3 * d^2 + 3632750203765321606507594820775370 * a * c^2 * d^3 + 2052001590335968900132492955062392 * a * c * d^4 + 262913288630861513382111844096068 * a * d^5 + 284070700905302195895506678799244 * b^6 - 118043816079339667618467771248496 * b^5 * c + 615074555437193897463504216896 * b^5 * d + 615923477777394774287869532359916 * b^4 * c^2 - 1335901905396695071126093825223928 * b^4 * c * d - 1111643072548091422384260874632084 * b^4 * d^2 - 2450545119005071646624493880957936 * b^3 * c^3 - 3648431291934776827142371094243140 * b^3 * c^2 * d - 2382094154620167335325130838177484 * b^3 * c * d^2 - 280631117016200656264491585380896 * b^3 * d^3 + 541917645816896337518142476906796 * b^2 * c^4 - 404171095068847621640347616880492 * b^2 * c^3 * d + 1290116956734581640023721845176076 * b^2 * c^2 * d^2 + 2867108520248799974502049538786284 * b^2 * c * d^3 + 1202978058906002936613657583361947 * b^2 * d^4 - 414067143921333414697375993060976 * b * c^5 + 896406483240111533668653613871183 * b * c^4 * d + 911620611960128284487399171498383 * b * c^3 * d^2 + 1115826233619656685163078443589738 * b * c^2 * d^3 + 875628886675258245344803867534940 * b * c * d^4 - 346505333508788815248618605039988 * b * d^5 - 44356349952020370764365958828808 * c^6 + 1178423127393660582614249142656644 * c^5 * d - 325965033188654769059859321155882 * c^4 * d^2 + 1780343764464426464434485899029940 * c^3 * d^3 + 4006708384224635792634041068291800 * c^2 * d^4 + 484161007348563710739150472772214 * c * d^5 + 132108680043690077328307199423676 * d^6) / (385717123892402528951667922297110 : ℂ)) * h2 +
      ((164544117776782163899424956733549 * a^3 * b^2 - 222510632922343013456338944277302 * a^3 * b * c - 62280166050400041778415931547311 * a^3 * c * d + 2442248233887622402143421631324839 * a^2 * b * d^2 + 3058417630208735598918639689408568 * a^2 * c^3 + 3566727985045584923044267216166336 * a^2 * c * d^2 - 173220365812560457385864353207528 * a * b^4 - 1626820354002687494102216156772146 * a * b^3 * c - 518016051885074811188783174546694 * a * b^3 * d - 2971955280103727985325481572928788 * a * b^2 * c^2 - 3313785985442439497039225912715712 * a * b^2 * c * d + 2261593245592547173804277188605090 * a * b^2 * d^2 - 1461333673192372354990041240597702 * a * b * c^3 - 7946137989034617096178626763273110 * a * b * c^2 * d - 3743560431883688686088297479307470 * a * b * c * d^2 - 2829472163968701008650702603800962 * a * b * d^3 - 53518346720877322602879230156883 * a * c^4 - 122528576735936282985154216328565 * a * c^3 * d + 1085455150255942696763812271296875 * a * c^2 * d^2 + 1325567603526049811184139523028476 * a * c * d^3 + 563833147620072978865988666715579 * a * d^4 - 471123586006215425746603252866720 * b^5 - 357371290304859398524471706177068 * b^4 * c + 205797300974920162360842008196958 * b^4 * d - 1772966700792724783418270232656165 * b^3 * c^2 - 2447725472797347800976360020433236 * b^3 * c * d + 1481292320841233067740492694379788 * b^3 * d^2 + 145977604875647774005683498763428 * b^2 * c^3 - 2779488897936121105836285959796312 * b^2 * c^2 * d + 2534075229951408732184843294235660 * b^2 * c * d^2 - 94424598258772588498645593803510 * b^2 * d^3 + 689463781312114955811265438742311 * b * c^4 + 317067002872368688249634898648791 * b * c^3 * d + 4075617673807643085605803609279699 * b * c^2 * d^2 + 4718564353696257913578794404632178 * b * c * d^3 + 2859644976968009661666706783152181 * b * d^4 + 1796859374171882104457198424183280 * c^5 + 1949582075265894859383659275453902 * c^4 * d + 7120222234454675561352568532698246 * c^3 * d^2 + 6377535942740218180080510826435198 * c^2 * d^3 + 6076422517555807434247388737466468 * c * d^4 + 1729146509512221725346503660792136 * d^5) / (385717123892402528951667922297110 : ℂ)) * h3 +
      ((-163096361447444970532409592143266 * a * b^2 * c - 158426919163304751606830776922235 * a * b^2 * d - 227987178259521528428297534946416 * a * b * c^2 - 327972504500519768089175453317549 * a * b * c * d - 21699715982964682434151701876835 * a * b * d^2 - 98485524076421642481169828896544 * a * c^3 - 238083116292484657554801639610460 * a * c^2 * d - 189563351507148221488220345368409 * a * c * d^2 - 87637762876953837794037281365356 * a * d^3 - 144730140449286388975751501158339 * b^2 * c^2 - 100527944132490243512880661378734 * b^2 * c * d + 33940076415345768527762041593962 * b^2 * d^2 + 74005831960498436769727055453120 * b * c^3 + 148537733266218882520374647577017 * b * c^2 * d + 168604026402859261849278516997753 * b * c * d^2 + 69542704698612970168659392128328 * b * d^3 + 91357491709392946261184041338653 * c^4 + 127321752057102436528832659843249 * c^3 * d + 169634370394761596105527797780009 * c^2 * d^2 + 178907108238689360553668109507292 * c * d^3 + 84536147949570817207786907624478 * d^4) / (385717123892402528951667922297110 : ℂ)) * h4 +
      ((-284042097376030732506721924409264 * a * b^2 - 116838111409726276022558351643116 * a * b * c - 394085714538737954210146932285270 * a * b * d - 489274498676502187216792456750280 * a * c^2 - 261012174157501756914688093969020 * a * c * d - 193974678924386561010791629768566 * a * d^2 - 217077032958517916726514906416010 * b^2 * c - 592431002931813459565839105967762 * b^2 * d + 68503876399971540382259058541958 * b * c^2 + 273235297762024317875658051962200 * b * c * d + 199858850973268901209062065477510 * b * d^2 - 318173864946901072667276585353240 * c^3 - 705816408109125834480192695587050 * c^2 * d - 668367913770460924543582393365404 * c * d^2 - 68938609706474952371320214327502 * d^3) / (385717123892402528951667922297110 : ℂ)) * h5 +
      ((-39832659866416189535765655891905 * a * b + 19949354551732810511358500797904 * a * c + 9254450666031845453917860916149 * a * d - 71017675226325548973876669699811 * b^2 + 29510954019834916904616942812124 * b * c - 153768638859298474365876054224 * b * d - 80268404221387853570092551631451 * c^2 - 62620306102614831522732570213961 * c * d - 40100009183625108827203501735185 * d^2) / (385717123892402528951667922297110 : ℂ)) * h6
  exact pow_eq_zero_iff (by decide) |>.mp hz

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
lemma eliminate3 (a b c : ℂ) (h2 : q2 a b c 0 = 0) (h3 : q3 a b c 0 = 0) (h4 : q4 a b c 0 = 0) (h5 : q5 a b c 0 = 0) : c = 0 := by
  have hz : c^6 = 0 := by
    unfold q2 q3 q4 q5 at *
    linear_combination
      ((1958 * a^3 * b + 576 * a^3 * c + 1482 * a^2 * b^2 + 592 * a^2 * b * c - 156 * a^2 * c^2 + 80 * a * b * c^2 - 192 * a * c^3 + 572 * b^4 - 208 * b^2 * c^2 + 572 * c^4) / (780 : ℂ)) * h2 +
      ((1265 * a^3 - 704 * a^2 * c + 32 * a * b^2 + 468 * a * b * c + 3994 * a * c^2 - 1016 * b^3 - 952 * b^2 * c + 416 * b * c^2 + 416 * c^3) / (780 : ℂ)) * h3 +
      ((-111 * a * b + 48 * a * c - 143 * b^2 + 52 * c^2) / (780 : ℂ)) * h4 +
      ((360 * a) / (780 : ℂ)) * h5
  exact pow_eq_zero_iff (by decide) |>.mp hz

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
lemma eliminate2 (a b : ℂ) (h2 : q2 a b 0 0 = 0) (h3 : q3 a b 0 0 = 0) : b = 0 := by
  have hz : b^4 = 0 := by
    unfold q2 q3 at *
    linear_combination
      ((b^2) / (1 : ℂ)) * h2 +
      ((b) / (1 : ℂ)) * h3
  exact pow_eq_zero_iff (by decide) |>.mp hz

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8000 in
lemma eliminate1 (a : ℂ) (h2 : q2 a 0 0 0 = 0) : a = 0 := by
  have hz : a^2 = 0 := by
    unfold q2 at *
    linear_combination
      ((1) / (1 : ℂ)) * h2
  exact pow_eq_zero_iff (by decide) |>.mp hz

lemma noDir (w : Fin 6 → ℂ) (e : w 0 + w 1 + w 4 = 0)
    (H : ∀ t : ℂ, Matrix.permanent (Matrix.of fun i j : Fin 6 => 1 + t * w (j-i)) = 720) : w = 0 := by
  have HH (t : ℂ) := (circ_shift (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) t).symm.trans
    ((circ_eq (fun i => 1 + t * w i)).symm.trans (H t))
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := vanishing _ _ _ _ _ _ HH
  have he : w 4 = -w 0 - w 1 := by linear_combination e
  unfold cc1 at h1
  have hf : w 5 = -w 2 - w 3 := by linear_combination h1 - e
  rewrite [he, hf, qq2] at h2
  rewrite [he, hf, qq3] at h3
  rewrite [he, hf, qq4] at h4
  rewrite [he, hf, qq5] at h5
  rewrite [he, hf, qq6] at h6
  have hq2 : q2 (w 0) (w 1) (w 2) (w 3) = 0 := by linear_combination (1/2 : ℂ) * h2
  have hq3 : q3 (w 0) (w 1) (w 2) (w 3) = 0 := by linear_combination (1/3 : ℂ) * h3
  have hq4 : q4 (w 0) (w 1) (w 2) (w 3) = 0 := by linear_combination (1 : ℂ) * h4
  have hq5 : q5 (w 0) (w 1) (w 2) (w 3) = 0 := by linear_combination (1/2 : ℂ) * h5
  have hq6 : q6 (w 0) (w 1) (w 2) (w 3) = 0 := by linear_combination (1/2 : ℂ) * h6
  have hw3 := eliminate4 (w 0) (w 1) (w 2) (w 3) hq2 hq3 hq4 hq5 hq6
  rw [hw3] at hq2 hq3 hq4 hq5 hq6
  have hw2 := eliminate3 (w 0) (w 1) (w 2) hq2 hq3 hq4 hq5
  rw [hw2] at hq2 hq3 hq4 hq5 hq6
  have hw1 := eliminate2 (w 0) (w 1) hq2 hq3
  rw [hw1] at hq2 hq3 hq4 hq5 hq6
  have hw0 := eliminate1 (w 0) hq2
  have hw4 : w 4 = 0 := by rw [he, hw0, hw1]; ring
  have hw5 : w 5 = 0 := by rw [hf, hw2, hw3]; ring
  funext i
  fin_cases i <;> first | exact hw0 | exact hw1 | exact hw2 | exact hw3 | exact hw4 | exact hw5

end PEqualNP.Outside.L_gct_224

theorem PEqualNP.Outside.L_gct_224 : ¬ (∃ f g : Fin 6 → ℂ, f ≠ 0 ∧ (∀ c : ℂ, g ≠ c • f) ∧ ∀ s r : ℂ, Matrix.permanent (Matrix.of fun (i j : Fin 6) => (1 : ℂ) + s * f (j - i) + r * g (j - i)) = 720) := by
  rintro ⟨f, g, hf, hg, H⟩
  by_cases ef : f 0 + f 1 + f 4 = 0
  · apply hf
    apply PEqualNP.Outside.L_gct_224.noDir f ef
    intro t
    simpa using H t 0
  · let z := (g 0 + g 1 + g 4) / (f 0 + f 1 + f 4)
    have hz : z * (f 0 + f 1 + f 4) = g 0 + g 1 + g 4 := div_mul_cancel₀ _ ef
    let w : Fin 6 → ℂ := fun i => g i - z * f i
    have he : w 0 + w 1 + w 4 = 0 := by
      dsimp [w]
      linear_combination -hz
    have hc (t : ℂ) : Matrix.permanent (Matrix.of fun i j : Fin 6 => 1 + t * w (j-i)) = 720 := by
      rw [← H (-t*z) t]
      congr 1
      ext i j
      simp only [Matrix.of_apply, w]
      ring
    have hw := PEqualNP.Outside.L_gct_224.noDir w he hc
    apply hg z
    funext i
    have hi := congrFun hw i
    simpa [w, sub_eq_zero, Pi.smul_apply, smul_eq_mul] using hi
