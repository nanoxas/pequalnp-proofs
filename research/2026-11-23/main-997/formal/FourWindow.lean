import TriplePacking
import DoubleExcess

/-
Combination of the independently checked triple packing and outsider-cut
criteria. This verifies the L-meta-997 inequality when n <= 4*|Y|+1.
-/

namespace PEqualNP.Research.FourWindow

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

theorem one_not_refund_bound_four_window {n m : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ) (t : ℕ) (Y : Finset (Fin n))
    (hn : n ≤ 4 * Y.card + 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < Y.card → value C x (n + t) = true)
    (hfalse : value C (bit Y) (n + t) = false) :
    (∑ i : Fin m, if Disjoint (S i) Y then (S i).card else min Y.card (S i).card) ≤
      C.size + (refundGates C S Y).card + m := by
  by_cases hk : 2 ≤ Y.card
  · apply PEqualNP.Research.DoubleExcess.one_not_refund_bound_double_excess
      C S out t Y hk hgate hnot hinter hout hbelow hfalse
    apply PEqualNP.Research.TriplePacking.heavy_excess_bound_twice S Y Y.card hinter
    have hp := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin n)) Y
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at hp
    omega
  · have h := PEqualNP.Research.SmallWindow.one_not_small_window_bound
      C S out t Y (by omega) hgate hnot hinter hout hbelow hfalse
    omega

end PEqualNP.Research.FourWindow

#print axioms PEqualNP.Research.FourWindow.one_not_refund_bound_four_window
