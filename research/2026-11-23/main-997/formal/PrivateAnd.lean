import CoupledCut
import OrCompensation

namespace PEqualNP.Research.PrivateAnd

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack
open PEqualNP.Research.OutsideActivation
open PEqualNP.Research.BoundaryActivation
open PEqualNP.Research.OrCompensation
open PEqualNP.Research.CoupledCut

theorem deficient_and_count {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (z : ℕ)
    (hG : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i : Fin m) (o : ℕ)
    (hpos : ∀ p ∈ S i, value C (fun q => decide (q = p)) o = true)
    (hneg : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      (∀ p ∈ S i, x p = false) → value C x o = false)
    (hdef : (lightAssigned C (S i) z).card < (S i).card - 1) :
    k - 1 ≤ (opPart n C GateOp.and (lightAssigned C (S i) z)).card := by
  classical
  let G := lightAssigned C (S i) z
  let A := opPart n C GateOp.and G
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have hA : ∀ w ∈ G,
      (C.gates.getD (w - n) ⟨GateOp.or, []⟩).op = GateOp.and → w ∈ A := by
    intro w hw hop
    exact Finset.mem_filter.mpr ⟨hw, hop⟩
  obtain ⟨B, hd, hBc, hBpos⟩ := coupled_cut C hG G A hgate hA (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hBlt : B.card < (S i).card := by
    have hf := Finset.card_filter_le G (· < n + C.size)
    simp only [Finset.card_singleton] at hBc
    change G.card < (S i).card - 1 at hdef
    omega
  have hclean := cleanLabel_card_le_one C S z i B hinter hd
  have hcover : (B.biUnion (cleanLabel C S z i)).card < (S i).card := by
    have hc := Finset.card_biUnion_le_card_mul B (cleanLabel C S z i) 1 hclean
    simp only [mul_one] at hc
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have hsingle : ∀ w ∈ ({o} : Finset ℕ),
      value C (fun q => decide (q = p)) w = true := by
    intro w hw
    simpa only [Finset.mem_singleton.mp hw] using hpos p hp
  obtain ⟨P, hPB, hPc, hPy, hforce⟩ :=
    hBpos (fun q => decide (q = p)) {o} (Finset.Subset.refl _) hsingle
  have hPsmall : P.card < k := by
    have hf := Finset.card_filter_le A (· < n + C.size)
    simp only [Finset.card_singleton] at hPc
    change A.card < k - 1 at hsmall
    omega
  let D := P.erase z
  have hDW : D ⊆ outsideWide C S z := by
    intro w hw
    obtain ⟨hwz, hwP⟩ := Finset.mem_erase.mp hw
    rcases missed_frontier_special C S z i B p hp hpnot w (hPB hwP) (hPy w hwP) with h | h
    · exact False.elim (hwz h)
    · exact h
  obtain ⟨U, hUc, hUS, hUactive⟩ := outside_activation_set C S z i hG D hDW
  have hUweight : (Finset.univ.filter (fun q => bit U q = true)).card < k := by
    rw [bit_weight]
    have hdP : D.card ≤ P.card := Finset.card_le_card (Finset.erase_subset z P)
    omega
  have hfalse := hneg (bit U) hUweight (bit_zero_on U (S i) hUS)
  have htrue : value C (bit U) o = true := by
    apply hforce (bit U) _ o (Finset.mem_singleton_self _)
    intro w hw
    by_cases hwz : w = z
    · rw [hwz]
      exact hz _
    · exact hUactive w (Finset.mem_erase.mpr ⟨hwz, hw⟩)
  rw [hfalse] at htrue
  contradiction

end PEqualNP.Research.PrivateAnd

#print axioms PEqualNP.Research.PrivateAnd.deficient_and_count
