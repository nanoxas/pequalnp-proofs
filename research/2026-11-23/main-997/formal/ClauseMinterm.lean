import NotWindow

/-
Research extension of the accepted L-meta-986 mandatory-clause bound.
The owned/countOne, mask, and incidence helpers are copied or adapted from
that accepted proof (Apache-2.0). The new disjoint count adds the checked
empty-singleton-support prefix AND budget from MintermSlack. This module
proves a conditional clause bound, not the unrestricted L-meta-997 theorem.
-/

namespace PEqualNP.Research.ClauseMinterm

open PEqualNP.CircuitLowerBounds
open PEqualNP.Research.MintermSlack

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def owned {n} (C : Circuit) (z : ℕ) (P S : Finset (Fin n)) : Finset ℕ :=
  ((Finset.Ico n (n+C.size)).erase z).filter fun w => support C w ∩ P ⊆ S ∧ 2 ≤ (support C w ∩ P).card

theorem countOne {n} (C : Circuit) (z o : ℕ) (P S : Finset (Fin n)) (hg : good C)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hpos : ∀ p ∈ S ∩ P, value C (fun v => decide (v = p)) o = true)
    (hneg : value C (bit (P \ S)) o = false) :
    (S ∩ P).card - 1 ≤ (owned C z P S).card := by
  classical
  let G := owned C z P S
  have hgate (w) (hw : w ∈ G) : n ≤ w ∧ w < n+C.size :=
    Finset.mem_Ico.mp (Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).2
  obtain ⟨B, hd, hc, hcut⟩ := cut C hg G hgate (n+C.size) {o} (fun w _ hw => (hgate w hw).2)
  let y := bit (P \ S)
  let F := B.filter fun w => value C y w = false
  have small (w) (hw : w ∈ F) : (support C w ∩ P).card ≤ 1 := by
    have hb := (Finset.mem_filter.mp hw).1
    have hv := (Finset.mem_filter.mp hw).2
    have hs : support C w ∩ P ⊆ S := by
      intro p hp
      by_contra h
      have hpt := (mem_support C w p).mp (Finset.mem_inter.mp hp).1
      have hmono := value_mono C hg (fun q => decide (q = p)) y (by
        intro q he
        have eq : q = p := of_decide_eq_true he
        subst q
        simp [y,bit,(Finset.mem_inter.mp hp).2,h]) w hpt
      simp [hv] at hmono
    by_contra! hlarge
    have hlt := Finset.card_le_card (Finset.inter_subset_left (s₂ := P) (s₁ := support C w))
    have hne : w ≠ z := by rintro rfl; simp [hz y] at hv
    exact Finset.disjoint_left.mp hd hb (Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hne,Finset.mem_Ico.mpr (support_gate C w (by omega))⟩,hs,by omega⟩)
  have covered : S ∩ P ⊆ F.biUnion (fun w => support C w ∩ P) := by
    intro p hp
    by_contra hn
    have hbad : value C y o = true := by
      apply hcut _ y _ o (Finset.mem_singleton_self _) (hpos p hp)
      intro w hw hv
      by_contra! he
      exact hn (Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨hw,Bool.eq_false_iff.mpr he⟩,
        Finset.mem_inter.mpr ⟨(mem_support C w p).mpr hv,(Finset.mem_inter.mp hp).2⟩⟩)
    rw [hneg] at hbad
    contradiction
  have h1 := Finset.card_le_card covered
  have h2 := Finset.card_biUnion_le_card_mul F (fun w => support C w ∩ P) 1 small
  have h3 := Finset.card_filter_le B (fun w => value C y w = false)
  change F.card ≤ B.card at h3
  have h4 := Finset.card_filter_le G (fun w => w < n+C.size)
  simp only [Finset.card_singleton] at hc
  change _ ≤ G.card
  omega



lemma sum_card_inter_eq {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ s : Fin m, (S s ∩ U).card
      = ∑ u ∈ U, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  have h1 : ∀ s : Fin m, (S s ∩ U).card = ∑ u ∈ U, if u ∈ S s then 1 else 0 := by
    intro s
    rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
  have h2 : ∀ u : Fin n, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card
      = ∑ s : Fin m, if u ∈ S s then 1 else 0 := by
    intro u
    rw [Finset.card_filter]
  simp only [h1, h2]
  exact Finset.sum_comm

lemma sum_pred_le_sdiff {n m : ℕ} (S : Fin m → Finset (Fin n)) (U : Finset (Fin n)) :
    ∑ s : Fin m, ((S s).card - 1)
      ≤ ∑ s : Fin m, ((S s \ U).card - 1)
        + ∑ u ∈ U, (Finset.univ.filter (fun c : Fin m => u ∈ S c)).card := by
  rw [← sum_card_inter_eq, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun s _ => ?_
  have h := Finset.card_sdiff_add_card_inter (S s) U
  omega

/-- Empty and singleton targets need no deletion-incidence payment. -/
lemma sum_pred_le_sdiff_large {n m : ℕ} (S : Fin m → Finset (Fin n))
    (U : Finset (Fin n)) :
    (∑ i : Fin m, ((S i).card - 1)) ≤
      (∑ i : Fin m, ((S i \ U).card - 1)) +
      ∑ p ∈ U, (Finset.univ.filter (fun i : Fin m => p ∈ S i ∧ 2 ≤ (S i).card)).card := by
  classical
  have h1 (i : Fin m) :
      (if 2 ≤ (S i).card then (S i ∩ U).card else 0) =
        ∑ p ∈ U, if p ∈ S i ∧ 2 ≤ (S i).card then 1 else 0 := by
    by_cases hi : 2 ≤ (S i).card
    · simp only [hi, ite_true, and_true]
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    · simp [hi]
  have h2 (p : Fin n) :
      (Finset.univ.filter (fun i : Fin m => p ∈ S i ∧ 2 ≤ (S i).card)).card =
        ∑ i : Fin m, if p ∈ S i ∧ 2 ≤ (S i).card then 1 else 0 := by
    rw [Finset.card_filter]
  have heq : (∑ i : Fin m, if 2 ≤ (S i).card then (S i ∩ U).card else 0) =
      ∑ p ∈ U, (Finset.univ.filter (fun i : Fin m => p ∈ S i ∧ 2 ≤ (S i).card)).card := by
    simp only [h1, h2]
    exact Finset.sum_comm
  rw [← heq, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : 2 ≤ (S i).card
  · rw [ite_eq_left hi]
    have h := Finset.card_sdiff_add_card_inter (S i) U
    omega
  · rw [ite_eq_right hi]
    omega

lemma sdiff_erase_of_notMem {n : ℕ} (X T : Finset (Fin n)) (t0 : Fin n) (h : t0 ∉ X) :
    X \ T.erase t0 = X \ T := by
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro ⟨ha, hn⟩
    exact ⟨ha, fun hT => hn ⟨fun e => h (e ▸ ha), hT⟩⟩
  · rintro ⟨ha, hn⟩
    exact ⟨ha, fun hT => hn hT.2⟩

def keep {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) : Finset (Fin n) :=
  if t0 ∈ S then Finset.univ \ (T.erase t0) else Finset.univ \ T

lemma inter_keep {n : ℕ} (S T : Finset (Fin n)) (t0 : Fin n) :
    S ∩ keep S T t0 = S \ T.erase t0 := by
  unfold keep
  split_ifs with h
  · ext a
    simp
  · rw [sdiff_erase_of_notMem S T t0 h]
    ext a
    simp

lemma repl_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

lemma replC_ge {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (x : Fin n → Bool) (w : ℕ) :
    value ⟨gates, o⟩ x w = true → value (replC gates i0.val) x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact id
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · intro _
        rw [hne]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        have hop : (gates[w - n]'(by omega)).op = GateOp.and ∨
            (gates[w - n]'(by omega)).op = GateOp.or := by
          rcases (hgate (gates[w - n]'(by omega)) (List.getElem_mem _)).1 with hop | hop | hop
          · exact Or.inl hop
          · exact Or.inr hop
          · have := congrArg Fin.val (hnot ⟨w - n, by omega⟩ hop)
            simp only at this
            omega
        apply repl_eval_mono _ hop
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · intro h
      rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega)] at h
      exact absurd h (by simp)


/-- The mandatory-clause count gains the complete empty-support minterm
budget. No lower bound on the sizes of the target sets is needed. -/
theorem clause_minterm_bound {n m k : ℕ} (C : Circuit)
    (S : Fin m → Finset (Fin n)) (out : Fin m → ℕ)
    (T : Finset (Fin n)) (t0 : Fin n) (u z : ℕ) (y : Fin n → Bool)
    (hG : good C)
    (hz : ∀ x : Fin n → Bool, value C x z = true)
    (hzgate : z ∈ Finset.Ico n (n + C.size))
    (huz : u < z)
    (hy : value C y u = true)
    (hmin : ∀ x : Fin n → Bool, value C x u = true →
      k ≤ (Finset.univ.filter (fun p : Fin n => x p = true)).card)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hmask : ∀ (i : Fin m) (x : Fin n → Bool),
      (∀ p, x p = true → p ∈ keep (S i) T t0) →
      value C x (out i) = decide (∃ p ∈ S i, x p = true)) :
    k + ∑ i : Fin m, ((S i).card - 1) ≤
      C.size + ∑ p ∈ T.erase t0, (Finset.univ.filter (fun i : Fin m => p ∈ S i ∧ 2 ≤ (S i).card)).card := by
  classical
  let P := fun i => keep (S i) T t0
  let G := fun i => owned C z (P i) (S i)
  let L := Finset.univ.biUnion G
  let A := (branches C y).filter (· ≤ u)
  let R := Finset.Ico n (n + C.size)
  have smallP (i) : (Finset.univ \ T) ⊆ P i := by
    intro p hp
    have hnt := (Finset.mem_sdiff.mp hp).2
    simp [P,keep]
    split <;> simp_all
  have comp (i j) : P i ⊆ P j ∨ P j ⊆ P i := by
    by_cases hi : t0 ∈ S i
    · by_cases hj : t0 ∈ S j
      · exact Or.inl (by simp [P,keep,hi,hj])
      · exact Or.inr (by simpa [P,keep,hj] using smallP i)
    · exact Or.inl (by simpa [P,keep,hi] using smallP j)
  have noCommon (i j) (hij : i ≠ j) (hp : P i ⊆ P j) (w)
      (hi : w ∈ G i) (hj : w ∈ G j) : False := by
    have ai := (Finset.mem_filter.mp hi).2
    have aj := (Finset.mem_filter.mp hj).2
    have inc : support (n := n) C w ∩ P i ⊆ S i ∩ S j := by
      intro p hp'
      exact Finset.mem_inter.mpr ⟨ai.1 hp', aj.1 (Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hp').1, hp (Finset.mem_inter.mp hp').2⟩)⟩
    exact (by omega : ¬ 2 ≤ 1)
      (ai.2.trans ((Finset.card_le_card inc).trans (hinter i j hij)))
  have dis : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    rcases comp i j with h | h
    · exact noCommon i j hij h w hi hj
    · exact noCommon j i hij.symm h w hj hi
  have hcount (i : Fin m) : (S i \ T.erase t0).card - 1 ≤ (G i).card := by
    rw [← inter_keep]
    apply countOne C z (out i) (P i) (S i) hG hz
    · intro p hp
      rw [hmask i _ (fun v hv => (of_decide_eq_true hv : v = p) ▸
        (Finset.mem_inter.mp hp).2)]
      exact decide_eq_true ⟨p, (Finset.mem_inter.mp hp).1, by simp⟩
    · have supp (v : Fin n) (hv : bit (P i \ S i) v = true) : v ∈ P i :=
        (Finset.mem_sdiff.mp (show v ∈ P i \ S i from of_decide_eq_true hv)).1
      rw [hmask i (bit (P i \ S i)) supp]
      apply decide_eq_false
      rintro ⟨p, hp, hb⟩
      exact (Finset.mem_sdiff.mp (show p ∈ P i \ S i from of_decide_eq_true hb)).2 hp
  have hL : L ⊆ R.erase z := by
    intro w hw
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp hi).1
  have hA : A ⊆ R.erase z := by
    intro w hw
    obtain ⟨hwa, hwu⟩ := Finset.mem_filter.mp hw
    have hgate := (Finset.mem_filter.mp hwa).1
    exact Finset.mem_erase.mpr ⟨by omega, hgate⟩
  have hLA : Disjoint L A := by
    refine Finset.disjoint_left.mpr fun w hwL hwA => ?_
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hwL
    have hwide := (Finset.mem_filter.mp hwi).2.2
    obtain ⟨hwa, _⟩ := Finset.mem_filter.mp hwA
    have hempty := (Finset.mem_filter.mp hwa).2.2.1
    simp [hempty] at hwide
  have hcards : L.card + A.card ≤ (R.erase z).card := by
    rw [← Finset.card_union_of_disjoint hLA]
    exact Finset.card_le_card (Finset.union_subset hL hA)
  have hremove : (R.erase z).card + 1 = C.size := by
    have h := Finset.card_erase_add_one hzgate
    simpa [R] using h
  have hsum : (∑ i : Fin m, ((S i \ T.erase t0).card - 1)) ≤ L.card := by
    calc
      _ ≤ ∑ i : Fin m, (G i).card := Finset.sum_le_sum (fun i _ => hcount i)
      _ = L.card := (Finset.card_biUnion dis).symm
  have hbranch := minterm_bound C hG y u k hy hmin
  change k ≤ A.card + 1 at hbranch
  have hcost := sum_pred_le_sdiff_large S (T.erase t0)
  omega

/-- Actual-circuit version with an explicit unique NOT and mandatory input
clause. The threshold window supplies the additional k-1 prefix branches. -/
theorem one_not_clause_window_bound_explicit {n m k : ℕ}
    (gates : List Gate) (origOut : ℕ) (S : Fin m → Finset (Fin n))
    (out : Fin m → ℕ) (i0 : Fin gates.length) (u : ℕ) (y : Fin n → Bool)
    (T : Finset (Fin n)) (t0 : Fin n)
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0)
    (hop : (gates.get i0).op = GateOp.not)
    (hhead : (gates.get i0).inputs.head? = some u)
    (hlt : u < n + i0.val)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value ⟨gates, origOut⟩ x (out i) = decide (∃ p ∈ S i, x p = true))
    (hbelow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k →
      value ⟨gates, origOut⟩ x (n + i0.val) = true)
    (hfalse : value ⟨gates, origOut⟩ y (n + i0.val) = false)
    (hT : ∀ x : Fin n → Bool, (∀ p ∈ T, x p = false) →
      value ⟨gates, origOut⟩ x u = false)
    (ht0 : t0 ∈ T) :
    k + ∑ i : Fin m, ((S i).card - 1) ≤
      gates.length + ∑ p ∈ T.erase t0,
        (Finset.univ.filter (fun i : Fin m => p ∈ S i ∧ 2 ≤ (S i).card)).card := by
  classical
  let D := replC gates i0.val
  have hG := replC_gates gates i0 hgate hnot
  have hy : value D y u = true := by
    rw [replC_prefix_eq gates i0 origOut y u hlt]
    have h := hfalse
    rw [orig_not_value gates i0 origOut u hop hhead hlt y] at h
    simpa using h
  have hmin : ∀ x : Fin n → Bool, value D x u = true →
      k ≤ (Finset.univ.filter (fun p => x p = true)).card := by
    intro x hx
    by_contra! hsmall
    have hz := hbelow x hsmall
    have hu : value ⟨gates, origOut⟩ x u = true := by
      rw [← replC_prefix_eq gates i0 origOut x u hlt]
      exact hx
    rw [orig_not_value gates i0 origOut u hop hhead hlt x, hu] at hz
    contradiction
  have hmask : ∀ (i : Fin m) (x : Fin n → Bool),
      (∀ p, x p = true → p ∈ keep (S i) T t0) →
      value D x (out i) = decide (∃ p ∈ S i, x p = true) := by
    intro i x hx
    by_cases ht : x t0 = false
    · have hzero : ∀ p ∈ T, x p = false := by
        intro p hp
        by_cases he : p = t0
        · simpa only [he] using ht
        · apply Bool.eq_false_iff.mpr
          intro hv
          have hin := hx p hv
          unfold keep at hin
          split_ifs at hin with hi
          · exact (Finset.mem_sdiff.mp hin).2 (Finset.mem_erase.mpr ⟨he, hp⟩)
          · exact (Finset.mem_sdiff.mp hin).2 hp
      have hz : value ⟨gates, origOut⟩ x (n + i0.val) = true := by
        rw [orig_not_value gates i0 origOut u hop hhead hlt x, hT x hzero]
        rfl
      rw [replC_eq gates i0 origOut x hz (out i)]
      exact hout i x
    · have htrue : x t0 = true := by simpa using ht
      have hin := hx t0 htrue
      have htS : t0 ∈ S i := by
        by_contra hn
        simp only [keep, ite_eq_right hn] at hin
        exact (Finset.mem_sdiff.mp hin).2 ht0
      have houttrue : decide (∃ p ∈ S i, x p = true) = true :=
        decide_eq_true ⟨t0, htS, htrue⟩
      rw [houttrue]
      exact replC_ge gates i0 origOut hgate hnot x (out i) ((hout i x).trans houttrue)
  have hzgate : n + i0.val ∈ Finset.Ico n (n + D.size) := by
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · change n + i0.val < n + (replC gates i0.val).size
      rw [replC_size]
      exact Nat.add_lt_add_left i0.isLt n
  have h := clause_minterm_bound D S out T t0 u (n + i0.val) y hG
    (replC_true gates i0) hzgate hlt hy hmin hinter hmask
  simpa only [D, replC_size] using h

end PEqualNP.Research.ClauseMinterm

#print axioms PEqualNP.Research.ClauseMinterm.clause_minterm_bound
#print axioms PEqualNP.Research.ClauseMinterm.one_not_clause_window_bound_explicit
