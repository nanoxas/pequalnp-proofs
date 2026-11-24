import Mathlib
import PEqualNP.Defs

-- Circuit normalization, compatibility of finite ownership, and edge geometry.
-- The conclusion is the exact assigned star-profile statement.

theorem PEqualNP.Outside.R_meta_1031_1 :
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d →
        G.Adj d a → a = c ∨ b = d) →
      ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.IsMinimalMonoCircuit n C ∧
        PEqualNP.MetaComplexity.circuitFun n C =
          PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
        ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
          C.gates[t]? = some g →
          g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
          (∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n C t u v) ∧
          ∀ u v a b : Fin n,
            G.Adj u v → PEqualNP.EdgeOwnership.Owns n C t u v →
            G.Adj a b → PEqualNP.EdgeOwnership.Owns n C t a b →
            u = a ∨ u = b ∨ v = a ∨ v = b) →
  (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
      (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate),
      C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ u v : Fin n,
        PEqualNP.EdgeOwnership.Owns n C t u v ↔
          (PEqualNP.EdgeOwnership.gateVal n C t (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
          ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate),
            C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and →
            Relation.TransGen
              (fun a b : ℕ => a < b ∧
                ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate),
                  b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs)
              (n + t') (n + t) →
            PEqualNP.EdgeOwnership.gateVal n C t' (PEqualNP.EdgeOwnership.pairInput u v) = false)) →
  (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (P : Fin n → Fin n → Prop),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ u v, P u v → G.Adj u v) →
      (∃ u v, P u v) →
      (∀ u v a b, P u v → P a b → u = a ∨ u = b ∨ v = a ∨ v = b) →
      ∃ c : Fin n, ∀ u v, P u v → u = c ∨ v = c) →
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  intro hCircuit hOwn hStar n G _ htri hfour
  obtain ⟨C, hmin, hfun, hprofile⟩ := hCircuit n G htri hfour
  have hFC : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
    intro x
    simpa [PEqualNP.MetaComplexity.circuitFun,
      PEqualNP.MetaComplexity.NestedCover.graphFun] using congrFun hfun x
  refine ⟨C, ?_, hFC, ?_, ?_⟩
  · simpa only [PEqualNP.MetaComplexity.Monotone2, Set.mem_insert_iff,
      Set.mem_singleton_iff] using hmin.1
  · intro D hD hDfun
    apply hmin.2 D
    · simpa only [PEqualNP.MetaComplexity.Monotone2, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hD
    · funext x
      exact (hDfun x).trans (hFC x).symm
  · intro t g ht hop
    obtain ⟨hne, hpair⟩ := hprofile t g ht hop
    obtain ⟨c, hc⟩ := hStar n G
      (fun u v => G.Adj u v ∧ PEqualNP.EdgeOwnership.Owns n C t u v)
      htri (fun _ _ h => h.1) hne
      (fun u v a b hu ha => hpair u v a b hu.1 hu.2 ha.1 ha.2)
    refine ⟨c, ?_, ?_⟩
    · obtain ⟨u, v, huv, ho⟩ := hne
      exact ⟨u, v, huv, (hOwn n C t g ht hop u v).mp ho⟩
    · intro u v huv ho
      exact hc u v ⟨huv, (hOwn n C t g ht hop u v).mpr ho⟩
