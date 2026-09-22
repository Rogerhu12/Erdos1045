import StructuralNote.FixedSchurBalancedDegrees
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Standard simple-graph realization of the selected diameter relation. -/

namespace StructuralNote.FixedSchurSimpleGraph

open Erdos1045.EventualExact FiniteBox FourierMultiplier SchurLift
open FixedSchurOffsetGeometry FixedSchurChartGeometry FixedSchurWordDegrees
open FixedSchurWordConnected FixedSchurBalancedDegrees

noncomputable section

theorem advance_full {m : ℕ} (j : Fin (2 * m)) : cyclicAdvance j (2 * m) = j := by
  apply Fin.ext
  simp only [cyclicAdvance, Nat.add_mod_right, Nat.mod_eq_of_lt j.isLt]

theorem advance_reverse {m : ℕ} (j : Fin (2 * m)) {a b : ℕ}
    (hab : a + b = 2 * m) : cyclicAdvance (cyclicAdvance j a) b = j := by
  rw [advance_add, hab, advance_full]

theorem wordEdge_generated {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ)
    (i j : Fin (2 * m)) : WordEdge σ i j ↔
      i = halfTurn (by omega) j ∨
      (i = cyclicAdvance j (m + 1) ∧ σ j = -1) ∨
      (j = cyclicAdvance i (m + 1) ∧ σ i = -1) := by
  have he (r : ℕ) (hr : r < 2 * m) :
      cyclicForwardDistance j i = r ↔ i = cyclicAdvance j r := by
    constructor
    · intro h
      rw [← h, CommonFiberNonlocalFeasibility.cyclicAdvance_forwardDistance]
    · rintro rfl
      exact cyclicForwardDistance_advance j hr
  unfold WordEdge OffsetEdge
  constructor
  · rintro (h | ⟨h, hs⟩ | ⟨h, hs⟩)
    · exact Or.inl ((he m (by omega)).1 h)
    · exact Or.inr (Or.inl ⟨(he (m + 1) (by omega)).1 h, hs⟩)
    · have hi := (he (m - 1) (by omega)).1 h
      refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hi, advance_reverse j (by omega)]
      · rwa [CommonFiberNonlocalFeasibility.cyclicAdvance_forwardDistance] at hs
  · rintro (h | ⟨h, hs⟩ | ⟨h, hs⟩)
    · exact Or.inl ((he m (by omega)).2 h)
    · exact Or.inr (Or.inl ⟨(he (m + 1) (by omega)).2 h, hs⟩)
    · have hi : i = cyclicAdvance j (m - 1) := by
        rw [h, advance_reverse i (by omega)]
      refine Or.inr (Or.inr ⟨(he (m - 1) (by omega)).2 hi, ?_⟩)
      rwa [CommonFiberNonlocalFeasibility.cyclicAdvance_forwardDistance]

theorem wordEdge_symmetric {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ) :
    ∀ ⦃i j⦄, WordEdge σ i j → WordEdge σ j i := by
  intro i j h
  rw [wordEdge_generated hm] at h ⊢
  rcases h with h | h | h
  · left
    rw [h, halfTurn_involutive (by omega) j]
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

theorem wordEdge_irreflexive {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ) :
    ∀ j, ¬WordEdge σ j j := by
  intro j
  simp only [WordEdge, cyclicForwardDistance_self, OffsetEdge]
  omega

def graph {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ) : SimpleGraph (Fin (2 * m)) where
  Adj i j := WordEdge σ j i
  symm := ⟨by
    intro i j h
    exact wordEdge_symmetric hm σ h⟩
  loopless := ⟨by
    intro j
    exact wordEdge_irreflexive hm σ j⟩

instance graph_decidable {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ) :
    DecidableRel (graph hm σ).Adj := Classical.decRel _

theorem graph_neighborFinset {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ)
    (j : Fin (2 * m)) : (graph hm σ).neighborFinset j = neighbors σ j := by
  ext i
  simp only [SimpleGraph.mem_neighborFinset, neighbors, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rfl

theorem graph_degree {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ)
    (j : Fin (2 * m)) : (graph hm σ).degree j = (neighbors σ j).card := by
  rw [SimpleGraph.degree, graph_neighborFinset]

theorem graph_preconnected {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m)) :
    (graph hm (patternSign s)).Preconnected := by
  intro i j
  rw [SimpleGraph.reachable_iff_reflTransGen]
  exact word_connected hm s i j

theorem graph_connected {m : ℕ} (hm : 2 ≤ m) (s : SignPattern (by omega : 0 < m)) :
    (graph hm (patternSign s)).Connected := by
  let : Nonempty (Fin (2 * m)) := ⟨⟨0, by omega⟩⟩
  exact ⟨graph_preconnected hm s⟩

/-- Deleting all leaves preserves the connectivity of the diameter graph. -/
theorem nonleaf_graph_preconnected {m : ℕ} (hm : 2 ≤ m)
    (s : SignPattern (by omega : 0 < m)) :
    ((graph hm (patternSign s)).induce
      {j | (neighbors (patternSign s) j).card ≠ 1}).Preconnected := by
  apply (graph_preconnected hm s).induce_of_degree_eq_one
  intro j hj
  have hd : (neighbors (patternSign s) j).card = 1 := by simpa only [Set.mem_ofPred_eq, not_not] using hj
  have hs : ((graph hm (patternSign s)).neighborFinset j).card ≤ 1 := by
    rw [graph_neighborFinset, hd]
  have hsub := Finset.card_le_one.mp hs
  intro a ha b hb
  apply hsub
  · change (graph hm (patternSign s)).Adj j a at ha
    simpa only [SimpleGraph.mem_neighborFinset] using ha
  · change (graph hm (patternSign s)).Adj j b at hb
    simpa only [SimpleGraph.mem_neighborFinset] using hb

end
end StructuralNote.FixedSchurSimpleGraph
