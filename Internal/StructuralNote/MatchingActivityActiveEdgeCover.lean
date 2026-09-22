import StructuralNote.MatchingActivityActiveConstraintDifferentials
import StructuralNote.FixedSchurSimpleGraph

/-! The `m` matching edges and the `m` selected crossing edges are exactly
the undirected edges of the completed word graph. -/

namespace StructuralNote.MatchingActivityActiveEdgeCover

open Erdos1045 Erdos1045.EventualExact Configuration FiniteFourierLift FourierMultiplier
open SchurLift FiniteBox CommonClosureEnergy
open FixedSchurOffsetGeometry FixedSchurChartGeometry FixedSchurSimpleGraph
open MatchingActivityActiveConstraintDifferentials

noncomputable section

def CoveredByActiveEdges {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    (p q : Fin (2 * m)) : Prop :=
  (∃ i : Fin m,
    (p = matchingFirst i ∧ q = matchingSecond hm i) ∨
      (q = matchingFirst i ∧ p = matchingSecond hm i)) ∨
  ∃ i : Fin m,
    (p = selectedFirst hm s i ∧ q = selectedSecond hm s i) ∨
      (q = selectedFirst hm s i ∧ p = selectedSecond hm s i)

theorem advance_halfTurn_next {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    cyclicAdvance (halfTurn (by omega) (CommonClosureEnergy.halfIndex i)) (m + 1) =
      successor (by omega) (CommonClosureEnergy.halfIndex i) := by
  apply Fin.ext
  simp only [cyclicAdvance, halfTurn, CommonClosureEnergy.halfIndex, successor,
    Nat.mod_add_mod]
  have hi : i.val + m + (m + 1) = i.val + 1 + 2 * m := by omega
  rw [hi, Nat.add_mod_right]

theorem half_decomposition_active {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    ∃ i : Fin m, j = matchingFirst i ∨ j = matchingSecond hm i := by
  by_cases hj : j.val < m
  · exact ⟨⟨j.val, hj⟩, Or.inl (Fin.ext rfl)⟩
  · let i : Fin m := ⟨j.val - m, by omega⟩
    refine ⟨i, Or.inr ?_⟩
    apply Fin.ext
    simp only [matchingSecond, CommonClosureEnergy.halfIndex,
      halfTurn, i]
    rw [Nat.sub_add_cancel (by omega : m ≤ j.val), Nat.mod_eq_of_lt j.isLt]

theorem wordEdge_covered {m : ℕ} (hm : 2 ≤ m) (σ : Fin (2 * m) → ℝ)
    (hσ : Antiperiodic (by omega) σ) (s : Fin m → ℝ)
    (hs : ∀ i, s i = σ (CommonClosureEnergy.halfIndex i)) {p q : Fin (2 * m)}
    (hEdge : WordEdge σ p q) : CoveredByActiveEdges (by omega) s p q := by
  rw [wordEdge_generated hm] at hEdge
  rcases hEdge with hmatch | hnext | hprev
  · obtain ⟨i, hq | hq⟩ := half_decomposition_active (by omega : 0 < m) q
    · left
      refine ⟨i, Or.inr ⟨hq, ?_⟩⟩
      rw [hmatch, hq]
      rfl
    · left
      refine ⟨i, Or.inl ⟨?_, hq⟩⟩
      rw [hmatch, hq]
      unfold matchingSecond
      exact halfTurn_involutive (by omega) (matchingFirst i)
  · obtain ⟨hpq, hqsign⟩ := hnext
    obtain ⟨i, hq | hq⟩ := half_decomposition_active (by omega : 0 < m) q
    · have hisign : s i = -1 := by
        rw [hs i]
        rw [hq] at hqsign
        simpa only [matchingFirst] using hqsign
      right
      refine ⟨i, Or.inr ⟨?_, ?_⟩⟩
      · rw [hq]
        unfold selectedFirst
        rw [hisign, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
        rfl
      · rw [hpq, hq, FixedSchurOffsetGeometry.advance_next]
        unfold selectedSecond
        rw [hisign, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
        rfl
    · have hqsign' : σ (matchingSecond (by omega) i) = -1 := by
        rw [hq] at hqsign
        exact hqsign
      have hh := hσ (matchingFirst i)
      change σ (matchingSecond (by omega) i) = -σ (matchingFirst i) at hh
      have hisign : s i = 1 := by
        rw [hs i]
        change σ (matchingFirst i) = 1
        rw [hqsign'] at hh
        linarith
      right
      refine ⟨i, Or.inl ⟨?_, ?_⟩⟩
      · rw [hpq, hq]
        simp only [selectedFirst, hisign, if_pos]
        exact advance_halfTurn_next hm i
      · rw [hq]
        simp [selectedSecond, hisign, matchingSecond]
  · obtain ⟨hqp, hpsign⟩ := hprev
    obtain ⟨i, hp | hp⟩ := half_decomposition_active (by omega : 0 < m) p
    · have hisign : s i = -1 := by
        rw [hs i]
        rw [hp] at hpsign
        simpa only [matchingFirst] using hpsign
      right
      refine ⟨i, Or.inl ⟨?_, ?_⟩⟩
      · rw [hp]
        unfold selectedFirst
        rw [hisign, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
        rfl
      · rw [hqp, hp, FixedSchurOffsetGeometry.advance_next]
        unfold selectedSecond
        rw [hisign, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
        rfl
    · have hpsign' : σ (matchingSecond (by omega) i) = -1 := by
        rw [hp] at hpsign
        exact hpsign
      have hh := hσ (matchingFirst i)
      change σ (matchingSecond (by omega) i) = -σ (matchingFirst i) at hh
      have hisign : s i = 1 := by
        rw [hs i]
        change σ (matchingFirst i) = 1
        rw [hpsign'] at hh
        linarith
      right
      refine ⟨i, Or.inr ⟨?_, ?_⟩⟩
      · rw [hqp, hp]
        simp only [selectedFirst, hisign, if_pos]
        exact advance_halfTurn_next hm i
      · rw [hp]
        simp [selectedSecond, hisign, matchingSecond]

theorem covered_edgeConstraint {m : ℕ} (hm : 0 < m) (s : Fin m → ℝ)
    {p q : Fin (2 * m)} (h : CoveredByActiveEdges hm s p q)
    (x : Points (2 * m)) :
    (∃ i, edgeConstraint x p q = matchingConstraint hm x i) ∨
      ∃ i, edgeConstraint x p q = selectedConstraint hm s x i := by
  rcases h with ⟨i, h | h⟩ | ⟨i, h | h⟩
  · exact Or.inl ⟨i, by rw [h.1, h.2]; rfl⟩
  · exact Or.inl ⟨i, by rw [h.1, h.2]; unfold matchingConstraint edgeConstraint; rw [norm_sub_rev]⟩
  · exact Or.inr ⟨i, by rw [h.1, h.2]; rfl⟩
  · exact Or.inr ⟨i, by rw [h.1, h.2]; unfold selectedConstraint edgeConstraint; rw [norm_sub_rev]⟩

end
end StructuralNote.MatchingActivityActiveEdgeCover
