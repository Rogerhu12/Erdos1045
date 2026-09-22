import Erdos1045.FaberCauchy
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast

/-! # Closing the classical sequence and geometric-moment inputs

Both structures are constructed from mathlib theorems. No additional
assumptions are used.
-/

namespace Erdos1045.ClosedSeries

open scoped BigOperators
noncomputable section

theorem complex_sequence_cauchy (x y : ℕ → ℂ)
    (hx : Summable (fun m => ‖x m‖ ^ 2)) (hy : Summable (fun m => ‖y m‖ ^ 2)) :
    Summable (fun m => ‖x m * y m‖) ∧
    ‖∑' m, x m * y m‖ ≤ Real.sqrt (∑' m, ‖x m‖ ^ 2) * Real.sqrt (∑' m, ‖y m‖ ^ 2) := by
  have hs : Summable (fun m => ‖x m * y m‖) := by
    apply Summable.of_nonneg_of_le (fun m => norm_nonneg _) _ ((hx.add hy).div_const 2)
    intro m
    rw [norm_mul]
    nlinarith [sq_nonneg (‖x m‖ - ‖y m‖)]
  refine ⟨hs, (norm_tsum_le_tsum_norm hs).trans ?_⟩
  apply hs.tsum_le_of_sum_le
  intro s
  simp_rw [norm_mul]
  calc
    _ ≤ Real.sqrt (∑ m ∈ s, ‖x m‖ ^ 2) * Real.sqrt (∑ m ∈ s, ‖y m‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s _ _
    _ ≤ _ := mul_le_mul
      (Real.sqrt_le_sqrt (hx.sum_le_tsum s (fun _ _ => sq_nonneg _)))
      (Real.sqrt_le_sqrt (hy.sum_le_tsum s (fun _ _ => sq_nonneg _)))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem sequenceFacts : FaberFourier.ClassicalSequenceFacts :=
  ⟨complex_sequence_cauchy⟩

theorem geometric_moment : FaberSampling.ClassicalGeometricMoment := by
  intro q hq0 hq1
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have h₂ := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hq).mul_left (2 * q)
  have h₁ := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hq).mul_left q
  have h := h₂.sub h₁
  convert h using 1 <;> try rfl
  · funext k
    rw [Nat.cast_choose_two]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    ring
  · have hd : 1 - q ≠ 0 := by linarith
    norm_num only [Nat.reduceAdd]
    field_simp
    ring

end
end Erdos1045.ClosedSeries
