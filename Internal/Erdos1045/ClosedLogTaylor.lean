import Erdos1045.LocalNonlinear
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Erdos1045.LocalNonlinear

open scoped BigOperators
noncomputable section

/-- The scalar logarithm remainder is discharged using mathlib's Taylor bound. -/
theorem scalarLogTaylor : ScalarLogTaylor := by
  intro z hz
  have hz1 : ‖z‖ < 1 := by linarith
  have ht := Complex.norm_log_sub_logTaylor_le 2 hz1
  have hp : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
    simp [Complex.logTaylor, Finset.sum_range_succ]
    ring
  rw [hp] at ht
  have hre := (Complex.abs_re_le_norm (Complex.log (1 + z) - (z - z ^ 2 / 2))).trans ht
  have hscalar : (Complex.log (1 + z) - (z - z ^ 2 / 2)).re =
      Real.log ‖1 + z‖ - z.re + (z ^ 2).re / 2 := by
    simp [Complex.log_re, Complex.div_ofNat_re]
    ring
  rw [hscalar] at hre
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (show (1 / 2 : ℝ) ≤ 1 - ‖z‖ by linarith)
    simpa using h
  have hmul := mul_le_mul_of_nonneg_left hinv (pow_nonneg (norm_nonneg z) 3)
  have heq : 2 * Real.log ‖1 + z‖ - 2 * z.re + (z ^ 2).re =
      2 * (Real.log ‖1 + z‖ - z.re + (z ^ 2).re / 2) := by ring
  rw [heq, abs_mul]
  norm_num at hre ⊢
  nlinarith [pow_nonneg (norm_nonneg z) 3]

end
end Erdos1045.LocalNonlinear
