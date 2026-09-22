import RadialParseval
import LaurentDerivativeSeries

/-! Finite-circle energy for the actual raw Laurent coefficients. -/

namespace ExteriorReduction

open Complex Metric Set
open FaberKernel
noncomputable section

theorem model_derivative_radial_hasSum {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m => ‖taylorCoefficients (modelDerivative q) (m + 1)‖ ^ 2 *
      r ^ (2 * (m + 1))) (radialMeanEnergy (modelDerivative q) r) := by
  have hD := modelDerivative_analytic hq hq0
  obtain ⟨hs, he⟩ := analytic_circle_parseval hD hr0 hr1
  have ht := (hasSum_nat_add_iff' 1).mpr hs.hasSum
  have hsub : closedBall (0 : ℂ) |r| ⊆ ball 0 1 := by
    rw [abs_of_nonneg hr0]
    exact closedBall_subset_ball hr1
  simp only [Finset.sum_range_one, modelDerivative_taylor_zero hq0, norm_one,
    one_pow, mul_zero, pow_zero, mul_one] at ht
  rw [← he, ← analytic_circle_variance (hD.mono hsub) (modelDerivative_zero hq0)] at ht
  exact ht

theorem raw_laurent_radial_hasSum {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun m : ℕ => (m : ℝ) ^ 2 * ‖modelLaurentCoefficient q m‖ ^ 2 *
      r ^ (2 * (m + 1))) (‖q 0‖ ^ 2 * radialMeanEnergy (modelDerivative q) r) := by
  have he (m : ℕ) :
      ‖q 0‖ ^ 2 * (‖taylorCoefficients (modelDerivative q) (m + 1)‖ ^ 2 * r ^ (2 * (m + 1))) =
        (m : ℝ) ^ 2 * ‖modelLaurentCoefficient q m‖ ^ 2 * r ^ (2 * (m + 1)) := by
    rw [modelDerivative_taylor_succ hq hq0]
    simp only [norm_div, norm_mul, norm_neg, Complex.norm_natCast, div_pow, mul_pow]
    have hn := norm_ne_zero_iff.mpr hq0
    field_simp
  convert! (model_derivative_radial_hasSum hq hq0 hr0 hr1).mul_left (‖q 0‖ ^ 2) using 1
  funext m
  exact (he m).symm

theorem raw_laurent_radial_energy {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) {c : ℝ} (hc : 0 < c) (hq0 : q 0 = (c : ℂ))
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2 * Real.pi * c ^ 2 * radialMeanEnergy (modelDerivative q) r =
      2 * Real.pi * ∑' m : ℕ, (m : ℝ) ^ 2 * ‖modelLaurentCoefficient q m‖ ^ 2 *
        r ^ (2 * (m + 1)) := by
  have hqne : q 0 ≠ 0 := hq0 ▸ Complex.ofReal_ne_zero.mpr hc.ne'
  have he := (raw_laurent_radial_hasSum hq hqne hr0 hr1).tsum_eq
  rw [hq0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at he
  rw [he]
  ring

#print axioms raw_laurent_radial_hasSum
#print axioms raw_laurent_radial_energy

end
end ExteriorReduction
