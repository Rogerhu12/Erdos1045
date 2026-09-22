import RadialEnergy
import NormalizedDerivative

/-!
# The analytic part of the new exterior energy estimate

The derivative bound is proved from the positive-real criterion and then
fed into the finite-circle energy theorem. No supremum bound, mean identity,
integrability statement, boundary square root, or SC product is an input.
The geometric derivation of the positive-real criterion is still separate.
-/

namespace ExteriorReduction

open Complex Metric Set

noncomputable section

theorem normalized_derivative_le_two {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0) (hzero : D 0 = 1)
    (hdzero : deriv D 0 = 0)
    (hpos : ∀ z ∈ ball 0 1, 0 ≤ (derivativeCriterion D z).re)
    {z : ℂ} (hz : z ∈ ball 0 1) : ‖D z‖ ≤ 2 := by
  have hn := normalized_derivative_bound hD hne hzero hdzero hpos hz
  have hzlt := mem_ball_zero_iff.mp hz
  nlinarith [norm_nonneg z]

theorem criterion_circle_energy_bound {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0) (hzero : D 0 = 1)
    (hdzero : deriv D 0 = 0)
    (hpos : ∀ z ∈ ball 0 1, 0 ≤ (derivativeCriterion D z).re)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    radialMeanEnergy D r ≤ 2 * (2 + r ^ 2) * (radialMeanNorm D r - 1) := by
  have hbound (z : ℂ) (hz : z ∈ sphere 0 r) : ‖D z‖ ≤ 1 + r ^ 2 := by
    have hznorm : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
    have hzball : z ∈ ball 0 1 := mem_ball_zero_iff.mpr (hznorm.trans_lt hr1)
    simpa only [hznorm] using normalized_derivative_bound hD hne hzero hdzero hpos hzball
  have h := analytic_disk_energy_bound hD hne hzero hr0 hr1
    (show (1 : ℝ) ≤ 1 + r ^ 2 by nlinarith [sq_nonneg r]) hbound
  convert h using 1
  ring

/-- This is the finite-radius precursor of the 12*pi capacity-defect bound. -/
theorem criterion_scaled_coarse_energy {D : ℂ → ℂ}
    (hD : AnalyticOnNhd ℂ D (ball 0 1))
    (hne : ∀ z ∈ ball 0 1, D z ≠ 0) (hzero : D 0 = 1)
    (hdzero : deriv D 0 = 0)
    (hpos : ∀ z ∈ ball 0 1, 0 ≤ (derivativeCriterion D z).re)
    {r c : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2 * Real.pi * c ^ 2 * radialMeanEnergy D r ≤
      12 * Real.pi * c * (c * radialMeanNorm D r - c) := by
  have hbound (z : ℂ) (hz : z ∈ sphere 0 r) : ‖D z‖ ≤ 2 :=
    normalized_derivative_le_two hD hne hzero hdzero hpos
      (sphere_subset_ball hr1 hz)
  have h := analytic_disk_scaled_energy_bound (c := c) hD hne hzero hr0 hr1
    (show (1 : ℝ) ≤ 2 by norm_num) hbound
  convert h using 1
  ring

#print axioms criterion_circle_energy_bound
#print axioms criterion_scaled_coarse_energy

end
end ExteriorReduction
