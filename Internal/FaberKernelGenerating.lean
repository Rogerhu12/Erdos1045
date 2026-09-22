import LaurentKernelSeries
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Faber generating identity on the entire unit disk

Local coefficient identification is combined with Taylor's theorem on a disk.
Absolute convergence follows without a positive-real-part assumption.
-/

namespace ExteriorReduction.FaberKernel

open Complex Metric Filter
open scoped Topology

noncomputable section

/-- Canonical Taylor coefficients represent a holomorphic function everywhere
in the unit disk, not only in an unspecified neighborhood of the center. -/
theorem canonical_taylor_hasSum {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    HasSum (fun n => taylorCoefficients q n * z ^ n) (q z) := by
  simpa only [taylorCoefficients, sub_zero, smul_eq_mul, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using Complex.hasSum_taylorSeries_on_ball hq hz

theorem canonical_taylor_norm_summable {q : ℂ → ℂ}
    (hq : DifferentiableOn ℂ q (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    Summable (fun n => ‖taylorCoefficients q n * z ^ n‖) :=
  (canonical_taylor_hasSum hq hz).summable.norm

theorem laurent_kernel_analytic {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0) :
    AnalyticOnNhd ℂ
      (fun z => derivativeNumerator q z / (q z + (A - x) * z)) (ball 0 1) :=
  (derivativeNumerator_analytic hq).div
    (hq.add (analyticOnNhd_const.mul analyticOnNhd_id)) hne

/-- Coefficients of the genuine holomorphic quotient agree with the already
defined Faber recurrence, with its corrected zero-th Laurent coefficient. -/
theorem kernel_taylor_coefficient {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0) (k : ℕ) :
    taylorCoefficients (fun z => derivativeNumerator q z / (q z + (A - x) * z)) k =
      value (laurentCoefficients (taylorCoefficients q))
        (laurentVariable (taylorCoefficients q) A x) k := by
  have hqs := taylorCoefficients_series (hq 0 (by simp))
  have hH := laurent_kernel_analytic hq A x hne
  apply analytic_kernel_coefficient _ _ (kernel_denominator_series hqs hq0 A x)
    (taylorCoefficients_series (hH 0 (by simp))) (kernel_numerator_series hqs hq0) _ k
  filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
  have hzden := hne z hz
  dsimp only [kernelDenominator, modelDerivative]
  field_simp

/-- The actual differentiated Faber generating identity throughout the disk.
The only assumptions are analyticity and exclusion of the displayed poles. -/
theorem kernel_generating_hasSum {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    HasSum (fun k => value (laurentCoefficients (taylorCoefficients q))
      (laurentVariable (taylorCoefficients q) A x) k * z ^ k)
      (derivativeNumerator q z / (q z + (A - x) * z)) := by
  have hs := canonical_taylor_hasSum (laurent_kernel_analytic hq A x hne).differentiableOn hz
  simpa only [kernel_taylor_coefficient hq hq0 A x hne] using hs

/-- Absolute convergence of the Faber generating series on every point of the
unit disk. Convexity and positivity are not needed for this conclusion. -/
theorem kernel_generating_norm_summable {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Summable (fun k => ‖value (laurentCoefficients (taylorCoefficients q))
      (laurentVariable (taylorCoefficients q) A x) k * z ^ k‖) :=
  (kernel_generating_hasSum hq hq0 A x hne hz).summable.norm

/-- The equivalent product of coefficient norms and radial powers, convenient
for later exterior estimates with `z = w⁻¹`. -/
theorem kernel_generating_norm_mul_pow_summable {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Summable (fun k => ‖value (laurentCoefficients (taylorCoefficients q))
      (laurentVariable (taylorCoefficients q) A x) k‖ * ‖z‖ ^ k) := by
  simpa only [norm_mul, norm_pow] using kernel_generating_norm_summable hq hq0 A x hne hz

#print axioms canonical_taylor_hasSum
#print axioms kernel_taylor_coefficient
#print axioms kernel_generating_hasSum
#print axioms kernel_generating_norm_summable

end
end ExteriorReduction.FaberKernel
