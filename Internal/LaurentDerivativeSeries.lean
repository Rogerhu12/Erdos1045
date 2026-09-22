import LaurentModelExpansion
import LaurentExteriorCalculus

/-! The actual derivative series, with canonical Laurent coefficients. -/

namespace ExteriorReduction

open Complex Metric Filter
open FaberKernel
open scoped Topology
noncomputable section

theorem modelDerivative_taylor_coefficient {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (n : ℕ) :
    taylorCoefficients (modelDerivative q) n =
      numeratorCoefficients (laurentCoefficients (taylorCoefficients q)) n := by
  have hs := taylorCoefficients_series ((modelDerivative_analytic hq hq0) 0 (by simp))
  have he := hs.eq_formalMultilinearSeries
    (kernel_numerator_series (taylorCoefficients_series (hq 0 (by simp))) hq0)
  have hn := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) he
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using hn

theorem modelDerivative_taylor_zero {q : ℂ → ℂ} (hq0 : q 0 ≠ 0) :
    taylorCoefficients (modelDerivative q) 0 = 1 := by
  simp [modelDerivative_zero hq0]

theorem modelDerivative_taylor_succ {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (m : ℕ) :
    taylorCoefficients (modelDerivative q) (m + 1) =
      -(m : ℂ) * modelLaurentCoefficient q m / q 0 := by
  rw [modelDerivative_taylor_coefficient hq hq0, numerator_succ]
  rw [← modelLaurentCoefficient_normalized]
  ring

/-- Absolute convergence of the actual weighted Laurent derivative series
at all interior model points. -/
theorem model_derivative_hasSum {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    HasSum (fun m : ℕ => (m : ℂ) * modelLaurentCoefficient q m * z ^ (m + 1))
      (q 0 - derivativeNumerator q z) := by
  have hs := canonical_taylor_hasSum (modelDerivative_analytic hq hq0).differentiableOn hz
  have ht : HasSum (fun m : ℕ =>
      (-(m : ℂ) * modelLaurentCoefficient q m / q 0) * z ^ (m + 1))
      (modelDerivative q z - 1) := by
    simpa only [Finset.sum_range_one, pow_zero, mul_one,
      modelDerivative_taylor_zero hq0, modelDerivative_taylor_succ hq hq0]
      using (hasSum_nat_add_iff' 1).mpr hs
  have hmul := ht.mul_left (-q 0)
  have he (m : ℕ) :
      -q 0 * (-(m : ℂ) * modelLaurentCoefficient q m / q 0 * z ^ (m + 1)) =
        (m : ℂ) * modelLaurentCoefficient q m * z ^ (m + 1) := by field_simp
  have hv : -q 0 * (modelDerivative q z - 1) = q 0 - derivativeNumerator q z := by
    unfold modelDerivative
    field_simp
    ring
  simpa only [he, hv] using hmul

theorem model_derivative_norm_summable {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Summable (fun m : ℕ => ‖(m : ℂ) * modelLaurentCoefficient q m * z ^ (m + 1)‖) :=
  (model_derivative_hasSum hq hq0 hz).summable.norm

theorem exterior_derivative_laurent {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (A : ℂ)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    deriv (fun v => A + v * q v⁻¹) w = q 0 -
      ∑' m : ℕ, (m : ℂ) * modelLaurentCoefficient q m * (w⁻¹) ^ (m + 1) := by
  rw [(model_derivative_hasSum hq hq0 (inv_mem_disk_of_exterior hw)).tsum_eq]
  rw [deriv_laurentExterior hq A hw]
  ring

#print axioms model_derivative_hasSum
#print axioms exterior_derivative_laurent

end
end ExteriorReduction
