import StructuralNote.FixedDualClassificationStep
import Mathlib.Analysis.Fourier.AddCircle

/-! The computed step coefficients are the standard Fourier coefficients, and
their full integer square sum is exactly the discrete square mass. -/

namespace StructuralNote.FixedDualClassificationParseval

open Real Complex MeasureTheory Set FixedDualClassificationStep
open scoped BigOperators ComplexConjugate
noncomputable section

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem fourier_on_circle (p : ℤ) (t : ℝ) :
    fourier p (t : AddCircle (2 * Real.pi)) = oscillation p t := by
  rw [fourier_coe_apply]
  unfold oscillation
  congr 1
  push_cast
  field_simp

theorem profileCoefficient_eq_fourierCoeffOn {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (scale : ℝ) (p : ℤ) :
    profileCoefficient (stepProfile q scale) p =
      fourierCoeffOn (by positivity : (0 : ℝ) < 2 * Real.pi)
        (fun t => (stepProfile q scale t : ℂ)) p := by
  rw [profileCoefficient_eq_interval hn, fourierCoeffOn_eq_integral]
  simp only [sub_zero, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [div_eq_inv_mul, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [mul_comm]
  congr 1
  rw [fourier_coe_apply]
  unfold oscillation
  congr 1
  push_cast
  field_simp

  ring

theorem stepProfile_sq {n : ℕ} (q : Fin n → ℝ) (scale t : ℝ) :
    stepProfile q scale t ^ 2 = stepProfile (fun j => q j ^ 2) (scale ^ 2) t := by
  by_cases ht : ∃ j : Fin n, t ∈ cell n j
  · obtain ⟨j, hj⟩ := ht
    rw [stepProfile_at_cell q scale j hj,
      stepProfile_at_cell (fun j => q j ^ 2) (scale ^ 2) j hj]
    ring
  · simp only [stepProfile_zero q scale (not_exists.mp ht), zero_pow (by decide : 2 ≠ 0),
      stepProfile_zero (fun j => q j ^ 2) (scale ^ 2) (not_exists.mp ht)]

theorem stepProfile_mean {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) :
    (∫ t in 0..2 * Real.pi, stepProfile q scale t) / (2 * Real.pi) =
      scale * (∑ j, q j) / n := by
  have h := profileCoefficient_eq hn q scale 0
  rw [profileCoefficient_eq_interval hn] at h
  simp only [signedMidpointCoefficient, Int.cast_zero, neg_zero, oscillation, zero_mul,
    Complex.ofReal_zero, Complex.exp_zero, mul_one, zero_div, sinc_zero] at h
  rw [intervalIntegral.integral_ofReal, ← mul_div_assoc] at h
  norm_cast at h ⊢

theorem stepProfile_square_mean {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) :
    (∫ t in 0..2 * Real.pi, stepProfile q scale t ^ 2) / (2 * Real.pi) =
      scale ^ 2 * (∑ j, q j ^ 2) / n := by
  simp_rw [stepProfile_sq]
  exact stepProfile_mean hn _ _

theorem stepProfile_memLp {n : ℕ} (q : Fin n → ℝ) (scale : ℝ) :
    MemLp (fun t => (stepProfile q scale t : ℂ)) 2
      (volume.restrict (Ioc 0 (2 * Real.pi))) := by
  have hq (j : Fin n) : |q j| ≤ ∑ k, |q k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (q k)) (Finset.mem_univ j)
  apply MemLp.of_bound
    ((Complex.continuous_ofReal.measurable.comp (stepProfile_measurable q scale)).aestronglyMeasurable)
    (|scale| * ∑ j, |q j|)
  apply Filter.Eventually.of_forall
  intro t
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
    stepProfile_bound q scale (∑ j, |q j|) (Finset.sum_nonneg (fun j _ => abs_nonneg _)) hq t

theorem profileCoefficient_parseval {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ) :
    HasSum (fun p : ℤ => ‖profileCoefficient (stepProfile q scale) p‖ ^ 2)
      (scale ^ 2 * (∑ j, q j ^ 2) / n) := by
  have h := hasSum_sq_fourierCoeffOn
    (by positivity : (0 : ℝ) < 2 * Real.pi) (stepProfile_memLp q scale)
  simp_rw [← profileCoefficient_eq_fourierCoeffOn hn q scale] at h
  simp only [sub_zero, smul_eq_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [← div_eq_inv_mul, stepProfile_square_mean hn] at h
  exact h

theorem profileCoefficient_bessel {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (scale : ℝ)
    (s : Finset ℤ) :
    ∑ p ∈ s, ‖profileCoefficient (stepProfile q scale) p‖ ^ 2 ≤
      scale ^ 2 * (∑ j, q j ^ 2) / n := by
  have h := profileCoefficient_parseval hn q scale
  exact sum_le_hasSum s (fun p _ => sq_nonneg _) h

end
end StructuralNote.FixedDualClassificationParseval
