import StructuralNote.FixedDualClassificationThirdReference
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sign

/-! Exact Fourier coefficients of the bounded antiperiodic third square wave. -/

namespace StructuralNote.FixedDualClassificationTrialCoefficients

open Real MeasureTheory Set
open FixedDualClassificationStep FixedDualClassificationCoefficientBound
open FixedDualClassificationThirdReference
noncomputable section

def trial (t : ℝ) : ℝ := Real.pi / 2 * Real.sign (sin (3 * t))

theorem trial_measurable : Measurable trial := by
  unfold trial Real.sign
  exact measurable_const.mul ((Measurable.ite
    (measurableSet_lt (by fun_prop) measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      measurable_const measurable_const)))

theorem trial_bound (t : ℝ) : |trial t| ≤ Real.pi / 2 := by
  unfold trial
  have hA : 0 < Real.pi / 2 := by positivity
  rcases Real.sign_apply_eq (sin (3 * t)) with h | h | h <;>
    rw [h] <;> simp [abs_of_pos hA, hA.le]

theorem trial_periodic : Function.Periodic trial (2 * Real.pi / 3) := by
  intro t
  unfold trial
  rw [show 3 * (t + 2 * Real.pi / 3) = 3 * t + 2 * Real.pi by ring,
    sin_add_two_pi]

theorem trial_antiperiodic (t : ℝ) : trial (t + Real.pi) = -trial t := by
  unfold trial
  rw [show 3 * (t + Real.pi) = (3 * t + Real.pi) + 2 * Real.pi by ring,
    sin_add_two_pi, sin_add_pi, Real.sign_neg, mul_neg]

theorem trial_positive_half {t : ℝ} (ht : t ∈ Ioo 0 (Real.pi / 3)) :
    trial t = Real.pi / 2 := by
  have hs : 0 < sin (3 * t) := sin_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [trial, Real.sign_of_pos hs, mul_one]

theorem trial_negative_half {t : ℝ} (ht : t ∈ Ioo (Real.pi / 3) (2 * Real.pi / 3)) :
    trial t = -(Real.pi / 2) := by
  have hs : 0 < sin (3 * t - Real.pi) :=
    sin_pos_of_mem_Ioo ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hn : sin (3 * t) < 0 := by
    rw [show 3 * t = (3 * t - Real.pi) + Real.pi by ring, sin_add_pi]
    linarith
  simp only [trial, Real.sign_of_neg hn, mul_neg_one]

theorem oscillation_integral {p : ℝ} (hp : p ≠ 0) (a b : ℝ) :
    (∫ t in a..b, oscillation p t) =
      (oscillation p b - oscillation p a) / ((p : ℂ) * Complex.I) := by
  have he (t : ℝ) : oscillation p t = Complex.exp (((p : ℂ) * Complex.I) * t) := by
    unfold oscillation
    congr 1
    push_cast
    ring
  simp only [he]
  exact integral_exp_mul_complex (mul_ne_zero (Complex.ofReal_ne_zero.mpr hp) Complex.I_ne_zero)

theorem trial_phase_half (k : ℕ) :
    oscillation (-(3 * (2 * k + 1) : ℤ)) (Real.pi / 3) = -1 := by
  unfold oscillation
  have he : (((-(3 * (2 * k + 1) : ℤ) : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I =
      ((-(k : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + -(Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
    Complex.exp_neg_pi_mul_I, one_mul]

theorem trial_phase_full (k : ℕ) :
    oscillation (-(3 * (2 * k + 1) : ℤ)) (2 * Real.pi / 3) = 1 := by
  unfold oscillation
  have he : (((-(3 * (2 * k + 1) : ℤ) : ℝ) * (2 * Real.pi / 3) : ℝ) : ℂ) * Complex.I =
      ((-(2 * k + 1 : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

theorem trial_coefficient (k : ℕ) :
    coefficient trial (3 * (2 * k + 1)) = -Complex.I / (2 * k + 1) := by
  let p : ℝ := -(3 * (2 * k + 1) : ℤ)
  let g (t : ℝ) : ℂ := (trial t : ℂ) * oscillation p t
  have hp : p ≠ 0 := by
    dsimp [p]
    push_cast
    exact neg_ne_zero.mpr (by positivity)
  have hi (a b : ℝ) : IntervalIntegrable g volume a b :=
    oscillation_integrable trial_measurable trial_bound p a b
  have hg : Function.Periodic g (2 * Real.pi / 3) := by
    intro t
    dsimp only [g]
    rw [trial_periodic t, oscillation_add, trial_phase_full]
    ring
  have hfirst : (∫ t in 0..Real.pi / 3, g t) =
      (Real.pi / 2 : ℂ) * ((-2) / ((p : ℂ) * Complex.I)) := by
    calc
      _ = ∫ t in 0..Real.pi / 3, (Real.pi / 2 : ℂ) * oscillation p t := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by positivity)
        intro t ht
        dsimp only [g]
        rw [trial_positive_half ht]
        push_cast
        rfl
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, oscillation_integral hp]
        change (Real.pi / 2 : ℂ) * ((oscillation (-(3 * (2 * k + 1) : ℤ)) (Real.pi / 3) -
          oscillation p 0) / _) = _
        rw [trial_phase_half]
        norm_num [oscillation]
  have hsecond : (∫ t in Real.pi / 3..2 * Real.pi / 3, g t) =
      -(Real.pi / 2 : ℂ) * (2 / ((p : ℂ) * Complex.I)) := by
    calc
      _ = ∫ t in Real.pi / 3..2 * Real.pi / 3, -(Real.pi / 2 : ℂ) * oscillation p t := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith [Real.pi_pos])
        intro t ht
        dsimp only [g]
        rw [trial_negative_half ht]
        push_cast
        rfl
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, oscillation_integral hp]
        change -(Real.pi / 2 : ℂ) * ((oscillation (-(3 * (2 * k + 1) : ℤ)) (2 * Real.pi / 3) -
          oscillation (-(3 * (2 * k + 1) : ℤ)) (Real.pi / 3)) / _) = _
        rw [trial_phase_full, trial_phase_half]
        ring
  have hperiod := hg.intervalIntegral_add_zsmul_eq (3 : ℤ) 0 hi
  have hT : (3 : ℤ) • (2 * Real.pi / 3) = 2 * Real.pi := by
    simp only [zsmul_eq_mul, Int.cast_ofNat]
    ring
  rw [hT, zero_add, zero_add, zsmul_eq_mul] at hperiod
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (Real.pi / 3))
    (hi (Real.pi / 3) (2 * Real.pi / 3)), hfirst, hsecond] at hperiod
  unfold coefficient
  change (∫ t in 0..2 * Real.pi, g t) / (2 * Real.pi) = _
  rw [hperiod]
  dsimp only [p]
  push_cast
  have hq : (2 * (k : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * (k : ℝ) + 1) ≠ 0)
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero, hq]
  simp [Complex.I_sq]
  ring

theorem trial_coefficient_norm (k : ℕ) :
    ‖coefficient trial (3 * (2 * k + 1))‖ = 1 / (2 * k + 1) := by
  rw [trial_coefficient, norm_div, norm_neg, Complex.norm_I]
  norm_cast

end
end StructuralNote.FixedDualClassificationTrialCoefficients
