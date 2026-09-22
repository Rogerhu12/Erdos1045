import StructuralNote.FixedDualClassificationPeriodicStep
import StructuralNote.FixedDualClassificationKernelTail
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Reflection and translation act on the actual circle profile. The odd
half-circle coefficients retain their exact phase and signed alias. -/

namespace StructuralNote.FixedDualClassificationCircleShift

open Real Set MeasureTheory AddCircle FixedDualClassificationStep
open FixedDualClassificationParseval FixedDualClassificationOddSpectrum
open FixedDualClassificationPeriodicStep
open scoped BigOperators ComplexConjugate
noncomputable section

abbrev Torus := AddCircle (2 * Real.pi)

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem fourier_argument_add (p : ℤ) (x y : Torus) :
    fourier p (x + y) = fourier p x * fourier p y := by
  simp only [fourier_apply, zsmul_add, toCircle_add, _root_.Circle.coe_mul]

theorem fourier_argument_neg (p : ℤ) (x : Torus) :
    fourier p (-x) = fourier (-p) x := by
  simp only [fourier_apply, smul_neg, neg_smul]

theorem fourier_argument_sub (p : ℤ) (x y : Torus) :
    fourier p (x - y) = fourier p x * conj (fourier p y) := by
  rw [sub_eq_add_neg, fourier_argument_add, fourier_argument_neg, fourier_neg]

def reflected (F : Torus → ℝ) (θ : ℝ) (u : ℝ) : ℝ := F ((θ - u : ℝ) : Torus)

theorem reflected_measurable {F : Torus → ℝ} (hF : Measurable F) (θ : ℝ) :
    Measurable (reflected F θ) := by
  exact hF.comp (((AddCircle.continuous_mk' (2 * Real.pi)).comp
    (show Continuous (fun u : ℝ => θ - u) by fun_prop)).measurable)

theorem reflected_bound {F : Torus → ℝ} {A : ℝ} (hF : ∀ x, |F x| ≤ A)
    (θ u : ℝ) : |reflected F θ u| ≤ A := hF _

theorem reflected_antiperiodic {F : Torus → ℝ}
    (hF : ∀ x, F (x + (Real.pi : ℝ)) = -F x) (θ : ℝ) (x : Torus) :
    F ((θ : Torus) - (x + (Real.pi : ℝ))) = -F ((θ : Torus) - x) := by
  have h := hF ((θ : Torus) - (x + (Real.pi : ℝ)))
  rw [show ((θ : Torus) - (x + (Real.pi : ℝ))) + (Real.pi : ℝ) = (θ : Torus) - x by abel] at h
  linarith

theorem reflected_fourierCoeff (F : Torus → ℝ) (θ : ℝ) (p : ℤ) :
    fourierCoeff (fun x : Torus => (F ((θ : Torus) - x) : ℂ)) p =
      oscillation (-p) θ * conj (fourierCoeff (fun x => (F x : ℂ)) p) := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  rw [← integral_sub_left_eq_self
    (fun x : Torus => fourier (-p) x * (F ((θ : Torus) - x) : ℂ)) haarAddCircle (θ : Torus)]
  simp_rw [sub_sub_cancel, fourier_argument_sub]
  rw [show (fun x : Torus => fourier (-p) (θ : Torus) * conj (fourier (-p) x) * (F x : ℂ)) =
      fun x => fourier (-p) (θ : Torus) * conj (fourier (-p) x * (F x : ℂ)) by
        funext x; simp only [map_mul, Complex.conj_ofReal]; ring,
    integral_const_mul, integral_conj, fourier_on_circle]
  norm_cast

theorem bounded_oscillation_integrable {F : Torus → ℝ} (hF : Measurable F)
    {A : ℝ} (hbox : ∀ x, |F x| ≤ A) (p a b : ℝ) :
    IntervalIntegrable (fun u => (F (u : Torus) : ℂ) * oscillation p u) volume a b := by
  have hm : Measurable (fun u : ℝ => (F (u : Torus) : ℂ) * oscillation p u) :=
    (Complex.continuous_ofReal.measurable.comp (hF.comp
      (show Measurable (fun u : ℝ => (u : Torus)) from AddCircle.measurable_mk'))).mul
      (oscillation_continuous p).measurable
  have hb (u : ℝ) : ‖(F (u : Torus) : ℂ) * oscillation p u‖ ≤ A := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, oscillation,
      Complex.norm_exp_ofReal_mul_I, mul_one] using hbox (u : Torus)
  constructor <;> exact (memLp_one_iff_integrable.mp
    (MemLp.of_bound hm.aestronglyMeasurable A (Filter.Eventually.of_forall hb)))

theorem odd_oscillation_pi (k : ℤ) : oscillation (-(2 * k + 1)) Real.pi = -1 := by
  unfold oscillation
  push_cast
  rw [show -(2 * (k : ℂ) + 1) * Real.pi * Complex.I =
      ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) - Real.pi * Complex.I by push_cast; ring,
    Complex.exp_sub_pi_mul_I, Complex.exp_int_mul_two_pi_mul_I]

theorem oddCoefficient_circle {F : Torus → ℝ} (hF : Measurable F)
    {A : ℝ} (hbox : ∀ x, |F x| ≤ A)
    (hanti : ∀ x, F (x + (Real.pi : ℝ)) = -F x) (k : ℤ) :
    oddCoefficient (fun u : ℝ => F (u : Torus)) k =
      fourierCoeff (fun x => (F x : ℂ)) (2 * k + 1) := by
  let g : ℝ → ℂ := fun u => (F (u : Torus) : ℂ) * oscillation (-(2 * k + 1)) u
  have hg (a b : ℝ) : IntervalIntegrable g volume a b := bounded_oscillation_integrable hF hbox _ a b
  have hper (u : ℝ) : g (u + Real.pi) = g u := by
    dsimp only [g]
    rw [AddCircle.coe_add, hanti, Complex.ofReal_neg, oscillation_add, odd_oscillation_pi]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (hg 0 Real.pi) (hg Real.pi (2 * Real.pi))
  have hshift := intervalIntegral.integral_comp_add_right g Real.pi (a := 0) (b := Real.pi)
  simp only [hper, zero_add, show Real.pi + Real.pi = 2 * Real.pi by ring] at hshift
  rw [← hshift] at hsplit
  rw [oddCoefficient_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, smul_eq_mul, Complex.real_smul, fourier_on_circle,
    Complex.ofReal_div, Complex.ofReal_one, Int.cast_neg, Int.cast_add, Int.cast_mul,
    Int.cast_ofNat, Int.cast_one]
  have hfull : (∫ u in 0..2 * Real.pi, oscillation (-(2 * k + 1)) u * (F (u : Torus) : ℂ)) =
      2 * ∫ u in 0..Real.pi, g u := by
    rw [show (fun u : ℝ => oscillation (-(2 * k + 1)) u * (F (u : Torus) : ℂ)) = g by
      funext u; dsimp [g]; ring, ← hsplit]
    ring
  rw [hfull]
  change (∫ u in 0..Real.pi, g u) / (Real.pi : ℂ) = _
  push_cast
  field_simp

theorem reflected_oddCoefficient {F : Torus → ℝ} (hF : Measurable F)
    {A : ℝ} (hbox : ∀ x, |F x| ≤ A)
    (hanti : ∀ x, F (x + (Real.pi : ℝ)) = -F x) (θ : ℝ) (k : ℤ) :
    oddCoefficient (reflected F θ) k =
      oscillation (-(2 * k + 1)) θ *
        conj (fourierCoeff (fun x => (F x : ℂ)) (2 * k + 1)) := by
  have hG : Measurable (fun x : Torus => F ((θ : Torus) - x)) :=
    hF.comp (show Continuous (fun x : Torus => (θ : Torus) - x) by fun_prop).measurable
  have h := oddCoefficient_circle hG (fun x => hbox ((θ : Torus) - x))
    (reflected_antiperiodic hanti θ) k
  change oddCoefficient (fun u : ℝ => F ((θ - u : ℝ) : Torus)) k = _
  simpa only [AddCircle.coe_sub, reflected_fourierCoeff, Int.cast_neg,
    Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using h

end
end StructuralNote.FixedDualClassificationCircleShift
