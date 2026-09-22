import StructuralNote.FixedDualClassificationHerglotzSeries
import StructuralNote.FixedDualClassificationCircleShift
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! The actual bounded circle profile as Herglotz boundary data. -/

namespace StructuralNote.ThirdSchwarzBoundary

open Real Complex Set Metric MeasureTheory AddCircle
open FixedDualClassificationStep FixedDualClassificationParseval
open FixedDualClassificationCircleShift FixedDualClassificationCoefficientBound
open FixedDualClassificationHerglotz
noncomputable section

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

def boundary (F : Torus → ℝ) (ζ : ℂ) : ℝ := F (ζ.arg : Torus)

theorem boundary_circleMap (F : Torus → ℝ) (t : ℝ) :
    boundary F (circleMap 0 1 t) = F (t : Torus) := by
  have he : circleMap 0 1 t = (((t : Real.Angle).toCircle) : ℂ) := by
    simp [circleMap, _root_.Circle.coe_exp]
  unfold boundary
  rw [he]
  exact congrArg F (Real.Angle.arg_toCircle (t : Real.Angle))

theorem boundary_measurable {F : Torus → ℝ} (hF : Measurable F) :
    Measurable (boundary F) :=
  hF.comp (AddCircle.measurable_mk'.comp Complex.measurable_arg)

theorem boundary_integrable {F : Torus → ℝ} (hF : Measurable F)
    {A : ℝ} (hb : ∀ x, |F x| ≤ A) : CircleIntegrable (boundary F) 0 1 := by
  have hi := bounded_intervalIntegrable (hF.comp AddCircle.measurable_mk')
    (fun t : ℝ => hb (t : Torus)) 0 (2 * Real.pi)
  simpa only [CircleIntegrable, Function.comp_def, boundary_circleMap] using hi

theorem circle_power_inverse (k : ℕ) (t : ℝ) :
    (circleMap 0 1 t ^ k)⁻¹ = oscillation (-(k : ℝ)) t := by
  simp only [circleMap_zero, Complex.ofReal_one, one_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_neg, FixedDualClassificationStep.oscillation]
  congr 1
  push_cast
  ring

theorem boundary_coefficient (F : Torus → ℝ) (k : ℕ) :
    circleAverage (fun ζ => (boundary F ζ : ℂ) / ζ ^ k) 0 1 =
      fourierCoeff (fun x => (F x : ℂ)) k := by
  rw [circleAverage_def, fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [zero_add, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_inv, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [boundary_circleMap, div_eq_mul_inv, circle_power_inverse, fourier_on_circle]
  norm_cast
  ring

theorem even_fourier_zero {F : Torus → ℝ}
    (hanti : ∀ x, F (x + (Real.pi : ℝ)) = -F x) (k : ℕ) :
    fourierCoeff (fun x => (F x : ℂ)) (2 * k) = 0 := by
  have he : fourier (-(2 * (k : ℤ))) (Real.pi : Torus) = 1 := by
    rw [fourier_on_circle]
    unfold FixedDualClassificationStep.oscillation
    push_cast
    rw [show -(2 * (k : ℂ)) * Real.pi * Complex.I =
      ((-(k : ℤ)) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    simpa only [Int.cast_neg] using Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
  have hs := integral_add_right_eq_self (μ := haarAddCircle)
    (fun x : Torus => fourier (-(2 * (k : ℤ))) x * (F x : ℂ))
    (Real.pi : Torus)
  simp only [fourier_argument_add, he, mul_one, hanti, Complex.ofReal_neg, mul_neg,
    integral_neg] at hs
  unfold fourierCoeff
  simp only [smul_eq_mul]
  change -(∫ x : Torus, fourier (-(2 * (k : ℤ))) x * (F x : ℂ) ∂haarAddCircle) =
    (∫ x : Torus, fourier (-(2 * (k : ℤ))) x * (F x : ℂ) ∂haarAddCircle) at hs
  linear_combination -hs / 2

theorem boundary_mean_zero {F : Torus → ℝ} (hF : Measurable F)
    {A : ℝ} (hb : ∀ x, |F x| ≤ A)
    (hanti : ∀ x, F (x + (Real.pi : ℝ)) = -F x) :
    circleAverage (boundary F) 0 1 = 0 := by
  have hc := boundary_coefficient F 0
  have hz := even_fourier_zero hanti 0
  norm_num only [Nat.cast_zero, mul_zero, pow_zero, div_one] at hc hz
  have hreal := Complex.ofRealCLM.circleAverage_comp_comm (boundary_integrable hF hb)
  change circleAverage (fun ζ => (boundary F ζ : ℂ)) 0 1 =
    ((circleAverage (boundary F) 0 1 : ℝ) : ℂ) at hreal
  rw [hc, hz] at hreal
  exact_mod_cast hreal.symm

end
end StructuralNote.ThirdSchwarzBoundary
