import StructuralNote.FixedDualClassificationGridComparison
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! Exact L1 norm of every translated nonzero trigonometric character. -/

namespace StructuralNote.FixedDualClassificationCosineNorm

open Real MeasureTheory Set
open FixedDualClassificationStep
noncomputable section

theorem abs_cos_periodic : Function.Periodic (fun t : ℝ => |cos t|) Real.pi := by
  intro t
  simp only [cos_add_pi, abs_neg]

theorem abs_cos_integral : (∫ t in (0 : ℝ)..Real.pi, |cos t|) = 2 := by
  have h := abs_cos_periodic.intervalIntegral_add_eq 0 (-(Real.pi / 2))
  simp only [zero_add, show -(Real.pi / 2) + Real.pi = Real.pi / 2 by ring] at h
  rw [h]
  calc
    _ = ∫ t in -(Real.pi / 2)..Real.pi / 2, cos t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith [pi_pos])] at ht
      exact abs_of_nonneg (cos_nonneg_of_mem_Icc ht)
    _ = 2 := by rw [integral_cos]; norm_num

theorem abs_cos_integral_translate (p : ℕ) (θ : ℝ) :
    (∫ t in θ..θ + (p : ℝ) * Real.pi, |cos t|) = 2 * p := by
  have h := abs_cos_periodic.intervalIntegral_add_zsmul_eq (p : ℤ) θ
    (fun a b => continuous_cos.abs.intervalIntegrable a b)
  have hbase := abs_cos_periodic.intervalIntegral_add_eq θ 0
  simp only [zero_add, abs_cos_integral] at hbase
  simp only [zsmul_eq_mul, Int.cast_natCast, hbase] at h
  simpa only [mul_comm (p : ℝ) 2] using h

theorem abs_cos_integral_affine {p : ℕ} (hp : 0 < p) (θ : ℝ) :
    (∫ t in (0 : ℝ)..2 * Real.pi, |cos ((p : ℝ) * t + θ)|) = 4 := by
  have hpR : (p : ℝ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun u : ℝ => |cos (u + θ)|) hpR,
    intervalIntegral.integral_comp_add_right (fun t : ℝ => |cos t|) θ, mul_zero, zero_add]
  have he : (p : ℝ) * (2 * Real.pi) + θ = θ + ((2 * p : ℕ) : ℝ) * Real.pi := by
    push_cast
    ring
  rw [he, abs_cos_integral_translate, smul_eq_mul]
  push_cast
  field_simp
  norm_num

theorem phase_align (z : ℂ) : oscillation (-1) z.arg * z = (‖z‖ : ℂ) := by
  have he : oscillation (-1) z.arg = Complex.exp (-((z.arg : ℂ) * Complex.I)) := by
    unfold oscillation
    congr 1
    push_cast
    ring
  rw [he, ← Complex.norm_mul_exp_arg_mul_I z, mul_left_comm, ← Complex.exp_add]
  simp

end
end StructuralNote.FixedDualClassificationCosineNorm
