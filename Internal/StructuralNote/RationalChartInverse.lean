import StructuralNote.RationalAngleBranch

/-! The inverse rational circle chart and quantitative bounds needed to recover
small rational parameters from an actual nearby unit-vector configuration. -/

namespace StructuralNote.RationalChartInverse

open RationalChart Erdos1045.EventualExact.LensClosure
noncomputable section

def parameter (z : ℂ) : ℝ := z.im / (1 + z.re)

theorem rotation_parameter {z : ℂ} (hz : ‖z‖ = 1) (hr : 0 < 1 + z.re) :
    rotation (parameter z) = z := by
  have hn : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z
    rw [hz] at h
    simpa only [Complex.normSq_apply, pow_two, one_mul] using h
  have hd : 1 + (z.im / (1 + z.re)) ^ 2 = 2 / (1 + z.re) := by
    field_simp
    nlinarith
  apply Complex.ext
  · change (1 - (z.im / (1 + z.re)) ^ 2) / (1 + (z.im / (1 + z.re)) ^ 2) = z.re
    rw [hd]
    field_simp
    nlinarith
  · change (2 * (z.im / (1 + z.re))) / (1 + (z.im / (1 + z.re)) ^ 2) = z.im
    rw [hd]
    field_simp

@[simp] theorem parameter_rotation (t : ℝ) : parameter (rotation t) = t := recover_parameter t

theorem parameter_abs_le {z : ℂ} (hr : 0 ≤ z.re) : |parameter z| ≤ ‖z - 1‖ := by
  have hd : 0 < 1 + z.re := by linarith
  rw [parameter, abs_div, abs_of_pos hd]
  have hi : |z.im| ≤ ‖z - 1‖ := by
    simpa only [Complex.sub_im, Complex.one_im, sub_zero] using Complex.abs_im_le_norm (z - 1)
  exact (div_le_self (abs_nonneg _) (by linarith : 1 ≤ 1 + z.re)).trans hi

theorem real_part_pos_of_close {z : ℂ} (hz : ‖z - 1‖ < 1) : 0 < z.re := by
  have hr : |z.re - 1| ≤ ‖z - 1‖ := by
    simpa only [Complex.sub_re, Complex.one_re] using Complex.abs_re_le_norm (z - 1)
  have h := (abs_lt.mp (hr.trans_lt hz)).1
  linarith

theorem parameter_abs_lt_of_close {z : ℂ} {ε : ℝ} (hε : ε ≤ 1) (hz : ‖z - 1‖ < ε) :
    |parameter z| < ε :=
  (parameter_abs_le (real_part_pos_of_close (hz.trans_le hε)).le).trans_lt hz

theorem unit_parameter {α : ℝ} (hα : |α| < Real.pi) : parameter (unit α) = Real.tan (α / 2) := by
  have h := RationalAngleBranch.angle_inverse hα
  have he : rotation (Real.tan (α / 2)) = unit α := by
    rw [RationalAngleBranch.rotation_eq_unit_arctan, h]
  rw [← he, parameter_rotation]

end
end StructuralNote.RationalChartInverse
