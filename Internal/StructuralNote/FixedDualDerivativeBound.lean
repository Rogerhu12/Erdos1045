import StructuralNote.FixedDualTable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Uniform control of the actual witness derivative on all ten certified intervals. -/

namespace StructuralNote.FixedDualDerivativeBound

open Real Set FixedDualPrimitive FixedDualArithmetic
noncomputable section

theorem small_mul_log_abs_le_one {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    |s * log (2 * s)| ≤ 1 := by
  have h2s : 0 < 2 * s := by positivity
  by_cases h : 1 ≤ 2 * s
  · have hlog : 0 ≤ log (2 * s) := log_nonneg h
    have hup := log_le_sub_one_of_pos h2s
    rw [abs_of_nonneg (mul_nonneg hs.le hlog)]
    have hl : log (2 * s) ≤ 1 := by linarith
    exact (mul_le_mul_of_nonneg_left hl hs.le).trans (by simpa using hs1)
  · have hlog : log (2 * s) ≤ 0 := log_nonpos h2s.le (le_of_not_ge h)
    have hup := log_le_sub_one_of_pos (inv_pos.mpr h2s)
    rw [log_inv] at hup
    have hm := mul_le_mul_of_nonneg_left hup hs.le
    have he : s * ((2 * s)⁻¹ - 1) = 1 / 2 - s := by field_simp
    rw [he] at hm
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hs.le hlog)]
    nlinarith only [hm, hs]

theorem sine_lower_on_table {u : ℝ} (hu : u ∈ Icc (3 / 50 : ℝ) (69 / 50)) :
    1 / 17 ≤ sin u := by
  have hs := sin_ge_sub_cube (by norm_num : (0 : ℝ) ≤ 3 / 50)
  have hm := sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ (3 / 50 : ℝ) by linarith [pi_pos])
    (show u ≤ Real.pi / 2 by linarith [pi_gt_three, hu.2]) hu.1
  norm_num at hs
  linarith

/-- The constant 26 applies to all signed parameters in the appendix. -/
theorem witnessFirst_abs_lt_twenty_six {b u : ℝ} (hb : |b| ≤ 1)
    (hu : u ∈ Icc (3 / 50 : ℝ) (69 / 50)) : |witnessFirst b u| < 26 := by
  have hs := sine_lower_on_table hu
  have hs0 : 0 < sin u := by linarith
  have hlog := small_mul_log_abs_le_one hs0 (sin_le_one u)
  have hc : |cos u ^ 2 / sin u| ≤ 17 := by
    rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hs0.le)]
    apply (div_le_iff₀ hs0).mpr
    nlinarith only [sin_sq_add_cos_sq u, sq_nonneg (sin u), hs]
  have ht : |(Real.pi / 2 - u) * cos u| < 2 := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi / 2 - u by linarith [pi_gt_three, hu.2])]
    have hh := mul_le_mul_of_nonneg_left (abs_cos_le_one u)
      (show 0 ≤ Real.pi / 2 - u by linarith [pi_gt_three, hu.2])
    nlinarith only [hh, pi_lt_four, hu.1]
  have hthree : |3 * b * cos (3 * u)| ≤ 3 := by
    rw [abs_mul, abs_mul]
    norm_num
    have hm := mul_le_mul hb (abs_cos_le_one (3 * u)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith only [hm]
  have hfirst : |-3 * sin (3 * u)| ≤ 3 := by
    rw [abs_mul]
    norm_num
    linarith [abs_sin_le_one (3 * u)]
  have htri : |witnessFirst b u| ≤ |-3 * sin (3 * u)| + |3 * b * cos (3 * u)| +
      |sin u * log (2 * sin u)| + |cos u ^ 2 / sin u| + |(Real.pi / 2 - u) * cos u| := by
    unfold witnessFirst
    calc
      _ ≤ |(-3 * sin (3 * u) + 3 * b * cos (3 * u) - sin u * log (2 * sin u)) +
          cos u ^ 2 / sin u| + |(Real.pi / 2 - u) * cos u| := abs_sub _ _
      _ ≤ (|-3 * sin (3 * u) + 3 * b * cos (3 * u) - sin u * log (2 * sin u)| +
          |cos u ^ 2 / sin u|) + |(Real.pi / 2 - u) * cos u| := by gcongr; exact abs_add_le _ _
      _ ≤ _ := by
        have hsub := abs_sub (-3 * sin (3 * u) + 3 * b * cos (3 * u))
          (sin u * log (2 * sin u))
        have hadd := abs_add_le (-3 * sin (3 * u)) (3 * b * cos (3 * u))
        linarith
  linarith

theorem table_row_domain (i : Fin 10) {u : ℝ}
    (hu : u ∈ Icc (left (rows i) : ℝ) (right (rows i) : ℝ)) :
    |(signedParameter (rows i) : ℝ)| ≤ 1 ∧ u ∈ Icc (3 / 50 : ℝ) (69 / 50) := by
  fin_cases i <;> norm_num [rows, left, right, signedParameter] at hu ⊢ <;> constructor <;> linarith

theorem witnessFirst_on_table (i : Fin 10) {u : ℝ}
    (hu : u ∈ Icc (left (rows i) : ℝ) (right (rows i) : ℝ)) :
    |witnessFirst (signedParameter (rows i)) u| < 26 := by
  obtain ⟨hb, hd⟩ := table_row_domain i hu
  exact witnessFirst_abs_lt_twenty_six hb hd

end
end StructuralNote.FixedDualDerivativeBound
