import StructuralNote.FixedDualPrimitive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The first and sixth rows of Appendix A, as inequalities for the actual
transcendental functions. The logarithm interval comes from a five-term series
with a proved remainder, not an externally supplied numerical approximation. -/

namespace StructuralNote.FixedDualIntervals

open Real FixedDualPrimitive
open scoped BigOperators
noncomputable section

/-- A kernel-checked logarithm enclosure from the existing atanh-series theorem. -/
theorem log_two_interval :
    (6931 : ℝ) / 10000 < log 2 ∧ log 2 < 6932 / 10000 := by
  have h := Real.sum_range_sub_log_div_le (x := (1 : ℝ) / 3) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  obtain ⟨hl, hu⟩ := abs_le.mp h
  constructor <;> linarith

theorem scaled_log_identity {x : ℝ} (hx : 0 < x) :
    log (8 * x) = 3 * log 2 + log x := by
  rw [log_mul (by norm_num) hx.ne']
  have he : (8 : ℝ) = 2 ^ 3 := by norm_num
  rw [he, log_pow]
  norm_num

/-- Rational interval bounds for the logarithm, after scaling near one. -/
theorem scaled_log_bounds {x : ℝ} (hx : 0 < x) :
    1 - (8 * x)⁻¹ - 3 * (6932 / 10000) < log x ∧
      log x < 8 * x - 1 - 3 * (6931 / 10000) := by
  have hlo := one_sub_inv_le_log_of_pos (by positivity : 0 < 8 * x)
  have hhi := log_le_sub_one_of_pos (by positivity : 0 < 8 * x)
  rw [scaled_log_identity hx] at hlo hhi
  constructor <;> linarith [log_two_interval.1, log_two_interval.2]

theorem sine_cosine_interval {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ sin x ∧ sin x ≤ x ∧ 1 - x ^ 2 / 2 ≤ cos x ∧ cos x ≤ 1 :=
  ⟨sin_ge_sub_cube hx, sin_le hx, one_sub_sq_div_two_le_cos, cos_le_one x⟩

theorem log_sine_left_upper : log (2 * sin ((3 : ℝ) / 50)) < -21193 / 10000 := by
  obtain ⟨hslo, hshi, _, _⟩ := sine_cosine_interval (x := (3 : ℝ) / 50) (by norm_num)
  have hspos : 0 < sin ((3 : ℝ) / 50) := by norm_num at hslo; linarith
  have h := (scaled_log_bounds (by positivity : 0 < 2 * sin ((3 : ℝ) / 50))).2
  linarith

theorem log_sine_right_interval :
    (-987 : ℝ) / 500 < log (2 * sin ((7 : ℝ) / 100)) ∧
      log (2 * sin ((7 : ℝ) / 100)) < -1 := by
  obtain ⟨hslo, hshi, _, _⟩ := sine_cosine_interval (x := (7 : ℝ) / 100) (by norm_num)
  norm_num at hslo
  have hspos : 0 < sin ((7 : ℝ) / 100) := by linarith
  have h := scaled_log_bounds (by positivity : 0 < 2 * sin ((7 : ℝ) / 100))
  have hinv : (8 * (2 * sin ((7 : ℝ) / 100)))⁻¹ ≤ (375000 / 419657 : ℝ) := by
    calc
      _ ≤ (419657 / 375000 : ℝ)⁻¹ := by
        simpa only [one_div] using one_div_le_one_div_of_le
          (by norm_num : (0 : ℝ) < 419657 / 375000)
          (by linarith : 419657 / 375000 ≤ 8 * (2 * sin ((7 : ℝ) / 100)))
      _ = _ := by norm_num
  constructor <;> linarith [h.1, h.2]

/-- The left endpoint is negative for both positive parameters in the table. -/
theorem first_bracket_left_negative {b : ℝ} (hb : b ≤ 1) :
    witness b (3 / 50) < 0 := by
  obtain ⟨hslo, hshi, hclo, _⟩ := sine_cosine_interval (x := (3 : ℝ) / 50) (by norm_num)
  obtain ⟨hs3lo, hs3hi, _, hc3hi⟩ :=
    sine_cosine_interval (x := 3 * ((3 : ℝ) / 50)) (by norm_num)
  norm_num at hslo hshi hclo hs3lo hs3hi
  have hspos : 0 ≤ sin ((3 : ℝ) / 50) := by linarith
  have hs3pos : 0 ≤ sin (3 * ((3 : ℝ) / 50)) := by norm_num at hs3lo ⊢; linarith
  have hthird : b * sin (3 * ((3 : ℝ) / 50)) ≤ 9 / 50 := by
    have h := mul_le_mul_of_nonneg_right hb hs3pos
    norm_num at h
    linarith
  have hlog := log_sine_left_upper
  have hcoslog : cos ((3 : ℝ) / 50) * (1 + log (2 * sin ((3 : ℝ) / 50))) ≤
      (4991 : ℝ) / 5000 * (-11193 / 10000) := by
    calc
      _ ≤ cos ((3 : ℝ) / 50) * (-11193 / 10000) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonpos_right hclo (by norm_num)
  have hnegative : (3 / 2 - (3 : ℝ) / 50) * (14991 / 250000) ≤
      (Real.pi / 2 - 3 / 50) * sin ((3 : ℝ) / 50) := by
    apply mul_le_mul
    · linarith [Real.pi_gt_three]
    · exact hslo
    · norm_num
    · linarith [Real.pi_gt_three]
  rw [witness_expand]
  linarith

/-- The right endpoint is positive even for the smaller parameter `b = 1/2`. -/
theorem first_bracket_right_positive {b : ℝ} (hb : 1 / 2 ≤ b) :
    0 < witness b (7 / 100) := by
  obtain ⟨hslo, hshi, hclo, hchi⟩ :=
    sine_cosine_interval (x := (7 : ℝ) / 100) (by norm_num)
  obtain ⟨hs3lo, _, hc3lo, _⟩ :=
    sine_cosine_interval (x := 3 * ((7 : ℝ) / 100)) (by norm_num)
  norm_num at hslo hshi hclo hs3lo hc3lo
  have hspos : 0 ≤ sin ((7 : ℝ) / 100) := by linarith
  have hs3pos : 0 ≤ sin (3 * ((7 : ℝ) / 100)) := by norm_num at hs3lo ⊢; linarith
  have hthird : (416913 : ℝ) / 4000000 ≤ b * sin (3 * ((7 : ℝ) / 100)) := by
    have h := mul_le_mul_of_nonneg_right hb hs3pos
    norm_num at h
    linarith
  obtain ⟨hloglo, hloghi⟩ := log_sine_right_interval
  have hcoslog : (-487 : ℝ) / 500 <
      cos ((7 : ℝ) / 100) * (1 + log (2 * sin ((7 : ℝ) / 100))) := by
    have h := mul_le_mul_of_nonpos_right hchi (by linarith :
      1 + log (2 * sin ((7 : ℝ) / 100)) ≤ 0)
    linarith
  have hnegative : (Real.pi / 2 - 7 / 100) * sin ((7 : ℝ) / 100) ≤
      (3927 / 2500 - (7 : ℝ) / 100) * (7 / 100) := by
    apply mul_le_mul
    · linarith [Real.pi_lt_d4]
    · exact hshi
    · exact hspos
    · norm_num
  rw [witness_expand]
  linarith

/-- Four of the twenty endpoint signs are now proved for the actual functions. -/
theorem first_and_sixth_rows :
    witness (1 / 2) (6 / 100) < 0 ∧ 0 < witness (1 / 2) (7 / 100) ∧
      witness 1 (6 / 100) < 0 ∧ 0 < witness 1 (7 / 100) := by
  constructor
  · convert first_bracket_left_negative (b := (1 : ℝ) / 2) (by norm_num) using 1
    norm_num
  constructor
  · exact first_bracket_right_positive (by norm_num)
  constructor
  · convert first_bracket_left_negative (b := (1 : ℝ)) (by norm_num) using 1
    norm_num
  · exact first_bracket_right_positive (by norm_num)

end
end StructuralNote.FixedDualIntervals
