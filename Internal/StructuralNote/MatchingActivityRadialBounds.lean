import StructuralNote.MatchingActivityRadialPair

/-! Quantitative radial-pair derivatives in the localized, unsaturated region. -/

namespace StructuralNote.MatchingActivityRadialBounds

open Erdos1045 Erdos1045.EventualExact Complex LensClosure
open MatchingActivityRadialPair
noncomputable section

theorem pair_re_ge_one {φ r₀ r₁ : ℝ} (hφ : |φ| ≤ 1 / 4)
    (h₀ : 3 / 4 ≤ r₀) (h₁ : 3 / 4 ≤ r₁) : 1 ≤ (pair φ r₀ r₁).re := by
  have hsq : φ ^ 2 ≤ 1 / 16 := by nlinarith [abs_le.mp hφ, sq_abs φ]
  have hc : (31 / 32 : ℝ) ≤ Real.cos φ := by nlinarith [Real.one_sub_sq_div_two_le_cos (x := φ)]
  rw [pair_re]
  have hh := mul_le_mul (show (3 / 2 : ℝ) ≤ r₀ + r₁ by linarith) hc (by norm_num) (by linarith)
  linarith

theorem argument_bound {z : ℂ} (hz : 1 ≤ z.re) : |z.arg| ≤ 2 * |z.im| := by
  have hn : 1 ≤ ‖z‖ := hz.trans (re_le_norm z)
  have hs := Real.mul_abs_le_abs_sin ((abs_arg_le_pi_div_two_iff).2 (by linarith : 0 ≤ z.re))
  rw [sin_arg, abs_div, abs_of_nonneg (norm_nonneg z)] at hs
  have him : |z.im| / ‖z‖ ≤ |z.im| := div_le_self (abs_nonneg _) hn
  have hm := mul_le_mul_of_nonneg_left (hs.trans him) Real.pi_pos.le
  have he : Real.pi * (2 / Real.pi * |z.arg|) = 2 * |z.arg| := by field_simp
  rw [he] at hm
  have hh := mul_le_mul_of_nonneg_right Real.pi_lt_four.le (abs_nonneg z.im)
  linarith

theorem direction_bound {φ r₀ r₁ : ℝ} (h : 1 ≤ (pair φ r₀ r₁).re) :
    |direction φ r₀ r₁| ≤ 2 * |r₁ - r₀| * |φ| := by
  have hh := argument_bound h
  rw [pair_im, abs_mul] at hh
  have hs := mul_le_mul_of_nonneg_left (Real.abs_sin_le_abs (x := φ)) (show 0 ≤ 2 * |r₁ - r₀| by positivity)
  change |(pair φ r₀ r₁).arg| ≤ _
  linarith only [hh, hs]

theorem length_derivative_bound {z v : ℂ} (hz : 0 < ‖z‖) (hv : ‖v‖ = 1) :
    |‖z‖ * (v / z).re| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (norm_nonneg z)]
  calc
    _ ≤ ‖z‖ * ‖v / z‖ := mul_le_mul_of_nonneg_left (abs_re_le_norm _) (norm_nonneg _)
    _ = 1 := by rw [norm_div, hv]; field_simp

theorem left_direction_derivative (φ r₀ r₁ : ℝ) :
    (unit (-φ) / pair φ r₀ r₁).im = -r₁ * Real.sin (2 * φ) / length φ r₀ r₁ ^ 2 := by
  rw [div_im, pair_re, pair_im, unit_re, unit_im, Real.cos_neg, Real.sin_neg,
    length, normSq_eq_norm_sq, Real.sin_two_mul]
  ring

theorem right_direction_derivative (φ r₀ r₁ : ℝ) :
    (unit φ / pair φ r₀ r₁).im = r₀ * Real.sin (2 * φ) / length φ r₀ r₁ ^ 2 := by
  rw [div_im, pair_re, pair_im, unit_re, unit_im,
    length, normSq_eq_norm_sq, Real.sin_two_mul]
  ring

theorem direction_derivative_bound {φ r L : ℝ} (hr : |r| ≤ 1) (hL : 1 ≤ L) :
    |r * Real.sin (2 * φ) / L ^ 2| ≤ 2 * |φ| := by
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg L)]
  have hs : |Real.sin (2 * φ)| ≤ 2 * |φ| := by
    simpa only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] using (Real.abs_sin_le_abs (x := 2 * φ))
  have hm := mul_le_mul hr hs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have hsq : 1 ≤ L ^ 2 := by nlinarith
  calc
    _ ≤ (2 * |φ|) / L ^ 2 := div_le_div_of_nonneg_right (by simpa only [one_mul] using hm) (sq_nonneg _)
    _ ≤ _ := div_le_self (by positivity) hsq

/-- An individual radius changes the adjacent length at speed at most one and
the adjacent direction at speed at most twice the half-angle. -/
theorem individual_derivative_bounds {φ r₀ r₁ : ℝ}
    (h : 1 ≤ (pair φ r₀ r₁).re) (h₀ : |r₀| ≤ 1) (h₁ : |r₁| ≤ 1) :
    |length φ r₀ r₁ * (unit (-φ) / pair φ r₀ r₁).re| ≤ 1 ∧
    |length φ r₀ r₁ * (unit φ / pair φ r₀ r₁).re| ≤ 1 ∧
    |(unit (-φ) / pair φ r₀ r₁).im| ≤ 2 * |φ| ∧
    |(unit φ / pair φ r₀ r₁).im| ≤ 2 * |φ| := by
  have hL : 1 ≤ length φ r₀ r₁ := h.trans (re_le_norm _)
  refine ⟨length_derivative_bound (by change 0 < length φ r₀ r₁; linarith) (norm_unit _),
    length_derivative_bound (by change 0 < length φ r₀ r₁; linarith) (norm_unit _), ?_, ?_⟩
  · rw [left_direction_derivative]
    have hh := direction_derivative_bound (φ := φ) (r := -r₁) (by simpa only [abs_neg] using h₁) hL
    exact hh
  · rw [right_direction_derivative]
    exact direction_derivative_bound h₀ hL

end
end StructuralNote.MatchingActivityRadialBounds
