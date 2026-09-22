import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Pairwise radial control from support inequalities; no boundary differentiation. -/

namespace Erdos1045.EventualExact.RadialControl

noncomputable section

theorem radius_difference_le {R S ρ x t : ℝ} (hρ : 0 ≤ ρ)
    (hS : 0 ≤ S) (hShi : S ≤ 5 / 4) (hspread : S - R ≤ 2 * ρ)
    (ht : |t| ≤ 8 * Real.sqrt ρ)
    (hsupport : S * (Real.cos x - t * Real.sin x) ≤ R) :
    S - R ≤ 12 * Real.sqrt ρ * |x| := by
  have hr := Real.sqrt_nonneg ρ
  have hrsq := Real.sq_sqrt hρ
  by_cases hx : Real.sqrt ρ ≤ |x|
  · have hm := mul_le_mul_of_nonneg_left hx hr
    nlinarith [mul_nonneg hr (abs_nonneg x)]
  · have hx' : |x| ≤ Real.sqrt ρ := (lt_of_not_ge hx).le
    have hs : t * Real.sin x ≤ 8 * Real.sqrt ρ * |x| := by
      calc
        _ ≤ |t * Real.sin x| := le_abs_self _
        _ = |t| * |Real.sin x| := abs_mul _ _
        _ ≤ _ := mul_le_mul ht Real.abs_sin_le_abs (abs_nonneg _) (by positivity)
    have hc := Real.one_sub_sq_div_two_le_cos (x := x)
    have hcomb : 1 - x ^ 2 / 2 - 8 * Real.sqrt ρ * |x| ≤
        Real.cos x - t * Real.sin x := by linarith
    have hm := mul_le_mul_of_nonneg_left hcomb hS
    have hsrad : S - R ≤ S * (x ^ 2 / 2 + 8 * Real.sqrt ρ * |x|) := by
      nlinarith
    have hx2 : x ^ 2 ≤ Real.sqrt ρ * |x| := by
      have hm' := mul_le_mul_of_nonneg_right hx' (abs_nonneg x)
      nlinarith [sq_abs x]
    have hinner : x ^ 2 / 2 + 8 * Real.sqrt ρ * |x| ≤
        9 * Real.sqrt ρ * |x| := by nlinarith [mul_nonneg hr (abs_nonneg x)]
    have hh := mul_le_mul hShi hinner (by positivity) (by norm_num : (0 : ℝ) ≤ 5 / 4)
    nlinarith [mul_nonneg hr (abs_nonneg x)]

theorem abs_radius_difference_le {R S ρ x t u : ℝ} (hρ : 0 ≤ ρ)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hRhi : R ≤ 5 / 4) (hShi : S ≤ 5 / 4)
    (hspread : |S - R| ≤ 2 * ρ)
    (ht : |t| ≤ 8 * Real.sqrt ρ) (hu : |u| ≤ 8 * Real.sqrt ρ)
    (hfirst : S * (Real.cos x - t * Real.sin x) ≤ R)
    (hsecond : R * (Real.cos (-x) - u * Real.sin (-x)) ≤ S) :
    |S - R| ≤ 12 * Real.sqrt ρ * |x| := by
  apply abs_le.mpr
  constructor
  · have h := radius_difference_le hρ hR hRhi
      (show R - S ≤ 2 * ρ by linarith [(abs_le.mp hspread).1]) hu hsecond
    rw [abs_neg] at h
    linarith
  · exact radius_difference_le hρ hS hShi (abs_le.mp hspread).2 ht hfirst

theorem log_difference_le {R S : ℝ} (hR : 1 / 4 ≤ R) (hS : 1 / 4 ≤ S)
    (hRS : R ≤ S) : Real.log S - Real.log R ≤ 4 * (S - R) := by
  have hR0 : 0 < R := by linarith
  have hS0 : 0 < S := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hS0 hR0)
  rw [Real.log_div hS0.ne' hR0.ne'] at hl
  have hd : S / R - 1 = (S - R) / R := by field_simp
  rw [hd] at hl
  have hh : (S - R) / R ≤ 4 * (S - R) := by
    apply (div_le_iff₀ hR0).mpr
    have hm := mul_le_mul_of_nonneg_right hR (sub_nonneg.mpr hRS)
    nlinarith
  exact hl.trans hh

theorem abs_log_difference_le {R S : ℝ} (hR : 1 / 4 ≤ R) (hS : 1 / 4 ≤ S) :
    |Real.log S - Real.log R| ≤ 4 * |S - R| := by
  rcases le_total R S with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_difference_le hR hS h
  · rw [abs_sub_comm (Real.log S), abs_sub_comm S,
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log (by linarith) h)),
      abs_of_nonneg (sub_nonneg.mpr h)]
    exact log_difference_le hS hR h

theorem abs_log_difference_le_support {R S ρ x t u : ℝ} (hρ : 0 ≤ ρ)
    (hR : 1 / 4 ≤ R) (hS : 1 / 4 ≤ S) (hRhi : R ≤ 5 / 4) (hShi : S ≤ 5 / 4)
    (hspread : |S - R| ≤ 2 * ρ)
    (ht : |t| ≤ 8 * Real.sqrt ρ) (hu : |u| ≤ 8 * Real.sqrt ρ)
    (hfirst : S * (Real.cos x - t * Real.sin x) ≤ R)
    (hsecond : R * (Real.cos (-x) - u * Real.sin (-x)) ≤ S) :
    |Real.log S - Real.log R| ≤ 48 * Real.sqrt ρ * |x| := by
  have hr := abs_radius_difference_le hρ (by linarith) (by linarith)
    hRhi hShi hspread ht hu hfirst hsecond
  have hl := abs_log_difference_le hR hS
  linarith

end
end Erdos1045.EventualExact.RadialControl
