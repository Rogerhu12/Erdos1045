import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-! Explicit scalar estimates for the even-order threshold. -/

namespace Erdos1045.ExplicitThreshold

noncomputable section

def threshold : ℕ := 2 ^ 100000

def logBudget (x : ℝ) : ℝ := 1 + Real.log x

def errorBudget (x : ℝ) : ℝ :=
  10 ^ 30 * logBudget x ^ 10 * x ^ (-(1 / 4 : ℝ))

/-- A uniform comparison for the logarithmic error profile, without a derivative. -/
theorem profile_antitone {a t : ℝ} (ha : 39 ≤ a) (hat : a ≤ t) :
    (1 + t) ^ 10 * Real.exp (-t / 4) ≤
      (1 + a) ^ 10 * Real.exp (-a / 4) := by
  have ha0 : 0 ≤ 1 + a := by linarith
  have ht0 : 0 ≤ 1 + t := by linarith
  have he := Real.add_one_le_exp ((t - a) / 40)
  have hm := mul_le_mul_of_nonneg_left he ha0
  have hprod : 0 ≤ (t - a) * (a - 39) := mul_nonneg (sub_nonneg.mpr hat) (by linarith)
  have hlin : 1 + t ≤ (1 + a) * Real.exp ((t - a) / 40) := by nlinarith
  have hp := pow_le_pow_left₀ ht0 hlin 10
  have hmul := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-t / 4)).le
  rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add] at hmul
  have hid : (10 : ℝ) * ((t - a) / 40) + -t / 4 = -a / 4 := by ring
  simpa only [Nat.cast_ofNat, hid] using hmul

theorem errorBudget_eq_profile {x : ℝ} (hx : 0 < x) :
    errorBudget x = 10 ^ 30 * ((1 + Real.log x) ^ 10 * Real.exp (-Real.log x / 4)) := by
  rw [errorBudget, logBudget, Real.rpow_def_of_pos hx]
  rw [show Real.log x * -(1 / 4 : ℝ) = -Real.log x / 4 by ring]
  ring

theorem errorBudget_antitone {x y : ℝ} (hx : 0 < x)
    (hlog : 39 ≤ Real.log x) (hxy : x ≤ y) : errorBudget y ≤ errorBudget x := by
  rw [errorBudget_eq_profile (hx.trans_le hxy), errorBudget_eq_profile hx]
  exact mul_le_mul_of_nonneg_left
    (profile_antitone hlog (Real.log_le_log hx hxy)) (by positivity)

theorem threshold_pos : 0 < threshold := by
  exact pow_pos (by norm_num) _

theorem threshold_cast : (threshold : ℝ) = (2 : ℝ) ^ 100000 := by
  simp only [threshold, Nat.cast_pow, Nat.cast_ofNat]

theorem log_threshold : Real.log (threshold : ℝ) = 100000 * Real.log 2 := by
  rw [threshold_cast, Real.log_pow]
  norm_cast

theorem log_two_lower : (2 / 3 : ℝ) < Real.log 2 := by
  linarith [Real.log_two_gt_d9]

theorem log_two_upper : Real.log 2 < 1 := by
  linarith [Real.log_two_lt_d9]

theorem log_lower {n : ℕ} (hn : threshold ≤ n) :
    (200000 / 3 : ℝ) < Real.log (n : ℝ) := by
  have hp : (0 : ℝ) < threshold := by exact_mod_cast threshold_pos
  have he := Real.log_le_log hp (show (threshold : ℝ) ≤ n by exact_mod_cast hn)
  rw [log_threshold] at he
  linarith [log_two_lower]

theorem endpoint_numerator :
    (10 : ℝ) ^ 30 * logBudget (threshold : ℝ) ^ 10 < (2 : ℝ) ^ 270 := by
  have hH : logBudget (threshold : ℝ) < (2 : ℝ) ^ 17 := by
    rw [logBudget, log_threshold]
    have := log_two_upper
    norm_num
    linarith
  have hHpos : 0 < logBudget (threshold : ℝ) := by
    rw [logBudget, log_threshold]
    linarith [log_two_lower]
  have hp : logBudget (threshold : ℝ) ^ 10 < ((2 : ℝ) ^ 17) ^ 10 :=
    pow_lt_pow_left₀ hH hHpos.le (by norm_num)
  have hnum : (10 : ℝ) ^ 30 < (2 : ℝ) ^ 100 := by norm_num
  calc
    _ < (2 : ℝ) ^ 100 * ((2 : ℝ) ^ 17) ^ 10 :=
      mul_lt_mul hnum hp.le (pow_pos hHpos _) (by positivity)
    _ = (2 : ℝ) ^ 270 := by rw [← pow_mul, ← pow_add]

/-- The paper's exponentially small bound, valid at every order above the threshold. -/
theorem errorBudget_lt {n : ℕ} (hn : threshold ≤ n) :
    errorBudget (n : ℝ) < (2 : ℝ) ^ (-(24730 : ℝ)) := by
  have hp : (0 : ℝ) < threshold := by exact_mod_cast threshold_pos
  have hlo : 39 ≤ Real.log (threshold : ℝ) := by
    rw [log_threshold]
    linarith [log_two_lower]
  have hmono := errorBudget_antitone hp hlo
    (show (threshold : ℝ) ≤ n by exact_mod_cast hn)
  apply lt_of_le_of_lt hmono
  rw [errorBudget, Real.rpow_def_of_pos hp, log_threshold]
  have he := mul_lt_mul_of_pos_right endpoint_numerator
    (Real.exp_pos ((100000 * Real.log 2) * -(1 / 4 : ℝ)))
  apply lt_of_lt_of_eq he
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul,
    ← Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  norm_num
  ring

theorem two_le_order {n : ℕ} (hn : threshold ≤ n) : 2 ≤ n := by
  apply le_trans (b := threshold) ?_ hn
  change (2 : ℕ) ^ 1 ≤ 2 ^ 100000
  exact pow_le_pow_right₀ (by decide) (by decide)

theorem logBudget_ge_one {n : ℕ} (hn : threshold ≤ n) :
    1 ≤ logBudget (n : ℝ) := by
  dsimp [logBudget]
  linarith [log_lower hn]

/-- The numerical smallness bound used throughout the analytic estimates. -/
theorem errorBudget_lt_millionth {n : ℕ} (hn : threshold ≤ n) :
    errorBudget (n : ℝ) < 1 / 1000000 := by
  have hpow : (2 : ℝ) ^ (-(24730 : ℝ)) ≤ (2 : ℝ) ^ (-(20 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hsmall : (2 : ℝ) ^ (-(20 : ℝ)) < 1 / 1000000 := by
    rw [Real.rpow_neg (by norm_num), show (20 : ℝ) = (20 : ℕ) by rfl,
      Real.rpow_natCast]
    norm_num
  exact (errorBudget_lt hn).trans_le hpow |>.trans hsmall

/-- All smaller coefficients and logarithmic powers, and all faster decay rates,
are controlled by the same error budget. -/
theorem monomial_le_errorBudget {n j : ℕ} {c α : ℝ} (hn : threshold ≤ n)
    (hc : c ≤ 10 ^ 30) (hj : j ≤ 10) (hα : (1 / 4 : ℝ) ≤ α) :
    c * logBudget (n : ℝ) ^ j * (n : ℝ) ^ (-α) ≤ errorBudget (n : ℝ) := by
  have hH := logBudget_ge_one hn
  have hH0 : 0 ≤ logBudget (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by have := two_le_order hn; omega)
  have hp := pow_le_pow_right₀ hH hj
  have hr := Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hα)
  exact mul_le_mul (mul_le_mul hc hp (pow_nonneg hH0 _) (by positivity))
    hr (by positivity) (by positivity)

theorem monomial_lt_millionth {n j : ℕ} {c α : ℝ} (hn : threshold ≤ n)
    (hc : c ≤ 10 ^ 30) (hj : j ≤ 10) (hα : (1 / 4 : ℝ) ≤ α) :
    c * logBudget (n : ℝ) ^ j * (n : ℝ) ^ (-α) < 1 / 1000000 :=
  (monomial_le_errorBudget hn hc hj hα).trans_lt (errorBudget_lt_millionth hn)

def logOrder (n : ℕ) : ℕ := ⌈Real.log n / Real.log 2⌉₊

theorem logOrder_lower {n : ℕ} (hn : threshold ≤ n) : 100000 ≤ logOrder n := by
  have hp : (0 : ℝ) < threshold := by exact_mod_cast threshold_pos
  have hh := Real.log_le_log hp (show (threshold : ℝ) ≤ n by exact_mod_cast hn)
  rw [log_threshold] at hh
  have hlog2 : 0 < Real.log 2 := by linarith [log_two_lower]
  have he : (100000 : ℝ) ≤ Real.log n / Real.log 2 := (le_div_iff₀ hlog2).mpr hh
  have hc : Real.log n / Real.log 2 ≤ (logOrder n : ℝ) := Nat.le_ceil _
  exact_mod_cast he.trans hc

theorem logOrder_upper {n : ℕ} (hn : threshold ≤ n) :
    (logOrder n : ℝ) ≤ 2 * logBudget (n : ℝ) := by
  have hl : 0 ≤ Real.log (n : ℝ) := by linarith [log_lower hn]
  have hlog2 : 0 < Real.log 2 := by linarith [log_two_lower]
  have hc := Nat.ceil_lt_add_one (div_nonneg hl hlog2.le)
  have hd : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
    apply (div_le_iff₀ hlog2).mpr
    nlinarith only [hl, log_two_lower]
  change (⌈Real.log n / Real.log 2⌉₊ : ℝ) ≤ 2 * (1 + Real.log n)
  linarith

/-- The original logarithmic branch selector contains the fixed energy budget. -/
theorem selector_budget {n : ℕ} (hn : threshold ≤ n) :
    (10 : ℝ) ^ 9 < 10 ^ 10 ∧ (10 : ℝ) ^ 10 ≤ (logOrder n : ℝ) ^ 2 := by
  constructor
  · norm_num
  · have hh : (100000 : ℝ) ≤ logOrder n := by exact_mod_cast logOrder_lower hn
    nlinarith only [hh]

/-- The nondecaying comparison excluding microscopic holes. -/
theorem microscopic_hole_budget {n : ℕ} (hn : threshold ≤ n) :
    2000000 < 36 * (Real.log (n : ℝ) - 60) := by
  linarith [log_lower hn]

/-- The nondecaying term in the original positive lens-curvature estimate. -/
theorem logarithmic_curvature_margin {n : ℕ} (hn : threshold ≤ n) :
    501 < Real.log (n : ℝ) := by
  linarith [log_lower hn]

/-- A convenient square-root denominator form of the uniform bound. -/
theorem sqrt_monomial_lt {n j : ℕ} {c : ℝ} (hn : threshold ≤ n)
    (hc : c ≤ 10 ^ 30) (hj : j ≤ 10) :
    c * logBudget (n : ℝ) ^ j / Real.sqrt n < 1 / 1000000 := by
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg n)]
  exact monomial_lt_millionth hn hc hj (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)

/-- Both local coordinate smallness requirements follow from the explicit rate. -/
theorem localization_small {n : ℕ} {η : ℝ} (hn : threshold ≤ n)
    (hη : η ≤ 10 ^ 4 * logBudget (n : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ))) :
    η ≤ 1 / 1500 ∧ η * logBudget (n : ℝ) ≤ 1 / 40 := by
  have h₁ := monomial_lt_millionth (j := 1) (c := 10 ^ 4) hn
    (by norm_num) (by norm_num) (le_refl (1 / 4 : ℝ))
  have h₂ := monomial_lt_millionth (j := 2) (c := 10 ^ 4) hn
    (by norm_num) (by norm_num) (le_refl (1 / 4 : ℝ))
  rw [pow_one] at h₁
  have hH : 0 ≤ logBudget (n : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans (logBudget_ge_one hn)
  have hm := mul_le_mul_of_nonneg_right hη hH
  constructor
  · linarith only [hη, h₁]
  · nlinarith only [hm, h₂]

/-- The scalar closure condition on the full logarithmically growing domain. -/
theorem closure_coefficient_small {n : ℕ} (hn : threshold ≤ n) :
    900000000 * logBudget (n : ℝ) ^ 3 / Real.sqrt n < 1 / 1000 := by
  have h := sqrt_monomial_lt (j := 3) (c := 900000000) hn (by norm_num) (by norm_num)
  linarith only [h]

/-- The scalar Hessian error is less than one sixth. -/
theorem hessian_coefficient_small {n : ℕ} (hn : threshold ≤ n) :
    162000000000 * logBudget (n : ℝ) ^ 5 / Real.sqrt n < 1 / 6 := by
  have h := sqrt_monomial_lt (j := 5) (c := 162000000000) hn (by norm_num) (by norm_num)
  linarith only [h]

/-- Positivity of the displayed logarithmic lens-curvature lower bound. -/
theorem lens_curvature_bound_pos {n : ℕ} (hn : threshold ≤ n) :
    0 < (2 * Real.log (n : ℝ) - 1000 - 10 ^ 12 * logBudget (n : ℝ) / n) /
      (n : ℝ) ^ 2 := by
  have hs := monomial_lt_millionth (j := 1) (c := 10 ^ 12) (α := 1) hn
    (by norm_num) (by norm_num) (by norm_num)
  rw [pow_one, Real.rpow_neg_one, ← div_eq_mul_inv] at hs
  have hlog := logarithmic_curvature_margin hn
  have hp : (0 : ℝ) < n := by exact_mod_cast threshold_pos.trans_le hn
  apply div_pos ?_ (sq_pos_of_pos hp)
  linarith only [hs, hlog]

/-- The absolute comparison error is smaller than the integer energy gap. -/
theorem comparison_error_below_gap {n : ℕ} (hn : threshold ≤ n) :
    (10 : ℝ) ^ 25 * (n : ℝ) ^ (-(5 / 2 : ℝ)) < 1 / (n : ℝ) ^ 2 := by
  have hs := sqrt_monomial_lt (j := 0) (c := 10 ^ 25) hn (by norm_num) (by norm_num)
  simp only [pow_zero, mul_one] at hs
  have hp : (0 : ℝ) < n := by exact_mod_cast threshold_pos.trans_le hn
  have he : (n : ℝ) ^ (-(5 / 2 : ℝ)) = (Real.sqrt n)⁻¹ / (n : ℝ) ^ 2 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hp.le]
    change (n : ℝ) ^ (-(5 / 2 : ℝ)) =
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * ((n : ℝ) ^ 2)⁻¹
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_neg hp.le, ← Real.rpow_add hp]
    congr 1
    norm_num
  rw [he, ← mul_div_assoc]
  apply (div_lt_div_iff_of_pos_right (sq_pos_of_pos hp)).mpr
  rw [← div_eq_mul_inv]
  linarith only [hs]

end
end Erdos1045.ExplicitThreshold
