import StructuralNote.ExplicitThresholdScalar
import StructuralNote.HessianErrorLimits
import StructuralNote.CommonFiberDifferentialEstimate

/-! Explicit order thresholds for the existing common-fiber Hessian budgets.
The threshold is an unevaluated natural-number expression. -/

namespace StructuralNote.ExplicitHessianThreshold

open CommonDomainRadius HessianErrorLimits HessianComparison
open Erdos1045.ExplicitThreshold

noncomputable section

/-- A fixed expression large enough for the unmodified coarse Hessian constants. -/
def orderThreshold : ℕ := 2 ^ 100000

theorem scalar_threshold {n : ℕ} (hn : orderThreshold ≤ n) : threshold ≤ n := hn

theorem order_pos {n : ℕ} (hn : orderThreshold ≤ n) : (0 : ℝ) < n := by
  exact_mod_cast threshold_pos.trans_le hn

theorem logOrder_bound {n : ℕ} (hn : orderThreshold ≤ n) :
    (CommonDomainRadius.logOrder n : ℝ) ≤ 2 * logBudget (n : ℝ) :=
  logOrder_upper hn

theorem log_monomial_div_small {n j : ℕ} {c : ℝ} (hn : orderThreshold ≤ n)
    (hc : c ≤ 10 ^ 30) (hj : j ≤ 10) :
    c * logBudget (n : ℝ) ^ j / n < 1 / 1000000 := by
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using
    monomial_lt_millionth (α := 1) hn hc hj (by norm_num)

theorem chordError_small {n : ℕ} (hn : orderThreshold ≤ n) :
    chordError n < 1 / 1000000 := by
  have hb := logOrder_bound hn
  have h := log_monomial_div_small (j := 1) (c := 600) hn (by norm_num) (by norm_num)
  simp only [pow_one] at h
  apply lt_of_le_of_lt ?_ h
  unfold chordError
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  linarith only [hb]

theorem phaseError_small {n : ℕ} (hn : orderThreshold ≤ n) :
    phaseError n < 1 / 1000000 := by
  have hb := logOrder_bound hn
  have h := log_monomial_div_small (j := 1) (c := 8) hn (by norm_num) (by norm_num)
  simp only [pow_one] at h
  apply lt_of_le_of_lt ?_ h
  unfold phaseError
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  linarith only [hb]

theorem gradientBound_le {n : ℕ} (hn : orderThreshold ≤ n) :
    gradientBound n ≤ 1200 * logBudget (n : ℝ) ^ 2 := by
  have hb := logOrder_bound hn
  have hp : 0 ≤ logBudget (n : ℝ) := (by norm_num : (0 : ℝ) ≤ 1).trans (logBudget_ge_one hn)
  have hm := mul_le_mul_of_nonneg_right hb hp
  unfold gradientBound
  change 600 * (CommonDomainRadius.logOrder n : ℝ) * logBudget (n : ℝ) ≤ _
  nlinarith only [hm]

theorem gradient_div_small {n : ℕ} (hn : orderThreshold ≤ n) :
    gradientBound n / n < 1 / 1000000 := by
  exact (div_le_div_of_nonneg_right (gradientBound_le hn) (Nat.cast_nonneg n)).trans_lt
    (log_monomial_div_small hn (by norm_num) (by norm_num))

theorem gradient_acceleration_small {n : ℕ} (hn : orderThreshold ≤ n) :
    gradientBound n * accelerationBound n < 2 / 1000000 := by
  have h₁ := log_monomial_div_small (j := 2) (c := 1200000000000) hn
    (by norm_num) (by norm_num)
  have h₂ := sqrt_monomial_lt (j := 2) (c := 1200000000000) hn
    (by norm_num) (by norm_num)
  have ha : 0 ≤ accelerationBound n := by unfold accelerationBound; positivity
  have hb := mul_le_mul_of_nonneg_right (gradientBound_le hn) ha
  have he : 1200 * logBudget (n : ℝ) ^ 2 * accelerationBound n =
      1200000000000 * logBudget (n : ℝ) ^ 2 / n +
      1200000000000 * logBudget (n : ℝ) ^ 2 / Real.sqrt n := by
    unfold accelerationBound
    ring
  rw [he] at hb
  linarith only [h₁, h₂, hb]

/-- Pointwise replacement for `HessianErrorLimits.eventual_error_small`. -/
theorem error_small {n : ℕ} (hn : orderThreshold ≤ n) :
    chordError n ≤ 1 / 2 ∧ errorCoefficient n (chordError n) (1 / 10000)
      (gradientBound n) (accelerationBound n) (phaseError n) ≤ 1 / 64 := by
  have hc := chordError_small hn
  have hp := phaseError_small hn
  have hg := gradient_div_small hn
  have ha := gradient_acceleration_small hn
  constructor
  · linarith only [hc]
  · unfold errorCoefficient
    linarith only [hc, hp, hg, ha]

theorem energyRadius_le_inverse {n : ℕ} (hn : orderThreshold ≤ n) :
    energyRadius n ≤ 1 / (n : ℝ) := by
  have hp := order_pos hn
  have hb := logOrder_bound hn
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg (CommonDomainRadius.logOrder n)) hb 2
  have h := log_monomial_div_small (j := 2) (c := 4) hn (by norm_num) (by norm_num)
  have hnumer : (CommonDomainRadius.logOrder n : ℝ) ^ 2 ≤ n := by
    have hx : 4 * logBudget (n : ℝ) ^ 2 < n := by
      apply (div_lt_one hp).mp
      linarith only [h]
    nlinarith only [hs, hx]
  have hi : 1 / (n : ℝ) = (n : ℝ) / (n : ℝ) ^ 2 := by field_simp
  rw [energyRadius, hi]
  exact div_le_div_of_nonneg_right hnumer (sq_nonneg _)

theorem order_bound {n : ℕ} (hn : orderThreshold ≤ n) :
    10 * (CommonDomainRadius.logOrder n : ℝ) + 1024 ≤ n := by
  have hp := order_pos hn
  have hb := logOrder_bound hn
  have h₁ := log_monomial_div_small (j := 1) (c := 20) hn (by norm_num) (by norm_num)
  have h₂ := log_monomial_div_small (j := 0) (c := 1024) hn (by norm_num) (by norm_num)
  simp only [pow_one] at h₁
  simp only [pow_zero, mul_one] at h₂
  have hs : (20 * logBudget (n : ℝ) + 1024) / n < 1 := by
    rw [add_div]
    linarith only [h₁, h₂]
  have hnum := (div_lt_one hp).mp hs
  linarith only [hb, hnum]

theorem two_fifty_six_le_order {n : ℕ} (hn : orderThreshold ≤ n) : 256 ≤ n := by
  apply le_trans (b := orderThreshold) ?_ hn
  change (2 : ℕ) ^ 8 ≤ 2 ^ 100000
  exact pow_le_pow_right₀ (by decide) (by decide)

/-- Pointwise replacement for the common-fiber geometric size conditions. -/
theorem size_conditions {m : ℕ} (hm : orderThreshold ≤ 2 * m) :
    128 ≤ m ∧ energyRadius (2 * m) ≤ 1 / (2 * m : ℝ) ∧
      10 * (CommonDomainRadius.logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m ∧
      1 ≤ Real.log (2 * m : ℝ) := by
  have hm128 : 128 ≤ m := by have := two_fifty_six_le_order hm; omega
  refine ⟨hm128, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using energyRadius_le_inverse hm
  · simpa only [Nat.cast_mul, Nat.cast_ofNat] using order_bound hm
  · have hl := log_lower hm
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hl
    linarith only [hl]

theorem velocity_coefficient_small {n : ℕ} (hn : orderThreshold ≤ n) :
    10000000000 / (n : ℝ) ≤ (1 / 10000 : ℝ) ^ 2 := by
  have h := log_monomial_div_small (j := 0) (c := 1000000000000) hn
    (by norm_num) (by norm_num)
  simp only [pow_zero, mul_one, div_eq_mul_inv] at h ⊢
  linarith only [h]

end
end StructuralNote.ExplicitHessianThreshold
