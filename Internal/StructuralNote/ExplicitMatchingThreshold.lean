import StructuralNote.ExplicitPressureThreshold
import StructuralNote.ExplicitLocalBudgets

/-! Explicit pointwise coordinate bounds and saturation of matching diameters. -/

namespace StructuralNote.ExplicitMatchingThreshold

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization
open Erdos1045.ExplicitThreshold SinglePressureEstimate StrongObjectiveEstimate
open StrongBudgetConsequences StrongPointwiseNormal StrongPointwiseSteps StrongPointwiseCoordinates
open NormalizedPolarRepresentation ExtremalPolarCenter SchurSpectrum SchurLiftBounds DiscreteEnergy
open MatchingActivityRadialGradient MatchingActivityRadialLowerBound
open MatchingActivityRadialModelCenterError MatchingActivityRadialDiameterError
open MatchingActivityRadialActual MatchingActivitySaturation
open SignedPressureRemainder
noncomputable section

theorem div_pow_le_div {n k : ℕ} {C : ℝ} (hn : 1 ≤ n) (hk : 1 ≤ k) (hC : 0 ≤ C) :
    C / (n : ℝ) ^ k ≤ C / n := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh := pow_le_pow_right₀ hnR hk
  simp only [pow_one] at hh
  exact div_le_div_of_nonneg_left hC (by linarith only [hnR]) hh

def pointwiseThreshold : ℕ :=
  max 16 (max (inverseThreshold (2 * budgetConstant) (1 / 2))
    (max (inverseThreshold angleConstant (1 / 2))
      (max (inverseThreshold centerConstant 1) (inverseThreshold normalConstant 1))))

theorem pointwise_scales {n : ℕ} (hn : pointwiseThreshold ≤ n) :
    16 ≤ n ∧ 2 * budgetConstant / (n : ℝ) ^ 3 ≤ 1 / 2 ∧
    angleConstant / (n : ℝ) ^ 2 ≤ 1 / 2 ∧ centerConstant / (n : ℝ) ≤ 1 ∧
    normalConstant / (n : ℝ) ≤ 1 := by
  simp only [pointwiseThreshold, max_le_iff] at hn
  have hn1 : 1 ≤ n := by omega
  exact ⟨hn.1,
    (div_pow_le_div hn1 (by norm_num : 1 ≤ 3) (mul_nonneg (by norm_num) budgetConstant_nonneg)).trans
      (inverse_small (by norm_num) hn.2.1).le,
    (div_pow_le_div hn1 (by norm_num : 1 ≤ 2) (Real.sqrt_nonneg _)).trans
      (inverse_small (by norm_num) hn.2.2.1).le,
    (inverse_small (by norm_num) hn.2.2.2.1).le,
    (inverse_small (by norm_num) hn.2.2.2.2).le⟩

theorem model_pointwise {m : ℕ} (hm : 8 ≤ m) (hn : pointwiseThreshold ≤ 2 * m)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : DiameterAtMost 2 z)
    (hc : CenterBounds (m := m) (by omega) β u)
    (hq : meanSquare (polarConstraint (m := m) (by omega) β u) ≤ 65 * Real.pi ^ 2)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2) :
    PointwiseBounds (m := m) (by omega) β u := by
  have hs := pointwise_scales hn
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs
  have hnormal := model_normal_bound hm h hz hc hq hbudget hs.2.1 hs.2.2.1 hs.2.2.2.1
  exact model_pointwise_coordinates (by omega) h hz hc hq hbudget hs.2.2.2.2 hnormal

def derivativeThreshold : ℕ :=
  max (inverseThreshold 53 (1 / 32))
    (max (decayThreshold (4 * configurationStepConstant) (1 / 32))
      (max (inverseSqrtThreshold (12 * centerErrorConstant) (1 / 32))
        (inverseThreshold configurationStepConstant (1 / 2))))

theorem derivative_scales {n : ℕ} (hn : derivativeThreshold ≤ n) :
    0 < lowerBound n ∧ configurationStepConstant / (n : ℝ) ≤ 1 / 2 := by
  simp only [derivativeThreshold, max_le_iff] at hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn.1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hc : 0 ≤ configurationStepConstant := by
    unfold configurationStepConstant
    exact add_nonneg diameterStepConstant_nonneg MatchingActivityRadialModelEnergy.constants_nonneg.1
  have h₁ := inverse_small (by norm_num : (0 : ℝ) < 1 / 32) hn.1
  have h₂ := monomial_small (n := n) (j := 1) (mul_nonneg (by norm_num) hc)
    (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num) (by norm_num : (1 / 4 : ℝ) ≤ 1) hn.2.1
  rw [Real.rpow_neg_one, pow_one] at h₂
  have h₃ := inverse_sqrt_small (by norm_num : (0 : ℝ) < 1 / 32) hn.2.2.1
  have hG := (inverse_small (by norm_num : (0 : ℝ) < 1 / 2) hn.2.2.2).le
  have heq : lowerBound n / (n : ℝ) =
      1 / 4 - 53 / (n : ℝ) - 4 * configurationStepConstant * logBudget n / (n : ℝ) -
        12 * centerErrorConstant / Real.sqrt n := by
    have hs := Real.sq_sqrt hn0.le
    have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    unfold lowerBound logBudget
    field_simp
    linear_combination (-48 * centerErrorConstant) * hs
  have hpos : 0 < lowerBound n / (n : ℝ) := by
    rw [heq]
    have h₂' : 4 * configurationStepConstant * logBudget n / (n : ℝ) < 1 / 32 := by
      simpa only [div_eq_mul_inv] using h₂
    linarith only [h₁, h₂', h₃]
  exact ⟨by simpa only [zero_mul] using (lt_div_iff₀ hn0).mp hpos, hG⟩

def saturationThreshold : ℕ := max ExplicitPressureThreshold.smallnessThreshold derivativeThreshold

theorem model_saturated {m : ℕ} (hm : 8 ≤ m) (hn : saturationThreshold ≤ 2 * m)
    {z : Points (2 * m)} {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) (hz : ExtremalNormalization.DiameterExtremal z)
    (hpressure : ‖FourierMultiplier.operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hbounds : PointwiseBounds (m := m) (by omega) β u) :
    ∀ i : Fin m, modelRadii m β u i = 1 := by
  have hs := ExplicitPressureThreshold.coefficients_small ((le_max_left _ _).trans hn)
  have hd := derivative_scales ((le_max_right _ _).trans hn)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs hd
  exact model_matching_saturated hm h hz hpressure hbudget hbounds
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2 hd.2 hd.1

end
end StructuralNote.ExplicitMatchingThreshold
