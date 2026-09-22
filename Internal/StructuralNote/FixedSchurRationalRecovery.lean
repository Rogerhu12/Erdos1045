import StructuralNote.CommonRationalRecovery
import StructuralNote.FixedSchurRationalWindowDomain
import StructuralNote.FixedSchurEdgeGeometry

/-! Explicit rational parameters recovered from physical selected crossings.
This is an algebraic inverse in the base-edge gauge, not an identification of
the old tangential free variable with the fixed-Schur free variable. -/

namespace StructuralNote.FixedSchurRationalRecovery

open Complex Erdos1045 Erdos1045.EventualExact LensClosure
open FiniteFourierLift FourierMultiplier SchurSpectrum CommonClosureEnergy
open CommonFiberGeometry CommonRationalChart RationalCommonConfiguration
open FixedSchurRationalWindowDomain FixedSchurEdgeGeometry
open CommonTangentialParameters
open scoped BigOperators
noncomputable section

def relativeCrossing {m : ℕ} (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ) (j : Fin m) : ℂ :=
  unit (-midpoint m j) * unit (-initialAngle (by omega) θ) *
    (crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j) / 2)

def parameters {m : ℕ} (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
    (θ : Fin (2 * m) → ℝ) (C : Fin (2 * m) → ℂ) :
    RationalConfiguration.Variables m → ℝ :=
  RationalParameterRecovery.parameters (relativeAngle (by omega) θ)
    (relativeCrossing hm s θ C)

theorem relativeCrossing_norm {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ) (j : Fin m)
    (hcross : ‖crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j)‖ = 2) :
    ‖relativeCrossing hm s θ C j‖ = 1 := by
  simp only [relativeCrossing, norm_mul, norm_unit, one_mul, norm_div, hcross]
  norm_num

theorem recovery_angle {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (ha : ∀ j, |relativeAngle (by omega) θ j| < Real.pi) (j : Fin (2 * m)) :
    RationalAngleBranch.angle (by omega) (parameters hm s θ C) j =
      θ j - initialAngle (by omega) θ := by
  rw [parameters, RationalParameterRecovery.angle_parameters (by omega) _ _
    (relativeAngle_zero (by omega) θ) ha]
  rw [relativeAngle, half_value (by omega) θ hθ]

theorem recovery_angleMean {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle (by omega) θ j| < Real.pi) :
    angleMean (by omega) (parameters hm s θ C) = -initialAngle (by omega) θ := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  unfold angleMean
  have he (j : Fin m) : RationalAngleBranch.angle (by omega) (parameters hm s θ C) j =
      θ (halfIndex j) - initialAngle (by omega) θ :=
    recovery_angle hm s θ C hθ ha (halfIndex j)
  simp_rw [he]
  rw [Finset.sum_sub_distrib, CommonRationalRecovery.half_sum_zero (by omega) θ hθ hmean,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem recovery_theta {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle (by omega) θ j| < Real.pi) :
    theta (by omega) (parameters hm s θ C) = θ := by
  funext j
  rw [theta, recovery_angle hm s θ C hθ ha,
    recovery_angleMean hm s θ C hθ hmean ha]
  ring

theorem recovery_diameter {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle (by omega) θ j| < Real.pi) (j : Fin (2 * m)) :
    RationalConfiguration.diameter (by omega) (parameters hm s θ C) j =
      unit (-initialAngle (by omega) θ) * diameterVector θ j := by
  have he := normalized_diameter (by omega : 0 < m) (parameters hm s θ C) j
  rw [recovery_theta hm s θ C hθ hmean ha,
    recovery_angleMean hm s θ C hθ hmean ha, neg_neg] at he
  rw [he, ← mul_assoc, ← unit_add]
  simp [unit]

theorem recovery_crossingUnit {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hcross : ∀ j : Fin m,
      ‖crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j)‖ = 2)
    (hR : ∀ j, 0 < 1 + (relativeCrossing hm s θ C j).re) (j : Fin m) :
    RationalConfiguration.crossingUnit (parameters hm s θ C) j =
      unit (-initialAngle (by omega) θ) *
        (crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j) / 2) := by
  rw [parameters, RationalParameterRecovery.crossingUnit_parameters _ _
    (fun j => relativeCrossing_norm hm s θ C j (hcross j)) hR]
  simp only [relativeCrossing]
  rw [← mul_assoc, ← mul_assoc, ← unit_add]
  simp [unit]

theorem recovery_increment {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle (by omega) θ j| < Real.pi)
    (hcross : ∀ j : Fin m,
      ‖crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j)‖ = 2)
    (hR : ∀ j, 0 < 1 + (relativeCrossing hm s θ C j).re) (j : Fin m) :
    RationalConfiguration.increment (by omega) (rationalSign s) (parameters hm s θ C) j =
      unit (-initialAngle (by omega) θ) * difference (by omega) C (halfIndex j) := by
  have hd := recovery_diameter hm s θ C hθ hmean ha (halfIndex j)
  have he := recovery_diameter hm s θ C hθ hmean ha (successor (by omega) (halfIndex j))
  rw [successor_half_val (by omega : 0 < m) j] at he
  change RationalConfiguration.diameter (by omega) (parameters hm s θ C) j.val = _ at hd
  rw [RationalConfiguration.increment, RationalChart.crossingIncrement,
    recovery_crossingUnit hm s θ C hcross hR, hd, he]
  have hsign : rationalSign s j = 1 ∨ rationalSign s j = -1 :=
    FiniteBox.patternSign_is_sign s _
  have hs : FiniteBox.patternSign s (halfIndex j) = rationalSign s j := rfl
  simp only [crossingVector, difference, hs]
  rcases hsign with hsign | hsign <;> rw [hsign] <;> push_cast <;> ring

theorem recovery_closure {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle (by omega) θ j| < Real.pi)
    (hC : HalfPeriodic (by omega) C)
    (hcross : ∀ j : Fin m,
      ‖crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j)‖ = 2)
    (hR : ∀ j, 0 < 1 + (relativeCrossing hm s θ C j).re) :
    RationalConfiguration.closure (by omega) (rationalSign s) (parameters hm s θ C) = 0 := by
  unfold RationalConfiguration.closure
  simp_rw [recovery_increment hm s θ C hθ hmean ha hcross hR]
  have hs : (∑ j : Fin m, difference (by omega) C (halfIndex j)) = 0 := by
    simpa only [CommonClosureEnergy.halfIndex, BoxLensLift.halfIndex] using
      half_difference_sum (by omega) C hC
  rw [← Finset.mul_sum, hs, mul_zero]

theorem recovery_center {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega)) (θ : Fin (2 * m) → ℝ)
    (C : Fin (2 * m) → ℂ)
    (hθ : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hmean : ∑ j, (θ j : ℂ) = 0)
    (ha : ∀ j, |relativeAngle (by omega) θ j| < Real.pi)
    (hC : HalfPeriodic (by omega) C) (hCmean : ∑ j, C j = 0)
    (hcross : ∀ j : Fin m,
      ‖crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j)‖ = 2)
    (hR : ∀ j, 0 < 1 + (relativeCrossing hm s θ C j).re) :
    normalizedCenter (by omega) (rationalSign s) (parameters hm s θ C) = C := by
  have hclosure := recovery_closure hm s θ C hθ hmean ha hC hcross hR
  have hd : difference (by omega)
      (normalizedCenter (by omega) (rationalSign s) (parameters hm s θ C)) =
      difference (by omega) C := by
    apply eq_of_half_restriction (by omega)
      (difference_halfPeriodic (by omega) _ (normalizedCenter_halfPeriodic _ _ _))
      (difference_halfPeriodic (by omega) C hC)
    intro j
    change difference (by omega)
      (normalizedCenter (by omega) (rationalSign s) (parameters hm s θ C))
      (halfIndex j) = difference (by omega) C (halfIndex j)
    rw [normalizedCenter_half_difference (by omega) _ _ hclosure j,
      recovery_increment hm s θ C hθ hmean ha hcross hR,
      recovery_angleMean hm s θ C hθ hmean ha, neg_neg,
      ← mul_assoc, ← unit_add]
    simp [unit]
  exact (integral_unique (by omega) _ _ (normalizedCenter_mean_zero _ _ _) hd).trans
    (integral_unique (by omega) _ C hCmean rfl).symm

end
end StructuralNote.FixedSchurRationalRecovery

