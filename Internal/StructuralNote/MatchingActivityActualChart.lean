import StructuralNote.MatchingActivityCrossingVariationSaturation
import StructuralNote.FixedSchurLogBoundedRepresentation
import StructuralNote.FixedSchurRationalWindowEnergy
import StructuralNote.MatchingActivityRadialModelEnergy
import StructuralNote.CommonFiberSchurExpansion

/-! The physical-center energy and normal-coordinate inputs for entering the
fixed-Schur chart from an actual maximizer.  The center used here is the
mean-zero physical `actualCenter`, not the corrected `polarCenter`. -/

namespace StructuralNote.MatchingActivityActualChart

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open AngularObjectiveCurvature
open MatchingActivityRadialIntegration MatchingActivityRadialModelEnergy
open MatchingActivityNonlocalPairs MatchingActivityRadialActual
open StrongPointwiseCoordinates StrongBudgetConsequences StrongObjectiveEstimate
open StrongPointwiseSteps SinglePressureEstimate SignedPressureRemainder
open NormalizedPolarRepresentation ExtremalPolarCenter
open FixedSchurLinear FixedSchurProjectionDomain FixedSchurRationalWindowEnergy
open CommonFiberNormalProjectionScaled EdgeCoordinates
open CommonFiberSchurExpansion
open scoped BigOperators Topology
noncomputable section

/-- Translation-normalize a center without changing any edge coordinate. -/
def centerZero {n : ℕ} (C : Fin n → ℂ) : Fin n → ℂ :=
  fun j => C j - average C

theorem centerZero_sum {n : ℕ} (hn : 0 < n) (C : Fin n → ℂ) :
    (∑ j, centerZero C j) = 0 := by
  exact sub_average_sum hn C

theorem centerZero_halfPeriodic {m : ℕ} (hm : 0 < m) (C : Fin (2 * m) → ℂ)
    (hC : HalfPeriodic hm C) : HalfPeriodic hm (centerZero C) := by
  intro j
  simp only [centerZero]
  rw [hC j]

theorem centerZero_pairEnergy {n : ℕ} (hn : 0 < n) (C : Fin n → ℂ) :
    pairEnergy hn (centerZero C) = pairEnergy hn C := by
  rw [pairEnergy_eq_chord_sum, pairEnergy_eq_chord_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  simp only [centerZero]
  ring

theorem centerZero_difference {n : ℕ} (hn : 0 < n) (C : Fin n → ℂ)
    (j : Fin n) : difference hn (centerZero C) j = difference hn C j := by
  unfold centerZero difference
  ring

theorem projection_add {m : ℕ} (hm : 2 ≤ m) (C D : Fin (2 * m) → ℂ) :
    projection hm (C + D) = projection hm C + projection hm D := by
  unfold projection
  rw [constraint_add (show 2 ≤ 2 * m by omega), canonicalLift_add]
  funext j
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The physical mean-zero center splits into the corrected polar center plus
the mean-zero derotation error. -/
theorem centerZero_actual_decomposition {m : ℕ} (_hm : 0 < m) (β : ℂ)
    (u : ℕ → ℂ) (hmean : (∑ j, polarCenter m β u j) = 0) :
    centerZero (actualCenter m β u) =
      polarCenter m β u + centerZero (actualCenter m β u - polarCenter m β u) := by
  funext j
  simp only [centerZero, Pi.add_apply, Pi.sub_apply, average,
    Finset.sum_sub_distrib, hmean, sub_zero]
  ring

def actualChartEnergyConstant : ℝ :=
  3 * budgetConstant + 12 * derotationConstant ^ 2

theorem actualChartEnergyConstant_nonneg : 0 ≤ actualChartEnergyConstant := by
  unfold actualChartEnergyConstant
  exact add_nonneg (mul_nonneg (by norm_num) budgetConstant_nonneg)
    (mul_nonneg (by norm_num) (sq_nonneg derotationConstant))

/-- Formula (7.17) for the genuine physical center: angular energy plus the
fixed-Schur free-center energy is `O(n⁻²)` with an explicit fixed constant. -/
theorem model_actual_projection_energy {m : ℕ} (hm : 2 ≤ m)
    {β : ℂ} {u : ℕ → ℂ}
    (hu : Function.Periodic u (2 * m))
    (hc : CenterBounds (m := m) (by omega) β u)
    (hb : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2) :
    pairEnergy (by omega) (fun j => (normalizedAngle m u j : ℂ)) +
        pairEnergy (by omega)
          (projection hm (centerZero (actualCenter m β u))) ≤
      actualChartEnergyConstant / (2 * m : ℝ) ^ 2 := by
  let D := actualCenter m β u - polarCenter m β u
  let D₀ := centerZero D
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun j _ => (hb.2.2.1 j).1)
  have hA0 : 0 ≤ DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) :=
    pairEnergy_nonneg (by omega) _
  have hR0 : 0 ≤ residualEnergy (by omega) (polarCenter m β u) :=
    pairEnergy_nonneg (by omega) _
  have hA : DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hbudget, hτ, hR0]
  have hR : residualEnergy (by omega) (polarCenter m β u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hbudget, hτ, hA0]
  have hDhalf : HalfPeriodic (by omega) D := by
    intro j
    simp only [D, Pi.sub_apply]
    rw [actualCenter_halfPeriodic (by omega) β u hu j, hc.half_periodic j]
  have hD₀half : HalfPeriodic (by omega) D₀ :=
    centerZero_halfPeriodic (by omega) D hDhalf
  have hD₀mean : (∑ j, D₀ j) = 0 := centerZero_sum (by omega) D
  have hderot := model_derotation_sqrt_energy (show 0 < m by omega) β u hb hθ
  have hDE0 : 0 ≤ pairEnergy (by omega) D := pairEnergy_nonneg (by omega) D
  have hDE : pairEnergy (by omega) D ≤ derotationConstant ^ 2 / (2 * m : ℝ) ^ 2 := by
    have hs := Real.sq_sqrt hDE0
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hderot 2
    rw [hs] at hsq
    calc
      _ ≤ (derotationConstant / (2 * m : ℝ)) ^ 2 := hsq
      _ = _ := by ring
  have hprojD := projection_pairEnergy_le_six hm D₀ hD₀half hD₀mean
  have hprojD' : pairEnergy (by omega) (projection hm D₀) ≤
      6 * derotationConstant ^ 2 / (2 * m : ℝ) ^ 2 := by
    rw [centerZero_pairEnergy (by omega) D] at hprojD
    calc
      _ ≤ 6 * pairEnergy (by omega) D := hprojD
      _ ≤ 6 * (derotationConstant ^ 2 / (2 * m : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hDE (by norm_num)
      _ = _ := by ring
  have hdecomp := centerZero_actual_decomposition (show 0 < m by omega) β u hc.mean_zero
  have hprojSplit : projection hm (centerZero (actualCenter m β u)) =
      projection hm (polarCenter m β u) + projection hm D₀ := by
    rw [hdecomp, projection_add]
  have hadd := QuadraticStability.pairEnergy_add_le (show 0 < 2 * m by omega)
    (projection hm (polarCenter m β u)) (projection hm D₀)
  rw [hprojSplit]
  rw [← residualEnergy_eq_projection hm (polarCenter m β u)] at hadd
  change DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) +
      pairEnergy (by omega)
        (projection hm (polarCenter m β u) + projection hm D₀) ≤ _
  unfold actualChartEnergyConstant
  have hcenter : pairEnergy (by omega)
      (projection hm (polarCenter m β u) + projection hm D₀) ≤
      (2 * budgetConstant + 12 * derotationConstant ^ 2) /
        (2 * m : ℝ) ^ 2 := by
    calc
      _ ≤ 2 * residualEnergy (by omega) (polarCenter m β u) +
          2 * pairEnergy (by omega) (projection hm D₀) := hadd
      _ ≤ 2 * (budgetConstant / (2 * m : ℝ) ^ 2) +
          2 * (6 * derotationConstant ^ 2 / (2 * m : ℝ) ^ 2) :=
        add_le_add (mul_le_mul_of_nonneg_left hR (by norm_num))
          (mul_le_mul_of_nonneg_left hprojD' (by norm_num))
      _ = _ := by ring
  calc
    _ ≤ budgetConstant / (2 * m : ℝ) ^ 2 +
        (2 * budgetConstant + 12 * derotationConstant ^ 2) /
          (2 * m : ℝ) ^ 2 := add_le_add hA hcenter
    _ = _ := by ring

/-- Pointwise normal edge coordinates are controlled by the scaled physical
center step. -/
theorem normal_abs_le_scaled_difference {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℂ) (j : Fin n) :
    |EdgeCoordinates.normal (by omega) v j| ≤
      scale n * ‖difference (by omega) v j‖ := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsin : 0 < Real.sin (Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply (div_lt_iff₀ hnR).2
      have hnR2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [Real.pi_pos]
  have hnormal : |EdgeCoordinates.normal (by omega) v j| ≤
      ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
    calc
      _ ≤ ‖(EdgeCoordinates.tangent (by omega) v j : ℂ) -
          I * (EdgeCoordinates.normal (by omega) v j : ℂ)‖ := by
        have h := Complex.abs_im_le_norm
          ((EdgeCoordinates.tangent (by omega) v j : ℂ) -
            I * (EdgeCoordinates.normal (by omega) v j : ℂ))
        simpa only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
          zero_add, zero_sub, abs_neg] using h
      _ = ‖(n : ℂ) * edgeRatio (by omega) v j‖ := by
        rw [EdgeCoordinates.scaled_edgeRatio (by omega) v j]
  have href : ‖difference (by omega) (fun k => character n 1 k) j‖ =
      2 * Real.sin (Real.pi / n) := by
    rw [SchurLift.reference_difference (by omega) j]
    simp only [norm_mul, norm_real, Real.norm_eq_abs, Complex.norm_I,
      FixedSchurData.norm_frame]
    rw [abs_of_pos hsin]
    norm_num
  calc
    _ ≤ ‖(n : ℂ) * edgeRatio (by omega) v j‖ := hnormal
    _ = (n : ℝ) * ‖edgeRatio (by omega) v j‖ := by
      simp only [norm_mul, Complex.norm_natCast]
    _ = (n : ℝ) *
        (‖difference (by omega) v j‖ / (2 * Real.sin (Real.pi / n))) := by
      rw [edgeRatio_eq_difference, norm_div, href]
    _ = scale n * ‖difference (by omega) v j‖ := by
      unfold scale
      field_simp

def actualConstraintConstant : ℝ := physicalStepConstant / 4

theorem actualConstraintConstant_nonneg : 0 ≤ actualConstraintConstant := by
  unfold actualConstraintConstant
  exact div_nonneg MatchingActivityRadialModelEnergy.constants_nonneg.1 (by norm_num)

/-- The actual physical normal coordinate has a fixed sup bound, hence a
fortiori the logarithmic bound required by the representation theorem. -/
theorem model_actual_constraint_log_bound {m : ℕ} (hm : 2 ≤ m)
    {β : ℂ} {u : ℕ → ℂ}
    (hb : PointwiseBounds (m := m) (by omega) β u) :
    ‖constraint (by omega) (centerZero (actualCenter m β u))‖ ≤
      actualConstraintConstant * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
  have hL : 1 ≤ (CommonDomainRadius.logOrder (2 * m) : ℝ) :=
    FixedSchurDomainSmallness.logOrder_one_le (show 2 ≤ 2 * m by omega)
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg actualConstraintConstant_nonneg (by linarith))).2
  intro j
  rw [← normal_eq_constraint hm]
  simp only [Real.norm_eq_abs]
  have hn := normal_abs_le_scaled_difference (show 2 ≤ 2 * m by omega)
    (centerZero (actualCenter m β u)) j
  rw [centerZero_difference (by omega) (actualCenter m β u) j] at hn
  have hs := (scale_bounds (show 2 ≤ 2 * m by omega)).2
  have hstep := hb.2.2.2.2.2.2 j
  have hs' : scale (2 * m) ≤ (2 * m : ℝ) ^ 2 / 4 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hs
  have hmul := mul_le_mul hs' hstep (norm_nonneg _)
    (by positivity : (0 : ℝ) ≤ (2 * m : ℝ) ^ 2 / 4)
  calc
    _ ≤ scale (2 * m) * ‖difference (by omega) (actualCenter m β u) j‖ := hn
    _ ≤ ((2 * m : ℝ) ^ 2 / 4) *
        (physicalStepConstant / (2 * m : ℝ) ^ 2) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmul
    _ = actualConstraintConstant := by
      unfold actualConstraintConstant
      field_simp
    _ ≤ actualConstraintConstant * (CommonDomainRadius.logOrder (2 * m) : ℝ) := by
      nlinarith [actualConstraintConstant_nonneg]

end
end StructuralNote.MatchingActivityActualChart
