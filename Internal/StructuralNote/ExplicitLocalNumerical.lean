import StructuralNote.ExplicitMatchingCoordinates
import StructuralNote.ExplicitNumericalBounds

/-! Numerical bounds for the local pressure and matching thresholds. -/
namespace StructuralNote.ExplicitLocalNumerical
open Erdos1045 Erdos1045.EventualExact Erdos1045.ExplicitThreshold
open ExplicitNumericalBounds ExplicitPressureNumerical
open ExplicitGradientThreshold ExplicitLocalBudgets
open StrongBudgetConsequences StrongPointwiseSteps SinglePressureEstimate
open StrongPointwiseNormal StrongPointwiseRadial StrongPointwiseConstraint
open MatchingActivityRadialGradient MatchingActivityRadialModelEnergy
open MatchingActivityRadialModelCenterError MatchingActivityRadialDiameterError
noncomputable section
set_option maxHeartbeats 800000

def localBound : ℕ := 2 ^ 10000

theorem local_le_concrete : localBound ≤ concreteThreshold := by
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num)

theorem inverse_le_local {C ε : ℝ} (h : C / ε ≤ (10 : ℝ) ^ 200) :
    inverseThreshold C ε ≤ localBound := by
  exact (inverse_le_pow10 h).trans ((pow10_le_pow2 201).trans
    (Nat.pow_le_pow_right (by decide) (by norm_num)))

theorem inverseSqrt_le_local {C ε : ℝ} (h : (C / ε) ^ 2 ≤ (10 : ℝ) ^ 200) :
    inverseSqrtThreshold C ε ≤ localBound := by
  exact (inverseSqrt_le_pow10 h).trans ((pow10_le_pow2 201).trans
    (Nat.pow_le_pow_right (by decide) (by norm_num)))

theorem decay_le_local {C ε : ℝ} (hC : |C| ≤ (10 : ℝ) ^ 100)
    (hε : |1 / ε| ≤ (10 : ℝ) ^ 100) : decayThreshold C ε ≤ localBound := by
  exact (decay_le_pow10 hC hε).trans ((pow10_le_pow2 1784).trans
    (Nat.pow_le_pow_right (by decide) (by norm_num)))

theorem pathEnergy_bounds : 0 ≤ pathEnergy ∧ pathEnergy ≤ 10 ^ 8 := by
  constructor
  · unfold pathEnergy; positivity
  · have hp : 32768 * Real.pi ^ 4 + 2688 * Real.pi ^ 2 ≤
        32768 * (4 : ℝ) ^ 4 + 2688 * 4 ^ 2 := by gcongr <;> exact Real.pi_lt_four.le
    unfold pathEnergy
    norm_num at hp ⊢
    linarith only [hp]

theorem path_head_bound : headCutoff pathEnergy (1 / 24) ≤ 10 ^ 15 := by
  have hc : (32 * |pathEnergy| / (1 / 24 : ℝ) ^ 2) ≤ ((10 : ℕ) ^ 15 - 1 : ℕ) := by
    rw [abs_of_nonneg pathEnergy_bounds.1]
    norm_num
    linarith only [pathEnergy_bounds.2]
  unfold headCutoff
  have hh : ⌈32 * |pathEnergy| / (1 / 24 : ℝ) ^ 2⌉₊ ≤ 10 ^ 15 - 1 := Nat.ceil_le.mpr hc
  exact Nat.succ_le_of_lt (lt_of_le_of_lt hh (by norm_num))

theorem pairTolerance_lower : (1 : ℝ) / 10 ^ 18 ≤ pairTolerance pathEnergy (1 / 24) := by
  unfold pairTolerance
  apply le_min (by norm_num)
  have hp : (0 : ℝ) < headCutoff pathEnergy (1 / 24) := by
    exact_mod_cast headCutoff_pos pathEnergy (1 / 24)
  apply (le_div_iff₀ (mul_pos (by norm_num) hp)).mpr
  have hh : (headCutoff pathEnergy (1 / 24) : ℝ) ≤ 10 ^ 15 := by
    exact_mod_cast path_head_bound
  have hmul := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 4 / 10 ^ 18)
  norm_num at hmul ⊢
  linarith only [hmul]

theorem edgeTolerance_lower : (1 : ℝ) / 10 ^ 20 ≤ ExplicitStrongBudget.edgeTolerance := by
  unfold ExplicitStrongBudget.edgeTolerance ExplicitObjectiveThreshold.edgeTolerance
    pathTolerance
  apply le_min _ (by norm_num)
  apply le_min _ (by norm_num)
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).mpr
  apply le_min (by norm_num)
  have h := pairTolerance_lower
  norm_num at h ⊢
  exact h

theorem normal_bound : normalConstant ≤ 10 ^ 19 := by
  have hprod := mul_le_mul center_bound angle_bound
    (by unfold angleConstant; positivity : 0 ≤ angleConstant) (by norm_num)
  have hs := pow_le_pow_left₀ (by unfold angleConstant; positivity : 0 ≤ angleConstant)
    angle_bound 2
  have hπT : Real.pi * angleConstant ≤ 4 * (6 * 10 ^ 8 : ℝ) := by
    gcongr
    · unfold angleConstant; positivity
    · exact Real.pi_lt_four.le
    · exact angle_bound
  have hπ4 : Real.pi ^ 4 ≤ (4 : ℝ) ^ 4 := by gcongr; exact Real.pi_lt_four.le
  unfold normalConstant errorConstant
  norm_num at hprod hs hπT hπ4 ⊢
  linarith only [hprod, hs, hπT, hπ4, budget_bound]

theorem radial_error_bound : radialErrorConstant ≤ 10 ^ 18 := by
  have hs := pow_le_pow_left₀ (by unfold angleConstant; positivity : 0 ≤ angleConstant)
    angle_bound 2
  have hp : Real.pi * angleConstant ≤ 4 * (6 * 10 ^ 8 : ℝ) := by
    gcongr
    · unfold angleConstant; positivity
    · exact Real.pi_lt_four.le
    · exact angle_bound
  unfold radialErrorConstant
  norm_num at hs hp ⊢
  linarith only [hs, hp, budget_bound]

theorem pi_margin : (1 : ℝ) / 100 ≤ 10 - Real.pi ^ 2 := by
  have h : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 := by
    gcongr
    exact Real.pi_lt_d2.le
  norm_num at h ⊢
  linarith only [h]

theorem configuration_step_bound : configurationStepConstant ≤ 10 ^ 18 := by
  unfold configurationStepConstant
  linarith only [diameter_step_bound, physical_step_bound]

theorem inverse_of_bounds {C ε : ℝ} (hC : C ≤ (10 : ℝ) ^ 100)
    (hε : (1 : ℝ) / 10 ^ 50 ≤ ε) : inverseThreshold C ε ≤ localBound := by
  apply inverse_le_local
  have he : 0 < ε := lt_of_lt_of_le (by norm_num) hε
  apply (div_le_iff₀ he).mpr
  nlinarith only [hC, hε]

theorem decay_of_bounds {C ε : ℝ} (hC : |C| ≤ (10 : ℝ) ^ 100)
    (hε : (1 : ℝ) / 10 ^ 50 ≤ ε) : decayThreshold C ε ≤ localBound := by
  apply decay_le_local hC
  have he : 0 < ε := lt_of_lt_of_le (by norm_num) hε
  rw [abs_of_pos (one_div_pos.mpr he)]
  apply (div_le_iff₀ he).mpr
  nlinarith only [hε]

theorem squared_tolerance_lower {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    (1 : ℝ) / 10 ^ 50 ≤ (min 1 ε / 100) ^ 2 := by
  have hmin : (1 : ℝ) / 10 ^ 20 ≤ min 1 ε := le_min (by norm_num) hε
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 20) hmin 2
  norm_num at hs ⊢
  nlinarith only [hs]

theorem size_le_local {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 50 ≤ ε) :
    sizeThreshold ε ≤ localBound := by
  apply decay_of_bounds _ hε
  rw [abs_of_nonneg (by positivity)]
  have hp : 384 * Real.pi ^ 2 ≤ 384 * (4 : ℝ) ^ 2 := by gcongr; exact Real.pi_lt_four.le
  norm_num at hp ⊢
  linarith only [hp]

theorem coordinate_le_local {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    coordinateThreshold ε ≤ localBound := size_le_local (squared_tolerance_lower hε)

theorem pair_le_local {ε : ℝ} (hε : (1 : ℝ) / 10 ^ 20 ≤ ε) :
    pairThreshold ε ≤ localBound := by
  apply max_le (size_le_local (squared_tolerance_lower hε))
  apply inverse_of_bounds
  · have hp : 512 * Real.pi ^ 2 ≤ 512 * (4 : ℝ) ^ 2 := by gcongr; exact Real.pi_lt_four.le
    norm_num at hp ⊢
    linarith only [hp]
  · norm_num at hε ⊢
    linarith only [hε]

theorem objective_le_local : ExplicitObjectiveThreshold.orderThreshold ≤ localBound := by
  have hsmall : 4 ≤ localBound := Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num : 2 ≤ 10000)
  apply max_le hsmall
  apply max_le (pair_le_local (pairTolerance_lower.trans' (by norm_num)))
  apply max_le (coordinate_le_local (by norm_num))
  exact max_le (size_le_local (by norm_num)) (inverse_of_bounds (by norm_num) (by norm_num))

theorem pressure_coordinates_le_local : ExplicitPressureCoordinates.orderThreshold ≤ localBound := by
  have hsmall : 2048 ≤ localBound := Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num : 11 ≤ 10000)
  apply max_le hsmall
  apply max_le (size_le_local (by norm_num))
  have he : (1 : ℝ) / 10 ^ 50 ≤ Real.pi ^ 2 / 2048 / 2 := by
    nlinarith only [Real.pi_gt_three]
  apply max_le
  · apply decay_of_bounds _ he
    rw [abs_of_nonneg (by positivity)]
    have hp : 4352 * 384 * Real.pi ^ 6 ≤ 4352 * 384 * (4 : ℝ) ^ 6 := by
      gcongr; exact Real.pi_lt_four.le
    norm_num at hp ⊢
    linarith only [hp]
  · apply decay_of_bounds _ he
    rw [abs_of_nonneg (by positivity)]
    have hp : 64 * Real.pi ^ 2 * (256 * Real.pi ^ 2) ^ 2 ≤
        64 * (4 : ℝ) ^ 2 * (256 * 4 ^ 2) ^ 2 := by gcongr <;> exact Real.pi_lt_four.le
    norm_num at hp ⊢
    linarith only [hp]

theorem matching_pointwise_le_local : ExplicitMatchingThreshold.pointwiseThreshold ≤ localBound := by
  have hB : 2 * budgetConstant ≤ (10 : ℝ) ^ 100 := by
    norm_num
    linarith only [budget_bound]
  have hsmall : 16 ≤ localBound := Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num : 4 ≤ 10000)
  apply max_le hsmall
  apply max_le (inverse_of_bounds hB (by norm_num))
  apply max_le (inverse_of_bounds (angle_bound.trans (by norm_num)) (by norm_num))
  exact max_le (inverse_of_bounds (center_bound.trans (by norm_num)) (by norm_num))
    (inverse_of_bounds (normal_bound.trans (by norm_num)) (by norm_num))

theorem pressure_smallness_le_local : ExplicitPressureThreshold.smallnessThreshold ≤ localBound := by
  have hB4 : 4 * budgetConstant ≤ (10 : ℝ) ^ 100 := by
    norm_num
    linarith only [budget_bound]
  have hB2 : 2 * budgetConstant ≤ (10 : ℝ) ^ 100 := by
    norm_num
    linarith only [budget_bound]
  have hsmall : 16 ≤ localBound := Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num : 4 ≤ 10000)
  apply max_le hsmall
  apply max_le (inverse_of_bounds hB4 (by norm_num))
  apply max_le (inverse_of_bounds (physical_step_bound.trans (by norm_num)) (by norm_num))
  apply max_le (inverse_of_bounds (radial_error_bound.trans (by norm_num))
    ((by norm_num : (1 : ℝ) / 10 ^ 50 ≤ 1 / 100).trans pi_margin))
  apply max_le (inverse_of_bounds hB2 (by norm_num))
  exact inverse_of_bounds (diameter_step_bound.trans (by norm_num)) (by norm_num)

theorem matching_derivative_le_local : ExplicitMatchingThreshold.derivativeThreshold ≤ localBound := by
  have hC : |4 * configurationStepConstant| ≤ (10 : ℝ) ^ 100 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) configurationStepConstant_nonneg)]
    norm_num
    linarith only [configuration_step_bound]
  apply max_le (inverse_of_bounds (by norm_num) (by norm_num))
  apply max_le (decay_of_bounds hC (by norm_num))
  apply max_le _ (inverse_of_bounds (configuration_step_bound.trans (by norm_num)) (by norm_num))
  apply inverseSqrt_le_local
  have hc : 12 * centerErrorConstant / (1 / 32 : ℝ) ≤ 10 ^ 60 := by
    norm_num
    linarith only [center_error_bound]
  have h0 : (0 : ℝ) ≤ 12 * centerErrorConstant / (1 / 32) := by
    exact div_nonneg (mul_nonneg (by norm_num) centerErrorConstant_nonneg) (by norm_num)
  have hs := pow_le_pow_left₀ h0 hc 2
  norm_num at hs ⊢
  linarith only [hs]

theorem absorption_le_local : absorptionThreshold ≤ localBound := by
  have hC1 : 512 * Real.pi ^ 2 ≤ (10 : ℝ) ^ 100 := by
    have hp : 512 * Real.pi ^ 2 ≤ 512 * (4 : ℝ) ^ 2 := by gcongr; exact Real.pi_lt_four.le
    norm_num at hp ⊢
    linarith only [hp]
  have hC2 : 4 * (31 * Real.pi / 64) * Real.pi ^ 2 ≤ (10 : ℝ) ^ 100 := by
    have hp : 4 * (31 * Real.pi / 64) * Real.pi ^ 2 ≤
        4 * (31 * (4 : ℝ) / 64) * 4 ^ 2 := by gcongr <;> exact Real.pi_lt_four.le
    norm_num at hp ⊢
    linarith only [hp]
  have hsmall : 16 ≤ localBound := Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num : 4 ≤ 10000)
  apply max_le hsmall
  apply max_le (size_le_local (by norm_num))
  apply max_le (inverse_of_bounds hC1 (by norm_num))
  apply max_le (inverse_of_bounds hC2 (by norm_num))
  apply decay_of_bounds _ (by norm_num)
  rw [abs_of_nonneg (by positivity)]
  have hp : 192 * (33 * Real.pi ^ 2) ^ 2 ≤ 192 * (33 * (4 : ℝ) ^ 2) ^ 2 := by
    gcongr; exact Real.pi_lt_four.le
  norm_num at hp ⊢
  linarith only [hp]

theorem canonical_le_local : canonicalThreshold (65 * Real.pi ^ 2) (320 * Real.pi ^ 2) ≤ localBound := by
  apply max_le
  · apply inverse_of_bounds _ (by norm_num)
    have hs : Real.sqrt (32 * Real.pi ^ 4 * (65 * Real.pi ^ 2) ^ 2) ≤ 10 ^ 8 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · have hp : 32 * Real.pi ^ 4 * (65 * Real.pi ^ 2) ^ 2 ≤
            32 * (4 : ℝ) ^ 4 * (65 * 4 ^ 2) ^ 2 := by gcongr <;> exact Real.pi_lt_four.le
        norm_num at hp ⊢
        linarith only [hp]
    norm_num at hs ⊢
    linarith only [hs]
  · apply decay_of_bounds _ (by norm_num)
    rw [abs_of_nonneg (by positivity)]
    have hp : 1536 * (320 * Real.pi ^ 2) ≤ 1536 * (320 * (4 : ℝ) ^ 2) := by
      gcongr; exact Real.pi_lt_four.le
    norm_num at hp ⊢
    linarith only [hp]

theorem strong_budget_le_local : ExplicitStrongBudget.orderThreshold ≤ localBound := by
  have hsmall : 256 ≤ localBound := Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num : 8 ≤ 10000)
  exact max_le hsmall (max_le objective_le_local (max_le canonical_le_local absorption_le_local))

theorem matching_saturation_le_local : ExplicitMatchingThreshold.saturationThreshold ≤ localBound :=
  max_le pressure_smallness_le_local matching_derivative_le_local

theorem active_word_le_concrete : ExplicitPressureThreshold.activeWordThreshold ≤ concreteThreshold :=
  max_le (pressure_smallness_le_local.trans local_le_concrete) marginThreshold_le_concrete

end
end StructuralNote.ExplicitLocalNumerical
