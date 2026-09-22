import StructuralNote.ExplicitNumericalBounds
import StructuralNote.ExplicitRationalRepresentation
import StructuralNote.ExplicitRationalRecovery
import StructuralNote.ExplicitCanonicalEntrySelected

/-! A single deliberately coarse numerical ceiling for the explicit rational
and selected-chart thresholds. -/
namespace StructuralNote.ExplicitRationalNumerical

open Erdos1045.ExplicitThreshold
open StrongBudgetConsequences StrongPointwiseSteps
open MatchingActivityRadialModelEnergy MatchingActivityActualChart
open FixedSchurNormalInnerBound FixedSchurNormalInnerEnergy
open FixedSchurNormalInnerDifference FixedSchurInnerRemainder
open FixedSchurLocalQuadratic FixedSchurLocalComparison
open FixedSchurReferenceDisplacement FixedSchurRationalInnerWindow
open ExplicitNumericalBounds ExplicitPressureNumerical

noncomputable section

theorem hessianThreshold_le_concrete :
    ExplicitHessianThreshold.orderThreshold ≤ concreteThreshold := by
  unfold ExplicitHessianThreshold.orderThreshold concreteThreshold
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num)

theorem chart_energy_bound : actualChartEnergyConstant ≤ (10 : ℝ) ^ 36 := by
  have hd0 : 0 ≤ derotationConstant := MatchingActivityRadialModelEnergy.constants_nonneg.2
  have hd2 := pow_le_pow_left₀ hd0 derotation_bound 2
  have hb := budget_bound
  unfold actualChartEnergyConstant
  norm_num at hd2 hb ⊢
  linarith only [hd2, hb]

theorem chart_energy_add_one_bound :
    actualChartEnergyConstant + 1 ≤ (10 : ℝ) ^ 37 := by
  linarith only [chart_energy_bound]

theorem constraint_bound : actualConstraintConstant ≤ (10 : ℝ) ^ 17 := by
  have hp := physical_step_bound
  unfold actualConstraintConstant
  norm_num at hp ⊢
  linarith only [hp]

private theorem pow10_1000_le_concrete : (10 : ℕ) ^ 1000 ≤ concreteThreshold := by
  apply (pow10_le_pow2 1000).trans
  unfold concreteThreshold
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num)

private theorem growth_le_concrete {T : ℝ}
    (hT : |T| ≤ (10 : ℝ) ^ 100) : growthThreshold T ≤ concreteThreshold := by
  have hm := majorant_le_pow10 hT
  have he : 2 * majorant T + 1 ≤ 10 ^ 120 := by omega
  unfold growthThreshold concreteThreshold
  exact Nat.pow_le_pow_right (by decide : 0 < 2) he

private theorem pow10_mono_to_1000 {k : ℕ} (hk : k ≤ 1000) :
    (10 : ℕ) ^ k ≤ 10 ^ 1000 :=
  Nat.pow_le_pow_right (by decide) hk

theorem representationThreshold_le_concrete :
    ExplicitRationalRepresentation.orderThreshold ≤ concreteThreshold := by
  have hK1 : |320 * (actualConstraintConstant + 1)| ≤ (10 : ℝ) ^ 20 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num)
      (by linarith only [actualConstraintConstant_nonneg]))]
    have hc := constraint_bound
    norm_num at hc ⊢
    nlinarith only [hc]
  have hrep : ExplicitCanonicalEntrySelected.representationThreshold
      actualConstraintConstant ≤ concreteThreshold := by
    unfold ExplicitCanonicalEntrySelected.representationThreshold
    simp only [max_le_iff]
    refine ⟨(show 1024 ≤ (10 : ℕ) ^ 1000 by
      calc
        1024 ≤ 10 ^ 4 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by decide) (by omega)).trans
      pow10_1000_le_concrete, ?_, ?_, ?_, ?_⟩
    · unfold Erdos1045.ExplicitThreshold.threshold
      unfold concreteThreshold
      exact Nat.pow_le_pow_right (by decide) (by norm_num)
    · exact (decay_le_pow10 (a := 4) (b := 1) (by norm_num) (by norm_num)).trans
        ((pow10_mono_to_1000 (by norm_num)).trans pow10_1000_le_concrete)
    · exact (decay_le_pow10 (a := 1) (b := 1) (by norm_num) (by norm_num)).trans
        ((pow10_mono_to_1000 (by norm_num)).trans pow10_1000_le_concrete)
    · exact (decay_le_pow10 (a := 20) (b := 1) hK1 (by norm_num)).trans
        ((pow10_mono_to_1000 (by norm_num)).trans pow10_1000_le_concrete)
  unfold ExplicitRationalRepresentation.orderThreshold
  exact max_le hessianThreshold_le_concrete hrep

theorem canonicalEntryThreshold_le_concrete :
    ExplicitCanonicalEntry.orderThreshold ≤ concreteThreshold := by
  unfold ExplicitCanonicalEntry.orderThreshold ExplicitCanonicalEntry.projectionThreshold
  apply growth_le_concrete
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [abs_of_nonneg (mul_nonneg (Real.log_nonneg (by norm_num)) (by positivity)),
    abs_of_nonneg actualChartEnergyConstant_nonneg]
  have hfac : actualChartEnergyConstant + 1 ≤ (10 : ℝ) ^ 36 + 1 := by
    simpa only [add_comm] using add_le_add_left chart_energy_bound 1
  calc
    Real.log 2 * (actualChartEnergyConstant + 1) ≤
        1 * ((10 : ℝ) ^ 36 + 1) :=
      mul_le_mul hlog hfac
        (by linarith only [actualChartEnergyConstant_nonneg]) (by norm_num)
    _ ≤ (10 : ℝ) ^ 100 := by norm_num

private theorem normalS_bound :
    normalSConstant (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 39 := by
  unfold normalSConstant
  have h := chart_energy_add_one_bound
  norm_num at h ⊢
  linarith only [h]

private theorem angularSup_bound :
    angularSupConstant (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 80 := by
  unfold angularSupConstant
  have h : 1 + (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 38 := by
    linarith only [chart_energy_add_one_bound]
  calc
    1000 * (1 + (actualChartEnergyConstant + 1)) ^ 2 ≤
        1000 * ((10 : ℝ) ^ 38) ^ 2 := by
      gcongr
      linarith only [actualChartEnergyConstant_nonneg]
    _ ≤ (10 : ℝ) ^ 80 := by norm_num

private theorem normalP_bound :
    normalPConstant (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 39 := by
  unfold normalPConstant
  have h := chart_energy_add_one_bound
  norm_num at h ⊢
  linarith only [h]

private theorem normalEnergy_sq_bound :
    normalEnergyConstant (actualChartEnergyConstant + 1) ^ 2 ≤ (10 : ℝ) ^ 170 := by
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hA0 := angularSupConstant_nonneg hB0
  have hP0 := normalPConstant_nonneg hB0
  have hS0 := normalSConstant_nonneg hB0
  have hrad0 : 0 ≤
      3 * angularSupConstant (actualChartEnergyConstant + 1) ^ 2 +
        96 * normalPConstant (actualChartEnergyConstant + 1) ^ 2 *
          (actualChartEnergyConstant + 1) ^ 2 +
        192 * normalSConstant (actualChartEnergyConstant + 1) ^ 4 := by positivity
  unfold normalEnergyConstant
  rw [Real.sq_sqrt hrad0]
  have hA := angularSup_bound
  have hP := normalP_bound
  have hB := chart_energy_add_one_bound
  have hS := normalS_bound
  calc
    _ ≤ 3 * ((10 : ℝ) ^ 80) ^ 2 +
        96 * ((10 : ℝ) ^ 39) ^ 2 * ((10 : ℝ) ^ 37) ^ 2 +
        192 * ((10 : ℝ) ^ 39) ^ 4 := by gcongr
    _ ≤ (10 : ℝ) ^ 170 := by norm_num

private theorem normalEnergy_zero_sq_bound :
    normalEnergyConstant 0 ^ 2 ≤ (10 : ℝ) ^ 170 := by
  have hrad0 : 0 ≤
      3 * angularSupConstant 0 ^ 2 + 96 * normalPConstant 0 ^ 2 * 0 ^ 2 +
        192 * normalSConstant 0 ^ 4 := by positivity
  unfold normalEnergyConstant
  rw [Real.sq_sqrt hrad0]
  unfold angularSupConstant normalPConstant normalSConstant
  norm_num

private theorem coordinate_bound :
    coordinateConstant (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 172 := by
  unfold coordinateConstant
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have he := normalEnergy_sq_bound
  have he0 := normalEnergy_zero_sq_bound
  have hB := chart_energy_add_one_bound
  calc
    _ ≤ 3 * ((10 : ℝ) ^ 170) + 3 * ((10 : ℝ) ^ 170) +
        12 * 4 ^ 2 * ((10 : ℝ) ^ 37) ^ 2 := by gcongr
    _ ≤ (10 : ℝ) ^ 172 := by norm_num

private theorem reference_bound :
    referenceConstant (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 174 := by
  unfold referenceConstant
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hB := chart_energy_add_one_bound
  have hC := coordinate_bound
  calc
    _ ≤ 40 * ((10 : ℝ) ^ 172) + 5 * ((10 : ℝ) ^ 37) ^ 2 := by
      gcongr
    _ ≤ (10 : ℝ) ^ 174 := by norm_num

private theorem innerWindow_bound :
    innerWindowConstant (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 180 := by
  unfold innerWindowConstant
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hB := chart_energy_add_one_bound
  have hR := reference_bound
  calc
    _ ≤ 4 * ((10 : ℝ) ^ 37) ^ 2 + (5 / 4 : ℝ) * ((10 : ℝ) ^ 174) +
        96120 * ((10 : ℝ) ^ 37) ^ 2 := by gcongr
    _ ≤ (10 : ℝ) ^ 180 := by norm_num

private theorem comparisonNormalThreshold_le_concrete :
    ExplicitComparisonNormal.orderThreshold (actualChartEnergyConstant + 1) ≤
      concreteThreshold := by
  have hc : ⌈8 * normalSConstant (actualChartEnergyConstant + 1) + 1⌉₊ ≤
      (10 : ℕ) ^ 40 := by
    apply Nat.ceil_le.mpr
    exact_mod_cast (show 8 * normalSConstant (actualChartEnergyConstant + 1) + 1 ≤
      (10 : ℝ) ^ 40 by nlinarith only [normalS_bound])
  have hc' := hc.trans (pow10_mono_to_1000 (by norm_num)) |>.trans pow10_1000_le_concrete
  have h2048 : 2048 ≤ concreteThreshold := by
    apply (show 2048 ≤ (10 : ℕ) ^ 1000 by
      calc
        2048 ≤ 10 ^ 4 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by decide) (by omega)).trans
    exact pow10_1000_le_concrete
  unfold ExplicitComparisonNormal.orderThreshold
  exact max_le hessianThreshold_le_concrete (max_le h2048 hc')

private theorem comparisonNormalZeroThreshold_le_concrete :
    ExplicitComparisonNormal.orderThreshold 0 ≤ concreteThreshold := by
  have hc : ⌈8 * normalSConstant 0 + 1⌉₊ ≤ (10 : ℕ) ^ 40 := by
    norm_num [normalSConstant]
  have hc' := hc.trans (pow10_mono_to_1000 (by norm_num)) |>.trans pow10_1000_le_concrete
  have h2048 : 2048 ≤ concreteThreshold := by
    apply (show 2048 ≤ (10 : ℕ) ^ 1000 by
      calc
        2048 ≤ 10 ^ 4 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by decide) (by omega)).trans
    exact pow10_1000_le_concrete
  unfold ExplicitComparisonNormal.orderThreshold
  exact max_le hessianThreshold_le_concrete (max_le h2048 hc')

private theorem recoverySquareThreshold_le_concrete :
    ExplicitRationalRecovery.squareLogThreshold
      (8 * innerWindowConstant (actualChartEnergyConstant + 1)) ≤ concreteThreshold := by
  unfold ExplicitRationalRecovery.squareLogThreshold
  apply growth_le_concrete
  have hinner0 : 0 ≤ innerWindowConstant (actualChartEnergyConstant + 1) := by
    unfold innerWindowConstant
    have := referenceConstant_nonneg (actualChartEnergyConstant + 1)
    positivity
  have hroot : Real.sqrt |8 * innerWindowConstant
      (actualChartEnergyConstant + 1)| ≤ (10 : ℝ) ^ 91 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [abs_of_nonneg (mul_nonneg (by norm_num) hinner0)]
      calc
        8 * innerWindowConstant (actualChartEnergyConstant + 1) ≤
            8 * ((10 : ℝ) ^ 180) := mul_le_mul_of_nonneg_left innerWindow_bound (by norm_num)
        _ ≤ ((10 : ℝ) ^ 91) ^ 2 := by norm_num
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [abs_of_nonneg (mul_nonneg (Real.log_nonneg (by norm_num)) (by positivity))]
  calc
    Real.log 2 * (Real.sqrt |8 * innerWindowConstant
        (actualChartEnergyConstant + 1)| + 1) ≤
        1 * ((10 : ℝ) ^ 91 + 1) := by gcongr
    _ ≤ (10 : ℝ) ^ 100 := by norm_num

theorem rationalRecoveryThreshold_le_concrete :
    ExplicitRationalRecovery.orderThreshold (actualChartEnergyConstant + 1) ≤
      concreteThreshold := by
  unfold ExplicitRationalRecovery.orderThreshold
    ExplicitRationalRecovery.displacementThreshold
  exact max_le (max_le comparisonNormalThreshold_le_concrete
    comparisonNormalZeroThreshold_le_concrete) recoverySquareThreshold_le_concrete

private theorem comparisonRemainderThreshold_le_concrete :
    ExplicitComparisonRemainder.orderThreshold (actualChartEnergyConstant + 1) ≤
      concreteThreshold := by
  have hr : (30 + 3 * (actualChartEnergyConstant + 1)) / (1 / 4 : ℝ) ≤
      (10 : ℝ) ^ 40 := by
    have h := chart_energy_add_one_bound
    norm_num at h ⊢
    nlinarith only [h]
  have hi := inverse_le_pow10 (k := 40) hr
  have hi' := hi.trans (pow10_mono_to_1000 (by norm_num)) |>.trans
    pow10_1000_le_concrete
  unfold ExplicitComparisonRemainder.orderThreshold
  exact max_le hessianThreshold_le_concrete hi'

private theorem comparisonAngularThreshold_le_concrete :
    ExplicitComparisonScalars.angularThreshold SinglePressureEstimate.budgetConstant ≤
      concreteThreshold := by
  have hb0 : 0 ≤ SinglePressureEstimate.budgetConstant :=
    StrongBudgetConsequences.budgetConstant_nonneg
  have hM0 : 0 ≤ |SinglePressureEstimate.budgetConstant| + 1 := by positivity
  let T : ℝ := 16 * (|(|SinglePressureEstimate.budgetConstant| + 1)| +
      |SinglePressureEstimate.budgetConstant| / 2) +
    1 + Real.log 4
  have hT0 : 0 ≤ T := by
    dsimp [T]
    positivity
  have hlog4 : Real.log 4 ≤ 4 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans (by norm_num)
  have hT : |T| ≤ (10 : ℝ) ^ 100 := by
    rw [abs_of_nonneg hT0]
    dsimp [T]
    rw [abs_of_nonneg hM0, abs_of_nonneg hb0]
    have hb := budget_bound
    norm_num at hb ⊢
    linarith only [hb, hlog4]
  have hg := growth_le_concrete hT
  have hs : ExplicitPressureThreshold.signThreshold SinglePressureEstimate.budgetConstant
      (|SinglePressureEstimate.budgetConstant| + 1) ≤ concreteThreshold := by
    unfold ExplicitPressureThreshold.signThreshold
    exact max_le (by
      exact (show 4 ≤ (10 : ℕ) ^ 1000 by
        calc
          4 ≤ 10 ^ 1 := by norm_num
          _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by decide) (by omega)).trans
        pow10_1000_le_concrete) hg
  unfold ExplicitComparisonScalars.angularThreshold
  exact max_le (by
    exact (show 2048 ≤ (10 : ℕ) ^ 1000 by
      calc
        2048 ≤ 10 ^ 4 := by norm_num
        _ ≤ 10 ^ 1000 := Nat.pow_le_pow_right (by decide) (by omega)).trans
      pow10_1000_le_concrete) hs

private theorem comparisonNearThreshold_le_concrete :
    ExplicitLocalComparison.nearThreshold (actualChartEnergyConstant + 1)
      SinglePressureEstimate.budgetConstant ≤ concreteThreshold := by
  unfold ExplicitLocalComparison.nearThreshold ExplicitLocalComparison.orderThreshold
  exact max_le
    (max_le comparisonNormalThreshold_le_concrete comparisonRemainderThreshold_le_concrete)
    comparisonAngularThreshold_le_concrete

private theorem normalEnergy_bound :
    normalEnergyConstant (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 86 := by
  have hE0 := normalEnergyConstant_nonneg (actualChartEnergyConstant + 1)
  have h := normalEnergy_sq_bound
  norm_num at h ⊢
  nlinarith only [h, sq_nonneg (normalEnergyConstant
    (actualChartEnergyConstant + 1) - (10 : ℝ) ^ 86)]

private theorem difference_bound :
    differenceConstant (actualChartEnergyConstant + 1) 2 ≤ (10 : ℝ) ^ 100 := by
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hA0 := angularSupConstant_nonneg hB0
  have hS0 := normalSConstant_nonneg hB0
  have hA := angularSup_bound
  have hS := normalS_bound
  have hB := chart_energy_add_one_bound
  unfold differenceConstant
  calc
    _ ≤ 4 * ((10 : ℝ) ^ 80) * 2 + 480 * ((10 : ℝ) ^ 37) * 2 +
        16 * ((10 : ℝ) ^ 39) * (80 * 2 + 10) +
        32 * ((10 : ℝ) ^ 39) ^ 2 * 2 := by gcongr
    _ ≤ (10 : ℝ) ^ 100 := by norm_num

private theorem remainderCoefficient_bound :
    FixedSchurInnerRemainder.coefficient (actualChartEnergyConstant + 1) ≤
      (10 : ℝ) ^ 100 := by
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hB := chart_energy_add_one_bound
  have hlin : 30 + 3 * (actualChartEnergyConstant + 1) ≤ (10 : ℝ) ^ 38 := by
    linarith only [chart_energy_add_one_bound]
  unfold FixedSchurInnerRemainder.coefficient
  calc
    _ ≤ 32 * (3 * ((10 : ℝ) ^ 37) * ((10 : ℝ) ^ 38) +
        82 * ((10 : ℝ) ^ 38) ^ 2) := by gcongr
    _ ≤ (10 : ℝ) ^ 100 := by norm_num

private theorem quadratic_bound :
    quadraticConstant (actualChartEnergyConstant + 1) 2 ≤ (10 : ℝ) ^ 180 := by
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hE0 := normalEnergyConstant_nonneg (actualChartEnergyConstant + 1)
  have hD0 := differenceConstant_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2)
  have hpi0 := Real.pi_pos.le
  have hE := normalEnergy_bound
  have hD := difference_bound
  have hB := chart_energy_add_one_bound
  have hE2 := normalEnergy_sq_bound
  unfold quadraticConstant
  calc
    _ ≤ 12 * 2 * ((10 : ℝ) ^ 86) + 3 * ((10 : ℝ) ^ 100) +
        4 * 4 ^ 2 * ((10 : ℝ) ^ 37) ^ 2 + (10 : ℝ) ^ 170 := by
      gcongr
      exact Real.pi_lt_four.le
    _ ≤ (10 : ℝ) ^ 180 := by norm_num

private theorem nearComparison_bound :
    nearComparisonConstant (actualChartEnergyConstant + 1) 2 ≤ (10 : ℝ) ^ 200 := by
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hcoef0 := FixedSchurInnerRemainder.coefficient_nonneg hB0
  have hq0 := quadraticConstant_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2)
  have hroot : Real.sqrt (12800 * (2 : ℝ)) ≤ 1000 := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  have hcoef := remainderCoefficient_bound
  have hq := quadratic_bound
  have hB := chart_energy_add_one_bound
  unfold nearComparisonConstant comparisonConstant
  calc
    _ ≤ (10 : ℝ) ^ 100 * 1000 + (10 : ℝ) ^ 180 +
        24 * 4 * ((10 : ℝ) ^ 37) * 2 := by
      gcongr
      exact Real.pi_lt_four.le
    _ ≤ (10 : ℝ) ^ 200 := by norm_num

private theorem comparisonInverseSqrtThreshold_le_concrete :
    inverseSqrtThreshold (nearComparisonConstant
      (actualChartEnergyConstant + 1) 2) (16 / 25) ≤ concreteThreshold := by
  have hB0 : 0 ≤ actualChartEnergyConstant + 1 := by
    linarith only [actualChartEnergyConstant_nonneg]
  have hC0 := nearComparisonConstant_nonneg hB0 (by norm_num : (0 : ℝ) ≤ 2)
  have hdiv : nearComparisonConstant (actualChartEnergyConstant + 1) 2 /
      (16 / 25 : ℝ) ≤ 2 * (10 : ℝ) ^ 200 := by
    have h := nearComparison_bound
    norm_num at h ⊢
    nlinarith only [h]
  have hsq : (nearComparisonConstant (actualChartEnergyConstant + 1) 2 /
      (16 / 25 : ℝ)) ^ 2 ≤ (10 : ℝ) ^ 500 := by
    calc
      _ ≤ (2 * (10 : ℝ) ^ 200) ^ 2 :=
        pow_le_pow_left₀ (div_nonneg hC0 (by norm_num)) hdiv 2
      _ ≤ (10 : ℝ) ^ 500 := by
        exact_mod_cast (show 4 * (10 : ℕ) ^ 400 ≤ 10 ^ 500 by
          rw [show 500 = 100 + 400 by omega, pow_add]
          exact Nat.mul_le_mul_right _ (calc
            4 ≤ 10 ^ 1 := by norm_num
            _ ≤ 10 ^ 100 := Nat.pow_le_pow_right (by decide) (by omega)))
  have hi := inverseSqrt_le_pow10 (k := 500) hsq
  exact hi.trans (pow10_mono_to_1000 (by norm_num)) |>.trans pow10_1000_le_concrete

theorem balancedSelectionThreshold_le_concrete :
    ExplicitBalancedSelection.orderThreshold (actualChartEnergyConstant + 1)
      SinglePressureEstimate.budgetConstant (16 / 25) ≤ concreteThreshold := by
  unfold ExplicitBalancedSelection.orderThreshold
  exact max_le comparisonNearThreshold_le_concrete
    comparisonInverseSqrtThreshold_le_concrete

end
end StructuralNote.ExplicitRationalNumerical
