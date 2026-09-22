import StructuralNote.ExplicitPressureThreshold

/-! A deliberately coarse concrete integer bound for the pressure margin. -/

namespace StructuralNote.ExplicitPressureNumerical

open Erdos1045.ExplicitThreshold ExplicitPressureThreshold
open StrongObjectiveEstimate PressureAngularAbsorption ActualPressureAbsorption
open SinglePressureEstimate StrongBudgetConsequences StrongPointwiseSteps
open MatchingActivityRadialDiameterError MatchingActivityRadialModelEnergy
open MatchingActivityRadialModelCenterError
noncomputable section

theorem budget_bound : budgetConstant ≤ 2 * 10 ^ 15 := by
  have hpi : Real.pi ≤ 4 := Real.pi_lt_four.le
  have hobj : objectiveConstant ≤
      8320 * (4 : ℝ) ^ 4 * (65 * 4 ^ 2) ^ 2 +
        4096 * (320 * 4 ^ 2) * 4 ^ 2 * (65 * 4 ^ 2) := by
    unfold objectiveConstant
    gcongr
  have hang : angularConstant ≤
      8 * (24 * (4 : ℝ) ^ 3) ^ 2 + 8 * (33 * 4 ^ 2) ^ 2 *
        (320 * 4 ^ 2 + 64 * 4 ^ 2 * (65 * 4 ^ 2)) := by
    unfold angularConstant
    gcongr
  have hp : 9 * (31 * Real.pi / 64) * Real.pi ^ 4 / 4 ≤
      9 * (31 * (4 : ℝ) / 64) * 4 ^ 4 / 4 := by gcongr
  unfold budgetConstant comparisonConstant pressureConstant
  norm_num at hobj hang hp ⊢
  linarith only [hobj, hang, hp]

theorem center_bound : centerConstant ≤ 3 * 10 ^ 8 := by
  unfold centerConstant
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hh : 64 * Real.pi ^ 2 * (65 * Real.pi ^ 2) ≤
        64 * (4 : ℝ) ^ 2 * (65 * 4 ^ 2) := by gcongr <;> exact Real.pi_lt_four.le
    norm_num at hh ⊢
    linarith only [hh, budget_bound]

theorem angle_bound : angleConstant ≤ 6 * 10 ^ 8 := by
  unfold angleConstant
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · have hh : 8 * Real.pi ^ 2 * budgetConstant ≤
        8 * (4 : ℝ) ^ 2 * (2 * 10 ^ 15) := by
      gcongr
      · exact budgetConstant_nonneg
      · exact Real.pi_lt_four.le
      · exact budget_bound
    norm_num at hh ⊢
    linarith only [hh]

theorem center_step_bound : centerStepConstant ≤ 7 * 10 ^ 8 := by
  unfold centerStepConstant
  linarith only [Real.pi_lt_four, angle_bound]

theorem physical_step_bound : physicalStepConstant ≤ 2 * 10 ^ 17 := by
  have ha : 0 ≤ angleConstant := by unfold angleConstant; positivity
  have hh := mul_le_mul angle_bound center_bound
    (by unfold centerConstant; positivity : 0 ≤ centerConstant)
    (by norm_num : (0 : ℝ) ≤ 6 * 10 ^ 8)
  unfold physicalStepConstant
  nlinarith only [hh, center_step_bound]

theorem diameter_step_bound : diameterStepConstant ≤ 5 * 10 ^ 15 := by
  unfold diameterStepConstant
  linarith only [angle_bound, budget_bound]

theorem derotation_bound : derotationConstant ≤ 2 * 10 ^ 17 := by
  have hh := mul_le_mul center_bound angle_bound
    (by unfold angleConstant; positivity : 0 ≤ angleConstant)
    (by norm_num : (0 : ℝ) ≤ 3 * 10 ^ 8)
  unfold derotationConstant
  nlinarith only [hh, center_step_bound]

theorem center_error_bound : centerErrorConstant ≤ 10 ^ 54 := by
  have hp0 : 0 ≤ physicalStepConstant := MatchingActivityRadialModelEnergy.constants_nonneg.1
  have hd0 : 0 ≤ diameterStepConstant := diameterStepConstant_nonneg
  have hcube := pow_le_pow_left₀ hp0 physical_step_bound 3
  have hprod := mul_le_mul diameter_step_bound physical_step_bound hp0
    (by norm_num : (0 : ℝ) ≤ 5 * 10 ^ 15)
  have hs : Real.sqrt budgetConstant ≤ 10 ^ 8 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · norm_num
      linarith only [budget_bound]
  unfold centerErrorConstant
  nlinarith only [hcube, hprod, hs, derotation_bound]

theorem margin_constant_bounds : 0 ≤ marginConstant ∧ marginConstant ≤ 10 ^ 15 := by
  have hb0 := budgetConstant_nonneg
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl : Real.log 4 ≤ 4 := (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans (by norm_num)
  unfold marginConstant
  constructor
  · positivity
  · linarith only [budget_bound, Real.pi_lt_four, hl]

/-- Kept as an exponent expression; its decimal digits are never expanded. -/
def concreteThreshold : ℕ := 2 ^ (10 ^ 120)

theorem marginThreshold_le_concrete : marginThreshold ≤ concreteThreshold := by
  let T : ℝ := max (4 * |(128 : ℝ)| * |marginConstant| + 4)
    (32 * (|(128 : ℝ)| * |(9 / 2 : ℝ) * centerErrorConstant|) ^ 2 + 4)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : T ≤ 10 ^ 116 := by
    dsimp [T]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 128),
      abs_of_nonneg margin_constant_bounds.1,
      abs_of_nonneg (mul_nonneg (by norm_num) centerErrorConstant_nonneg)]
    apply max_le
    · linarith only [margin_constant_bounds.2]
    · have hh : (128 * ((9 / 2 : ℝ) * centerErrorConstant)) ^ 2 ≤
          (128 * ((9 / 2 : ℝ) * 10 ^ 54)) ^ 2 := by
        gcongr
        · exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) centerErrorConstant_nonneg)
        · exact center_error_bound
      norm_num at hh ⊢
      linarith only [hh]
  have hmaj : majorant T ≤ 10 ^ 116 + 1 := by
    unfold majorant
    apply Nat.add_le_add_right
    apply Nat.ceil_le.mpr
    rw [abs_of_nonneg hT0]
    exact_mod_cast hT
  have he : 2 * majorant T + 1 ≤ 10 ^ 120 := by omega
  have hp : growthThreshold T ≤ concreteThreshold := by
    unfold growthThreshold concreteThreshold
    exact Nat.pow_le_pow_right (by decide : 0 < 2) he
  have h16 : 16 ≤ concreteThreshold := by
    change 2 ^ 4 ≤ 2 ^ (10 ^ 120)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num)
  exact max_le h16 hp

theorem pressure_margin_concrete {n : ℕ} (hn : concreteThreshold ≤ n) :
    8 * (31 * Real.pi / 64) +
        (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (n : ℝ)) <
      ((Real.log (((n / 4 : ℕ) : ℝ) + 1) - 1) / 16 - budgetConstant / 2) / 8 :=
  pressure_margin (marginThreshold_le_concrete.trans hn)

end
end StructuralNote.ExplicitPressureNumerical
