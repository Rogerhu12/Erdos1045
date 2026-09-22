import StructuralNote.ExplicitKernelBalanced
import StructuralNote.ExplicitLocalNumerical

/-! Numerical bounds for the finite Fourier and sign-classification cutoffs. -/
namespace StructuralNote.ExplicitKernelNumerical
open Erdos1045 Erdos1045.EventualExact Erdos1045.ExplicitThreshold
open ExplicitPressureNumerical ExplicitNumericalBounds ExplicitLocalNumerical
open SinglePressureEstimate ExplicitKernelBalanced ExplicitKernelRateIdentification
open StrongBudgetConsequences
open ExplicitKernelRate
noncomputable section

theorem word_classification_bound : 2 * wordClassificationThreshold ≤ 10 ^ 16 := by
  norm_num [wordClassificationThreshold, compressionKernelSignsThreshold,
    positiveIntervalThreshold, negativeIntervalThreshold, gridThreshold, frequencyCutoff]

theorem word_classification_le_concrete : 2 * wordClassificationThreshold ≤ concreteThreshold := by
  exact word_classification_bound.trans ((pow10_le_pow2 16).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num)))

theorem comparison_le_concrete : (2 : ℕ) ^ 200 ≤ concreteThreshold :=
  Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num)

theorem deficit_inverse_le_concrete :
    inverseThreshold |budgetConstant| (1 / 400000) ≤ concreteThreshold := by
  apply le_trans _ local_le_concrete
  apply inverse_of_bounds _ (by norm_num)
  rw [abs_of_nonneg budgetConstant_nonneg]
  exact budget_bound.trans (by norm_num)

theorem sign_threshold_le_concrete :
    ExplicitPressureThreshold.signThreshold budgetConstant (|budgetConstant| + 1) ≤ concreteThreshold := by
  let T : ℝ := 16 * (|(|budgetConstant| + 1)| + |budgetConstant| / 2) + 1 + Real.log 4
  have hlog0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog : Real.log 4 ≤ 4 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)).trans (by norm_num)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : |T| ≤ (10 : ℝ) ^ 18 := by
    rw [abs_of_nonneg hT0]
    dsimp [T]
    rw [abs_of_nonneg budgetConstant_nonneg,
      abs_of_nonneg (add_nonneg budgetConstant_nonneg (by norm_num))]
    norm_num
    linarith only [budget_bound, hlog]
  have hmaj : majorant T ≤ 10 ^ 19 := majorant_le_pow10 hT
  have hg : growthThreshold T ≤ concreteThreshold := by
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    norm_num at hmaj ⊢
    omega
  have h4 : 4 ≤ concreteThreshold :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num : 2 ≤ 10 ^ 120)
  exact max_le h4 hg

end
end StructuralNote.ExplicitKernelNumerical
