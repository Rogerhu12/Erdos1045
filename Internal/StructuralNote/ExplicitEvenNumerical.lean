import StructuralNote.ExplicitFrontNumerical
import StructuralNote.ExplicitRationalNumerical
import StructuralNote.ExplicitKernelNumerical
import StructuralNote.ExplicitActualRationalStationary
import EventualExact.ExplicitLocalizationNumerical
import StructuralNote.ExplicitEvenThreshold

/-! The finite analytic and algebraic cutoffs fit below a single integer. -/
namespace StructuralNote.ExplicitEvenNumerical
open Erdos1045.EventualExact
open ExplicitPressureNumerical ExplicitRationalNumerical
open MatchingActivityActualChart
noncomputable section

theorem canonicalEntryThreshold_le_concrete_of_local
    (hlocal : ExplicitLocalization.localizationThreshold ExplicitStrongBudget.edgeTolerance ≤
      concreteThreshold) :
    ExplicitCanonicalEntrySelected.actualThreshold (16 / 25) ≤ concreteThreshold := by
  have hrepresentation :
      ExplicitCanonicalEntrySelected.representationThreshold actualConstraintConstant ≤
        concreteThreshold :=
    (le_max_right _ _).trans representationThreshold_le_concrete
  exact max_le
    (max_le (ExplicitFrontNumerical.crossingThreshold_le_concrete hlocal)
      (max_le canonicalEntryThreshold_le_concrete hrepresentation))
    balancedSelectionThreshold_le_concrete

theorem actualRationalThreshold_le_concrete_of_local
    (hlocal : ExplicitLocalization.localizationThreshold ExplicitStrongBudget.edgeTolerance ≤
      concreteThreshold) :
    ExplicitActualRationalStationary.orderThreshold (16 / 25) ≤ concreteThreshold :=
  max_le (canonicalEntryThreshold_le_concrete_of_local hlocal)
    (max_le rationalRecoveryThreshold_le_concrete representationThreshold_le_concrete)

theorem kernelThreshold_le_concrete :
    ExplicitKernelSelection.orderThreshold SinglePressureEstimate.budgetConstant ≤
      concreteThreshold := by
  exact max_le ExplicitKernelNumerical.word_classification_le_concrete
    (max_le ExplicitKernelNumerical.comparison_le_concrete
      (max_le ExplicitKernelNumerical.deficit_inverse_le_concrete
        ExplicitKernelNumerical.sign_threshold_le_concrete))

theorem orderThreshold_le_concrete : ExplicitEvenThreshold.orderThreshold ≤ concreteThreshold := by
  have h16 : 16 ≤ concreteThreshold := by
    change (2 : ℕ) ^ 4 ≤ 2 ^ (10 ^ 120)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by norm_num)
  exact max_le h16 (max_le hessianThreshold_le_concrete
    (max_le
      (actualRationalThreshold_le_concrete_of_local
        ExplicitLocalizationNumerical.localizationThreshold_le_concrete)
      kernelThreshold_le_concrete))

end
end StructuralNote.ExplicitEvenNumerical
