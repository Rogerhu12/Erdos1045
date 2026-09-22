import StructuralNote.ExplicitLocalNumerical

/-! Assembly of the quantitative front-end bounds. -/
namespace StructuralNote.ExplicitFrontNumerical
open Erdos1045.EventualExact
open ExplicitPressureNumerical ExplicitLocalNumerical
noncomputable section

theorem strong_coordinates_le_concrete
    (hlocal : ExplicitLocalization.localizationThreshold ExplicitStrongBudget.edgeTolerance ≤
      concreteThreshold) : ExplicitStrongCoordinates.orderThreshold ≤ concreteThreshold :=
  max_le hlocal (max_le (pressure_coordinates_le_local.trans local_le_concrete)
    (strong_budget_le_local.trans local_le_concrete))

theorem crossingThreshold_le_concrete
    (hlocal : ExplicitLocalization.localizationThreshold ExplicitStrongBudget.edgeTolerance ≤
      concreteThreshold) : ExplicitMatchingCoordinates.crossingThreshold ≤ concreteThreshold :=
  max_le (max_le (strong_coordinates_le_concrete hlocal)
    (max_le (matching_pointwise_le_local.trans local_le_concrete)
      (matching_saturation_le_local.trans local_le_concrete))) active_word_le_concrete

end
end StructuralNote.ExplicitFrontNumerical
