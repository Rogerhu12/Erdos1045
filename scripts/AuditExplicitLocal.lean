import StructuralNote.ExplicitLocalBudgets
import StructuralNote.ExplicitObjectiveThreshold
import StructuralNote.ExplicitStrongBudget
import StructuralNote.ExplicitPressureCoordinates
import StructuralNote.ExplicitStrongCoordinates
import StructuralNote.ExplicitMatchingThreshold
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
elab "#audit_explicit_local" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[    ``StructuralNote.ExplicitLocalBudgets.log_div_power_small,
    ``StructuralNote.ExplicitLocalBudgets.sizeThreshold,
    ``StructuralNote.ExplicitLocalBudgets.size_small,
    ``StructuralNote.ExplicitLocalBudgets.coordinateThreshold,
    ``StructuralNote.ExplicitLocalBudgets.coordinate_small,
    ``StructuralNote.ExplicitLocalBudgets.pairThreshold,
    ``StructuralNote.ExplicitLocalBudgets.pair_small,
    ``StructuralNote.ExplicitLocalBudgets.pathEnergy,
    ``StructuralNote.ExplicitLocalBudgets.pathTolerance,
    ``StructuralNote.ExplicitLocalBudgets.pathThreshold,
    ``StructuralNote.ExplicitLocalBudgets.pathTolerance_pos,
    ``StructuralNote.ExplicitLocalBudgets.model_path_gradient,
    ``StructuralNote.ExplicitLocalBudgets.canonicalThreshold,
    ``StructuralNote.ExplicitLocalBudgets.canonical_small,
    ``StructuralNote.ExplicitLocalBudgets.absorptionThreshold,
    ``StructuralNote.ExplicitLocalBudgets.absorption_small,
    ``StructuralNote.ExplicitObjectiveThreshold.edgeTolerance,
    ``StructuralNote.ExplicitObjectiveThreshold.orderThreshold,
    ``StructuralNote.ExplicitObjectiveThreshold.edgeTolerance_pos,
    ``StructuralNote.ExplicitObjectiveThreshold.parameters_small,
    ``StructuralNote.ExplicitObjectiveThreshold.model_normalized_price,
    ``StructuralNote.ExplicitObjectiveThreshold.model_angular_loss,
    ``StructuralNote.ExplicitObjectiveThreshold.model_objective_loss,
    ``StructuralNote.ExplicitStrongBudget.orderThreshold,
    ``StructuralNote.ExplicitStrongBudget.edgeTolerance,
    ``StructuralNote.ExplicitStrongBudget.edgeTolerance_pos,
    ``StructuralNote.ExplicitStrongBudget.model_scalar_gap_budget,
    ``StructuralNote.ExplicitStrongBudget.model_strong_budget,
    ``StructuralNote.ExplicitPressureCoordinates.diameter_budget_small,
    ``StructuralNote.ExplicitPressureCoordinates.constraintThreshold,
    ``StructuralNote.ExplicitPressureCoordinates.constraint_error_small,
    ``StructuralNote.ExplicitPressureCoordinates.orderThreshold,
    ``StructuralNote.ExplicitPressureCoordinates.model_pressure_coordinates,
    ``StructuralNote.ExplicitStrongCoordinates.orderThreshold,
    ``StructuralNote.ExplicitStrongCoordinates.diameter_strong_coordinates,
    ``StructuralNote.ExplicitStrongCoordinates.diameter_scalar_gap_coordinates,
    ``StructuralNote.ExplicitMatchingThreshold.div_pow_le_div,
    ``StructuralNote.ExplicitMatchingThreshold.pointwiseThreshold,
    ``StructuralNote.ExplicitMatchingThreshold.pointwise_scales,
    ``StructuralNote.ExplicitMatchingThreshold.model_pointwise,
    ``StructuralNote.ExplicitMatchingThreshold.derivativeThreshold,
    ``StructuralNote.ExplicitMatchingThreshold.derivative_scales,
    ``StructuralNote.ExplicitMatchingThreshold.saturationThreshold,
    ``StructuralNote.ExplicitMatchingThreshold.model_saturated]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"EXPLICIT_LOCAL_GEOMETRY_AUDIT_PASS: {declarations.size} declarations"
#audit_explicit_local
