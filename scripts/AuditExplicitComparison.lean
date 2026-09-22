import StructuralNote.ExplicitMatchingCoordinates
import StructuralNote.ExplicitComparisonScalars
import StructuralNote.ExplicitComparisonGeometry
import StructuralNote.ExplicitComparisonStability
import StructuralNote.ExplicitComparisonRotated
import StructuralNote.ExplicitComparisonNormal
import StructuralNote.ExplicitComparisonRemainder
import StructuralNote.ExplicitLocalComparison
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
elab "#audit_explicit_comparison" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[    ``StructuralNote.ExplicitMatchingCoordinates.matchingThreshold,
    ``StructuralNote.ExplicitMatchingCoordinates.crossingThreshold,
    ``StructuralNote.ExplicitMatchingCoordinates.combined_budget_parts,
    ``StructuralNote.ExplicitMatchingCoordinates.HasSaturatedCoordinates,
    ``StructuralNote.ExplicitMatchingCoordinates.diameter_matching_saturated,
    ``StructuralNote.ExplicitMatchingCoordinates.model_crossings_active,
    ``StructuralNote.ExplicitMatchingCoordinates.diameter_crossings_active,
    ``StructuralNote.ExplicitComparisonScalars.small_coefficients,
    ``StructuralNote.ExplicitComparisonScalars.inner_angle_sup,
    ``StructuralNote.ExplicitComparisonScalars.angularThreshold,
    ``StructuralNote.ExplicitComparisonScalars.near_angular_bound,
    ``StructuralNote.ExplicitComparisonGeometry.quotient_properties,
    ``StructuralNote.ExplicitComparisonGeometry.center_bounds,
    ``StructuralNote.ExplicitComparisonGeometry.normal_inner_local_bounds,
    ``StructuralNote.ExplicitComparisonStability.coordinate_l1_stability,
    ``StructuralNote.ExplicitComparisonStability.J_pointwise_stability,
    ``StructuralNote.ExplicitComparisonStability.center_energy_stability,
    ``StructuralNote.ExplicitComparisonStability.hamming_stability,
    ``StructuralNote.ExplicitComparisonStability.angleAverage_inv,
    ``StructuralNote.ExplicitComparisonStability.rotated_stability,
    ``StructuralNote.ExplicitComparisonRotated.radial_coefficient,
    ``StructuralNote.ExplicitComparisonRotated.coordinate_radial,
    ``StructuralNote.ExplicitComparisonRotated.angle_smallness,
    ``StructuralNote.ExplicitComparisonRotated.coordinate_rotated,
    ``StructuralNote.ExplicitComparisonRotated.normalError_rotated_expansion,
    ``StructuralNote.ExplicitComparisonNormal.orderThreshold,
    ``StructuralNote.ExplicitComparisonNormal.thresholds,
    ``StructuralNote.ExplicitComparisonNormal.normal_error_meanSquare,
    ``StructuralNote.ExplicitComparisonNormal.normal_error_l1_difference,
    ``StructuralNote.ExplicitComparisonNormal.actual_quadratic_comparison,
    ``StructuralNote.ExplicitComparisonRemainder.orderThreshold,
    ``StructuralNote.ExplicitComparisonRemainder.chosen_inner_sizes,
    ``StructuralNote.ExplicitComparisonRemainder.remainder_energy_bound,
    ``StructuralNote.ExplicitComparisonRemainder.remainder_hamming_bound,
    ``StructuralNote.ExplicitComparisonRemainder.objective_hamming_bound,
    ``StructuralNote.ExplicitLocalComparison.orderThreshold,
    ``StructuralNote.ExplicitLocalComparison.nearThreshold,
    ``StructuralNote.ExplicitLocalComparison.local_comparison,
    ``StructuralNote.ExplicitLocalComparison.near_local_comparison]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"EXPLICIT_MATCHING_AND_COMPARISON_AUDIT_PASS: {declarations.size} declarations"
#audit_explicit_comparison
