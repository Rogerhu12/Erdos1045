import StructuralNote.ExplicitFixedSchurFirstMoments
import StructuralNote.ExplicitFixedSchurHessianEstimate
import StructuralNote.ExplicitRationalWindow
import StructuralNote.ExplicitRationalRepresentation
import StructuralNote.ExplicitRationalClosure
import StructuralNote.ExplicitRationalPolynomial
import StructuralNote.ExplicitRationalTransfer
import StructuralNote.ExplicitRationalRecovery
import StructuralNote.ExplicitActualRationalStationary
import StructuralNote.ExplicitRationalStationaryTransfer
import StructuralNote.ExplicitRationalStationarySelection
import StructuralNote.ExplicitPolynomialSelection
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
elab "#audit_explicit_rational" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[
    ``StructuralNote.ExplicitFixedSchurFirstMoments.chosen_first_l2,
    ``StructuralNote.ExplicitFixedSchurFirstMoments.chosen_first_sup_sq,
    ``StructuralNote.ExplicitFixedSchurFirstMoments.chosen_first_coarse,
    ``StructuralNote.ExplicitFixedSchurFirstMoments.center_velocity_energy,
    ``StructuralNote.ExplicitFixedSchurHessianEstimate.actual_hessian_split,
    ``StructuralNote.ExplicitFixedSchurHessianEstimate.normal_hessian_bound,
    ``StructuralNote.ExplicitFixedSchurHessianEstimate.chosen_remainder_budget,
    ``StructuralNote.ExplicitFixedSchurHessianEstimate.hessian_error_of_second_moment,
    ``StructuralNote.ExplicitFixedSchurHessianEstimate.negative_hessian_of_second_moment,
    ``StructuralNote.ExplicitFixedSchurHessianEstimate.actual_hessian_estimate,
    ``StructuralNote.ExplicitRationalWindow.window_error_small,
    ``StructuralNote.ExplicitRationalWindow.fixedReferenceCenter_data,
    ``StructuralNote.ExplicitRationalWindow.selectedWindow_inDomain,
    ``StructuralNote.ExplicitRationalWindow.angle_error_small,
    ``StructuralNote.ExplicitRationalWindow.selectedWindow_angleParameter_small,
    ``StructuralNote.ExplicitRationalWindow.selectedWindow_angle_chart,
    ``StructuralNote.ExplicitRationalRepresentation.actualConstraint_lower,
    ``StructuralNote.ExplicitRationalRepresentation.reference_constraint_norm,
    ``StructuralNote.ExplicitRationalRepresentation.normalizedCenter_constraint_bound,
    ``StructuralNote.ExplicitRationalRepresentation.selectedWindow_representation,
    ``StructuralNote.ExplicitRationalClosure.crossing_coefficient_small,
    ``StructuralNote.ExplicitRationalClosure.selectedWindow_crossingParameter_small,
    ``StructuralNote.ExplicitRationalClosure.selectedWindow_closure_y_rank_two,
    ``StructuralNote.ExplicitRationalClosure.selectedWindow_closure_hasFDerivAt_surjective,
    ``StructuralNote.ExplicitRationalClosure.selectedWindow_closureMatrix_surjective,
    ``StructuralNote.ExplicitRationalPolynomial.reference_algebraic,
    ``StructuralNote.ExplicitRationalPolynomial.exists_selectedWindowPolynomial,
    ``StructuralNote.ExplicitRationalTransfer.selectedWindow_smallWindow,
    ``StructuralNote.ExplicitRationalTransfer.fixedSchurCoordinates_inDomain,
    ``StructuralNote.ExplicitRationalTransfer.fixed_configuration_eq_rigid,
    ``StructuralNote.ExplicitRationalTransfer.selectedWindow_collisionFree,
    ``StructuralNote.ExplicitRationalTransfer.fixed_discriminant_eq_rational,
    ``StructuralNote.ExplicitRationalTransfer.rational_objective_eq_fixed,
    ``StructuralNote.ExplicitRationalTransfer.objective_path_eventuallyEq,
    ``StructuralNote.ExplicitRationalTransfer.objective_path_deriv_eq,
    ``StructuralNote.ExplicitRationalTransfer.objective_path_second_deriv_eq,
    ``StructuralNote.ExplicitRationalRecovery.square_log_gt,
    ``StructuralNote.ExplicitRationalRecovery.coordinate_reference_meanSquare,
    ``StructuralNote.ExplicitRationalRecovery.center_reference_energy,
    ``StructuralNote.ExplicitRationalRecovery.selectedWindowEnergy_bound,
    ``StructuralNote.ExplicitRationalRecovery.selectedWindow_of_inner_recovery,
    ``StructuralNote.ExplicitRationalRecovery.recovery_data,
    ``StructuralNote.ExplicitRationalRecovery.inner_rational_recovery,
    ``StructuralNote.ExplicitActualRationalStationary.exists_rational_stationary_of_fixed_stationary,
    ``StructuralNote.ExplicitActualRationalStationary.actual_extremizer_rational_stationary,
    ``StructuralNote.ExplicitRationalStationaryTransfer.smooth_local_recovery,
    ``StructuralNote.ExplicitRationalStationaryTransfer.rational_stationary_fixed,
    ``StructuralNote.ExplicitRationalStationaryTransfer.affine_strict_curvature,
    ``StructuralNote.ExplicitRationalStationaryTransfer.rational_lagrangianHessian_negative,
    ``StructuralNote.ExplicitRationalStationaryTransfer.selectedWindow_stationary_jacobian_nonsingular,
    ``StructuralNote.ExplicitRationalStationarySelection.selectedWindow_stationary_unique,
    ``StructuralNote.ExplicitRationalStationarySelection.selectedWindow_stationary_algebraic,
    ``StructuralNote.ExplicitRationalStationarySelection.actual_extremizer_unique_algebraic_root,
    ``StructuralNote.ExplicitPolynomialSelection.window_polynomial_system_iff,
    ``StructuralNote.ExplicitPolynomialSelection.even_maximum_single_polynomial_root
  ]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"EXPLICIT_RATIONAL_AUDIT_PASS: {declarations.size} declarations"
#audit_explicit_rational
