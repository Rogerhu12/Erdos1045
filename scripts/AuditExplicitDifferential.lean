import StructuralNote.ExplicitFixedSchurCoefficients
import StructuralNote.ExplicitFixedSchurHessianGeometry
import StructuralNote.ExplicitBalancedSelection
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
elab "#audit_explicit_differential" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[
    ``StructuralNote.ExplicitFixedSchurCoefficients.logOrder_div_small,
    ``StructuralNote.ExplicitFixedSchurCoefficients.actual_coefficients_small,
    ``StructuralNote.ExplicitFixedSchurCoefficients.actual_solution_bounds,
    ``StructuralNote.ExplicitFixedSchurCoefficients.source_coefficients,
    ``StructuralNote.ExplicitFixedSchurCoefficients.radialCoefficient_bound,
    ``StructuralNote.ExplicitFixedSchurCoefficients.source_meanSquare,
    ``StructuralNote.ExplicitFixedSchurCoefficients.first_solution_meanSquare,
    ``StructuralNote.ExplicitFixedSchurCoefficients.first_solution_l2,
    ``StructuralNote.ExplicitFixedSchurCoefficients.source_pointwise_sq,
    ``StructuralNote.ExplicitFixedSchurCoefficients.first_solution_sup_sq,
    ``StructuralNote.ExplicitFixedSchurCoefficients.betaBudget_le_order,
    ``StructuralNote.ExplicitFixedSchurCoefficients.first_solution_coarse,
    ``StructuralNote.ExplicitFixedSchurHessianGeometry.log_ratio_small,
    ``StructuralNote.ExplicitFixedSchurHessianGeometry.logOrder_le_sqrt,
    ``StructuralNote.ExplicitFixedSchurHessianGeometry.hessian_coefficient_small,
    ``StructuralNote.ExplicitFixedSchurHessianGeometry.angular_derivative_energy,
    ``StructuralNote.ExplicitFixedSchurHessianGeometry.circular_curvature,
    ``StructuralNote.ExplicitFixedSchurHessianGeometry.chosen_derivatives_antiperiodic,
    ``StructuralNote.ExplicitBalancedSelection.FiniteImprovement,
    ``StructuralNote.ExplicitBalancedSelection.orderThreshold,
    ``StructuralNote.ExplicitBalancedSelection.extremal_chart_word_balanced
  ]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"EXPLICIT_DIFFERENTIAL_AUDIT_PASS: {declarations.size} declarations"
#audit_explicit_differential
