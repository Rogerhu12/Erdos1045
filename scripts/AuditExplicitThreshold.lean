import StructuralNote.ExplicitThresholdScalar
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

elab "#audit_explicit_threshold" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[
    ``Erdos1045.ExplicitThreshold.threshold,
    ``Erdos1045.ExplicitThreshold.logBudget,
    ``Erdos1045.ExplicitThreshold.errorBudget,
    ``Erdos1045.ExplicitThreshold.profile_antitone,
    ``Erdos1045.ExplicitThreshold.errorBudget_eq_profile,
    ``Erdos1045.ExplicitThreshold.errorBudget_antitone,
    ``Erdos1045.ExplicitThreshold.threshold_pos,
    ``Erdos1045.ExplicitThreshold.threshold_cast,
    ``Erdos1045.ExplicitThreshold.log_threshold,
    ``Erdos1045.ExplicitThreshold.log_two_lower,
    ``Erdos1045.ExplicitThreshold.log_two_upper,
    ``Erdos1045.ExplicitThreshold.log_lower,
    ``Erdos1045.ExplicitThreshold.endpoint_numerator,
    ``Erdos1045.ExplicitThreshold.errorBudget_lt,
    ``Erdos1045.ExplicitThreshold.two_le_order,
    ``Erdos1045.ExplicitThreshold.logBudget_ge_one,
    ``Erdos1045.ExplicitThreshold.errorBudget_lt_millionth,
    ``Erdos1045.ExplicitThreshold.monomial_le_errorBudget,
    ``Erdos1045.ExplicitThreshold.monomial_lt_millionth,
    ``Erdos1045.ExplicitThreshold.logOrder,
    ``Erdos1045.ExplicitThreshold.logOrder_lower,
    ``Erdos1045.ExplicitThreshold.logOrder_upper,
    ``Erdos1045.ExplicitThreshold.selector_budget,
    ``Erdos1045.ExplicitThreshold.microscopic_hole_budget,
    ``Erdos1045.ExplicitThreshold.logarithmic_curvature_margin,
    ``Erdos1045.ExplicitThreshold.sqrt_monomial_lt,
    ``Erdos1045.ExplicitThreshold.localization_small,
    ``Erdos1045.ExplicitThreshold.closure_coefficient_small,
    ``Erdos1045.ExplicitThreshold.hessian_coefficient_small,
    ``Erdos1045.ExplicitThreshold.lens_curvature_bound_pos,
    ``Erdos1045.ExplicitThreshold.comparison_error_below_gap]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"THRESHOLD_AXIOM_AUDIT_PASS: {declarations.size} declarations"

#audit_explicit_threshold
#print axioms Erdos1045.ExplicitThreshold.errorBudget_lt
#print axioms Erdos1045.ExplicitThreshold.comparison_error_below_gap
