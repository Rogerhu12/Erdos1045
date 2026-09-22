import StructuralNote.ExplicitThresholdFunctions
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
elab "#audit_explicit_functions" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[    ``Erdos1045.ExplicitThreshold.majorant,
    ``Erdos1045.ExplicitThreshold.majorant_pos,
    ``Erdos1045.ExplicitThreshold.abs_lt_majorant,
    ``Erdos1045.ExplicitThreshold.le_majorant,
    ``Erdos1045.ExplicitThreshold.decayThreshold,
    ``Erdos1045.ExplicitThreshold.growthThreshold,
    ``Erdos1045.ExplicitThreshold.logBudget_le_small_power,
    ``Erdos1045.ExplicitThreshold.logBudget_tenth_bound,
    ``Erdos1045.ExplicitThreshold.decayThreshold_two_le,
    ``Erdos1045.ExplicitThreshold.decay_small,
    ``Erdos1045.ExplicitThreshold.growth_log_gt,
    ``Erdos1045.ExplicitThreshold.monomial_small,
    ``Erdos1045.ExplicitThreshold.inverseSqrtThreshold,
    ``Erdos1045.ExplicitThreshold.inverse_sqrt_small,
    ``Erdos1045.ExplicitThreshold.comparison_error_small,
    ``Erdos1045.ExplicitThreshold.sqrt_monomial_small,
    ``Erdos1045.ExplicitThreshold.linearGrowthThreshold,
    ``Erdos1045.ExplicitThreshold.log_dominates_sqrt,
    ``Erdos1045.ExplicitThreshold.inverseThreshold,
    ``Erdos1045.ExplicitThreshold.inverse_small]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"THRESHOLD_FUNCTIONS_AUDIT_PASS: {declarations.size} declarations"
#audit_explicit_functions