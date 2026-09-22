import StructuralNote.ExplicitPressureNumerical
import StructuralNote.ExplicitGradientThreshold
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
elab "#audit_explicit_numeric" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[    ``StructuralNote.ExplicitPressureNumerical.budget_bound,
    ``StructuralNote.ExplicitPressureNumerical.center_bound,
    ``StructuralNote.ExplicitPressureNumerical.angle_bound,
    ``StructuralNote.ExplicitPressureNumerical.center_step_bound,
    ``StructuralNote.ExplicitPressureNumerical.physical_step_bound,
    ``StructuralNote.ExplicitPressureNumerical.diameter_step_bound,
    ``StructuralNote.ExplicitPressureNumerical.derotation_bound,
    ``StructuralNote.ExplicitPressureNumerical.center_error_bound,
    ``StructuralNote.ExplicitPressureNumerical.margin_constant_bounds,
    ``StructuralNote.ExplicitPressureNumerical.concreteThreshold,
    ``StructuralNote.ExplicitPressureNumerical.marginThreshold_le_concrete,
    ``StructuralNote.ExplicitPressureNumerical.pressure_margin_concrete,
    ``StructuralNote.ExplicitGradientThreshold.headCutoff,
    ``StructuralNote.ExplicitGradientThreshold.pairTolerance,
    ``StructuralNote.ExplicitGradientThreshold.headCutoff_pos,
    ``StructuralNote.ExplicitGradientThreshold.pairTolerance_pos,
    ``StructuralNote.ExplicitGradientThreshold.harmonic_le_cast,
    ``StructuralNote.ExplicitGradientThreshold.tail_small,
    ``StructuralNote.ExplicitGradientThreshold.gradient_small]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"PRESSURE_NUMERIC_AND_GRADIENT_AUDIT_PASS: {declarations.size} declarations"
#audit_explicit_numeric