import StructuralNote.ExplicitPressureThreshold
import Lean.Util.CollectAxioms
import Lean.Elab.Command
open Lean Elab Command
elab "#audit_explicit_pressure" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[    ``StructuralNote.ExplicitPressureThreshold.smallnessThreshold,
    ``StructuralNote.ExplicitPressureThreshold.coefficients_small,
    ``StructuralNote.ExplicitPressureThreshold.log_quarter_lower,
    ``StructuralNote.ExplicitPressureThreshold.signThreshold,
    ``StructuralNote.ExplicitPressureThreshold.scaled_potential_large,
    ``StructuralNote.ExplicitPressureThreshold.marginConstant,
    ``StructuralNote.ExplicitPressureThreshold.marginThreshold,
    ``StructuralNote.ExplicitPressureThreshold.pressure_margin,
    ``StructuralNote.ExplicitPressureThreshold.near_maximum_signs,
    ``StructuralNote.ExplicitPressureThreshold.activeWordThreshold,
    ``StructuralNote.ExplicitPressureThreshold.model_activeHalfSign_pressure_pos]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
  logInfo m!"PRESSURE_THRESHOLD_AUDIT_PASS: {declarations.size} declarations"
#audit_explicit_pressure