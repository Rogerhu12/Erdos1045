import Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

/-- The submitted theorem contains the canonical thresholded conclusions. -/
example : Erdos1045.Statement.DiameterCharacterization := Erdos1045.main.1
example : Erdos1045.Statement.PerimeterCharacterization := Erdos1045.main.2.1
example : Erdos1045.Statement.Algebraic.CertificateAboveThreshold := Erdos1045.main.2.2.2.1

elab "#audit_public_result" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let axioms ← collectAxioms ``Erdos1045.main
  for ax in axioms do
    unless allowed.contains ax do
      throwError "Unexpected axiom in Erdos1045.main: {ax}"
  logInfo m!"Erdos1045.main transitive axioms: {axioms}"
  logInfo "ERDOS1045_PUBLIC_AXIOM_AUDIT_PASS"

#audit_public_result

example : Erdos1045.Statement.KKT.UniquePositiveKKT := Erdos1045.main.2.2.2.2
