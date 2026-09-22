import Erdos1045.ExplicitProof
import Erdos1045.ExplicitRegularProof
import Erdos1045.Internal.KKT
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

elab "#audit_explicit_final" : command => do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let declarations : Array Name := #[
    ``Erdos1045.Statement.evenThreshold,
    ``Erdos1045.Internal.EvenThresholdClaims,
    ``StructuralNote.ExplicitKernelSelection.finiteImprovement,
    ``StructuralNote.ExplicitEvenCertificate.certificate,
    ``StructuralNote.ExplicitEvenThreshold.actual_extremizers_unique,
    ``StructuralNote.ExplicitEvenThreshold.actual_extremizer_diameterGraph,
    ``StructuralNote.ExplicitEvenThreshold.actual_extremizer_euclidean_symmetries,
    ``StructuralNote.ExplicitEvenThreshold.even_maximum_single_polynomial_root,
    ``StructuralNote.ExplicitEvenThreshold.certificate,
    ``StructuralNote.ExplicitEvenThreshold.even_geometry,
    ``StructuralNote.ExplicitEvenNumerical.orderThreshold_le_concrete,
    ``Erdos1045.explicit_even,
    ``Erdos1045.Statement.regularThreshold,
    ``Erdos1045.EventualExact.ExplicitPerimeter.perimeter_extremal_regular,
    ``Erdos1045.EventualExact.ExplicitPerimeter.sharp_perimeter,
    ``Erdos1045.EventualExact.ExplicitPerimeter.odd_diameter_two_exact,
    ``Erdos1045.explicit_odd,
    ``Erdos1045.explicit_perimeter,
    ``StructuralNote.ExplicitKKTThreshold.actual_maximizer_unique_multipliers,
    ``StructuralNote.ExplicitKKTThreshold.positive_original_certificate,
    ``Erdos1045.Statement.KKT.unique_positive_kkt
  ]
  for decl in declarations do
    let axioms ← collectAxioms decl
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom in {decl}: {ax}"
    logInfo m!"{decl}: {axioms}"
  logInfo m!"EXPLICIT_FINAL_AUDIT_PASS: {declarations.size} declarations"

#audit_explicit_final
