import Erdos1045.ExplicitStatement
import EventualExact.ExplicitPerimeter
import StructuralNote.RewrittenMaxima

/-! Public odd-order and perimeter conclusions at a common concrete cutoff. -/

namespace Erdos1045.Internal.ExplicitRegular

open Erdos1045.Configuration Erdos1045.HullGeometry Erdos1045.EventualExact
open Erdos1045.GlobalProof
open StructuralNote StructuralNote.RewrittenMaxima
open StructuralNote.RewrittenMainUniqueness
noncomputable section

theorem explicitOddClaims : Internal.OddThresholdClaims := by
  intro n hn hodd
  have hn4 : 4 ≤ n := ExplicitPerimeter.orderThreshold_ge_four.trans hn
  obtain ⟨hu, ⟨hc, hv⟩, hr⟩ := ExplicitPerimeter.odd_diameter_two_exact hn hodd
  have hM : M n = diameterTwoMaximum n := by
    apply supremum_eq_of_attained_bound
    · exact ⟨diameterTwoRegular n, hc, hv⟩
    · rintro x ⟨z, hz, rfl⟩
      exact hu z hz
  have hreg : ∀ z : Points n, DiameterAtMost 2 z → discriminant z = M n →
      Configuration.IsRegular z := by
    intro z hz hD
    exact hr z hz (hD.trans hM)
  refine ⟨hM, ⟨diameterTwoRegular n, hc, hv.trans hM.symm⟩, hreg, ?_⟩
  intro z w hz hDz hw hDw
  exact regular_equal_discriminant_directRigid (by omega) z w
    (hreg z hz hDz) (hreg w hw hDw) (hDz.trans hDw.symm)

theorem explicitPerimeterClaims : Statement.PerimeterCharacterization := by
  intro n hn
  let H := classicalBackground_proved.toClassicalAnalysis.geometry
  have hn4 : 4 ≤ n := ExplicitPerimeter.orderThreshold_ge_four.trans hn
  have hr := fun z (hz : PerimeterExtremal n z) =>
    ExplicitPerimeter.perimeter_extremal_regular hn hz
  have hW : W n = perimeterMaximum n := by
    apply supremum_eq_of_attained_bound
    · exact ⟨perimeterRegular n, (perimeterRegular_perimeter H (by omega)).le,
        perimeterRegular_discriminant H (by omega)⟩
    · rintro x ⟨z, hz, rfl⟩
      exact perimeter_bound_of_regular_extremals H (by omega) hr z hz
  have hreg : ∀ z : Points n, hullPerimeter z ≤ 2 * Real.pi →
      discriminant z = W n → Configuration.IsRegular z := by
    intro z hz hD
    exact hr z (perimeterExtremal_of_attains H (by omega) hr z hz (hD.trans hW))
  refine ⟨?_, ?_, hreg, ?_⟩
  · change W n = _
    rw [hW]
    simp only [perimeterMaximum, circlePerimeter, exponent]
    ring
  · exact ⟨perimeterRegular n, (perimeterRegular_perimeter H (by omega)).le,
      (perimeterRegular_discriminant H (by omega)).trans hW.symm⟩
  · intro z w hz hDz hw hDw
    exact regular_equal_discriminant_directRigid (by omega) z w
      (hreg z hz hDz) (hreg w hw hDw) (hDz.trans hDw.symm)

end
end Erdos1045.Internal.ExplicitRegular

namespace Erdos1045

/-- Exact maximum, attainment, regularity and rigid uniqueness for every odd
order at least `2^100000000`. -/
theorem explicit_odd : Internal.OddThresholdClaims :=
  Internal.ExplicitRegular.explicitOddClaims

/-- Exact maximum, attainment, regularity and rigid uniqueness for the perimeter
problem at every order at least `2^100000000`. -/
theorem explicit_perimeter : Statement.PerimeterCharacterization :=
  Internal.ExplicitRegular.explicitPerimeterClaims

end Erdos1045
