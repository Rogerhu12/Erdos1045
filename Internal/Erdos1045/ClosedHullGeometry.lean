import Erdos1045.ClosedGeometryAffine
import Erdos1045.ClosedRegularGeometry
import Erdos1045.ClosedRegularPerimeter

namespace Erdos1045.HullGeometry

open Configuration
noncomputable section

/-- The sole remaining convex-geometry input is Reinhardt's perimeter inequality. -/
def ReinhardtPerimeterInequality : Prop :=
  ∀ n, 3 ≤ n → ∀ z : Points n, DiameterAtMost 1 z →
    hullPerimeter z ≤ diameterPerimeterBound n

/-- All nine other fields of the former convex-geometry interface are proved. -/
theorem classicalHullGeometry_of_reinhardt (H : ReinhardtPerimeterInequality) :
    ClassicalHullGeometry where
  nonneg := hullPerimeter_nonneg_proved
  continuous := hullPerimeter_continuous_proved
  affine := hullPerimeter_affine_proved
  perm := hullPerimeter_perm_proved
  monotone := hullPerimeter_monotone_proved
  distance_le_half := hullPerimeter_distance_le_half_proved
  regular_perimeter := hullPerimeter_regular_proved
  regular_discriminant := ClosedRegularGeometry.regular_discriminant
  regular_diameter := ClosedRegularGeometry.regular_diameter
  reinhardt := H

end
end Erdos1045.HullGeometry
