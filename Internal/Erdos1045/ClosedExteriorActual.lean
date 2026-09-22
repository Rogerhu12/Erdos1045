import Erdos1045.ExteriorModelBridge
import ExteriorEnvelopePerimeter
import BoundaryPolygonCanonical
import Erdos1045.ClosedGeometryAffine

/-! The classical exterior existence interface is constructed from geometry.
No Faber, boundary regularity, perimeter, or energy theorem remains an input. -/

namespace Erdos1045.ExteriorClassical

open Complex Metric Set ExteriorReduction Configuration HullGeometry
open scoped Topology
noncomputable section

theorem hull_nontrivial_of_injective {n : ℕ} (hn : 2 ≤ n) {z : Points n}
    (hz : Function.Injective z) : (hull z).Nontrivial := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  refine ⟨z i, subset_convexHull ℝ _ (mem_range_self i),
    z j, subset_convexHull ℝ _ (mem_range_self j), ?_⟩
  intro he
  have hv := congrArg Fin.val (hz he)
  norm_num [i, j] at hv

theorem hull_perm {n : ℕ} (z : Points n) (σ : Equiv.Perm (Fin n)) :
    hull (z ∘ σ) = hull z := by
  have hr : range (z ∘ σ) = range z := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨σ i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨σ.symm i, by simp⟩
  unfold hull
  rw [hr]

/-- The same actual model supplies the map, Faber identities, energy, ordered
nodes and perimeter bound required by the asymptotic proof. -/
theorem classicalExteriorExistence_proved : ClassicalExteriorExistence where
  model := by
    intro n hn z hz hP hf
    have hK : IsCompact (hull z) := (finite_range z).isCompact_convexHull ℝ
    have hconv : Convex ℝ (hull z) := convex_convexHull ℝ _
    obtain ⟨m⟩ := exists_convexExteriorModel hK hconv (hull_nontrivial_of_injective (by omega) hz)
    have hlength := m.circleLength_upper z hK
    have hL := m.radialMeanNorm_normalized_upper z hK hP
    obtain ⟨σ, a, har, hnode, hboundary⟩ :=
      ConvexExteriorModel.ordered_fekete_configuration_length_le (by omega) m hz hf hlength
    have hboundary' : boundaryLength (z ∘ σ) ≤ hullPerimeter (z ∘ σ) := by
      rw [hullPerimeter_perm_proved n z σ]
      exact hboundary
    let d := m.toExteriorData hK hconv hL (z ∘ σ) a har (fun i => (hnode i).symm) hboundary'
    refine ⟨σ, ⟨⟨d, ?_⟩⟩⟩
    exact m.toExteriorData_faberIdentities hK hconv hL (z ∘ σ) a har
      (fun i => (hnode i).symm) hboundary' (hull_perm z σ)

#print axioms classicalExteriorExistence_proved

end
end Erdos1045.ExteriorClassical
