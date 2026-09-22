import BoundaryPolygonLength
import CanonicalExteriorModel
import FeketeBoundary

/-! The finite boundary-length estimate for the model actually constructed by
the Riemann mapping theorem. The only remaining numerical input is an upper
limit for its exterior-circle lengths. -/

namespace ExteriorReduction.ConvexExteriorModel

open Complex Metric Set Filter
open Erdos1045.ExteriorBoundary Erdos1045.CyclicAngles Erdos1045.Configuration
open scoped Topology
noncomputable section

variable {K : Set ℂ} (d : ConvexExteriorModel K)

theorem circleLength_map_eq_open {r : ℝ} (hr : 1 < r) :
    exteriorCircleLength d.map r = exteriorCircleLength d.openMap r := by
  apply intervalIntegral.integral_congr
  intro t _
  have heq : d.map =ᶠ[𝓝 ((r : ℂ) * unit t)] d.openMap := by
    filter_upwards [exteriorDisk_isOpen.mem_nhds (exterior_circle_mem hr t)] with w hw
    exact d.map_eq_open hw
  dsimp only
  rw [heq.deriv_eq]

theorem boundary_polygon_length_le {n : ℕ} (hn : 2 ≤ n) (a : Angles n)
    (hK : IsCompact K) (hconv : Convex ℝ K) {P : ℝ}
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 1,
      exteriorCircleLength d.openMap r ≤ P + ε) :
    boundaryLength (fun i : Fin n => d.map (unit (a.angle i))) ≤ P := by
  apply boundary_polygon_le_of_circle_length_upper hn a
    (fun _ hw => (d.map_hasDerivAt hw).differentiableAt.differentiableWithinAt)
    (d.map_continuous hK hconv)
  intro ε hε
  filter_upwards [hupper ε hε, self_mem_nhdsWithin] with r hr hr1
  rw [d.circleLength_map_eq_open hr1]
  exact hr

theorem ordered_boundary_configuration_length_le {n : ℕ} (hn : 2 ≤ n)
    (hK : IsCompact K) (hconv : Convex ℝ K) {z : Fin n → ℂ}
    (hz : Function.Injective z) (hfront : ∀ i, z i ∈ frontier K) {P : ℝ}
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 1,
      exteriorCircleLength d.openMap r ≤ P + ε) :
    ∃ (σ : Equiv.Perm (Fin n)) (a : Angles n),
      (∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi) ∧
      (∀ i : Fin n, d.map (unit (a.angle i)) = z (σ i)) ∧
      boundaryLength (fun i => z (σ i)) ≤ P := by
  obtain ⟨σ, a, hrange, hmap⟩ := ordered_boundary_preimages (by omega : 0 < n) hz
    (F := d.map) (fun i => by
      obtain ⟨u, hu, he⟩ := d.boundary_surjective hK hconv (hfront i)
      exact ⟨u, mem_sphere_zero_iff_norm.mpr hu, he⟩)
  refine ⟨σ, a, hrange, hmap, ?_⟩
  simpa only [hmap] using d.boundary_polygon_length_le hn a hK hconv hupper

/-- The sorting and length construction needed for a Fekete configuration.
The hull and exterior map remain fixed while only the finite indices rotate. -/
theorem ordered_fekete_configuration_length_le {n : ℕ} (hn : 2 ≤ n)
    {z : Fin n → ℂ} (m : ConvexExteriorModel (Erdos1045.ExteriorClassical.hull z))
    (hz : Function.Injective z) (hf : Erdos1045.ExteriorClassical.Fekete z) {P : ℝ}
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℝ in 𝓝[>] 1,
      exteriorCircleLength m.openMap r ≤ P + ε) :
    ∃ (σ : Equiv.Perm (Fin n)) (a : Angles n),
      (∀ i : Fin n, 0 ≤ a.angle i ∧ a.angle i < 2 * Real.pi) ∧
      (∀ i : Fin n, m.map (unit (a.angle i)) = z (σ i)) ∧
      boundaryLength (fun i => z (σ i)) ≤ P := by
  exact m.ordered_boundary_configuration_length_le hn
    ((Set.finite_range z).isCompact_convexHull ℝ) (convex_convexHull ℝ _)
    hz (fekete_points_mem_frontier hn hz hf) hupper

#print axioms circleLength_map_eq_open
#print axioms boundary_polygon_length_le
#print axioms ordered_boundary_configuration_length_le
#print axioms ordered_fekete_configuration_length_le

end
end ExteriorReduction.ConvexExteriorModel
