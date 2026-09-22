import ExteriorEnvelopeCircle
import ExteriorEnvelopeSupport
import BoundaryPolygonCanonical
import ExteriorEnvelopeRadial

/-! The upper limit of lengths of the actual exterior circles is the support
integral of the finite convex hull. No boundary smoothness is assumed. -/

namespace ExteriorReduction.ConvexExteriorModel

open Complex Metric Set Filter
open Erdos1045.Configuration Erdos1045.ExteriorBoundary Erdos1045.HullGeometry
open scoped Topology
open ExteriorEnvelope

noncomputable section

variable {K : Set ℂ} (d : ConvexExteriorModel K)

theorem inverseMap_norm_atTop (hK : IsCompact K) :
    Tendsto (fun p => ‖d.inverseMap p‖) (cocompact ℂ) atTop := by
  have hΩ := invertedComplement_isOpen hK d.center
  have hzero := zero_mem_invertedComplement K d.center
  have hf0 : DifferentiableAt ℂ d.f 0 :=
    d.f_differentiable.differentiableAt (hΩ.mem_nhds hzero)
  have hdf0 : deriv d.f 0 ≠ 0 := RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
    hΩ isOpen_ball d.f_differentiable d.g_differentiable d.f_bijective.mapsTo d.inverse.1 hzero
  exact exteriorInverse_norm_atTop hf0 d.f_zero hdf0 d.center

theorem exists_circle_collar (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 1 < r → r < 1 + δ → ∀ t : ℝ,
      infDist (d.openMap ((r : ℂ) * unit t)) K < ε := by
  obtain ⟨_, hΦ, _, hΦmap, hinv, _⟩ := d.open_biholomorphic hK
  obtain ⟨δ, hδ, hclose⟩ := exists_collar_infDist_lt hΦ.continuousOn hΦmap
    (fun _ hw => hinv.1 hw) (d.inverseMap_norm_atTop hK) hε
  refine ⟨δ, hδ, fun r hr hrδ t => ?_⟩
  have hnorm : ‖(r : ℂ) * unit t‖ = r := by
    simp [norm_unit, abs_of_pos (lt_trans zero_lt_one hr)]
  apply hclose
  · rwa [hnorm]
  · rwa [hnorm]

theorem circleLength_upper {n : ℕ} (z : Points n)
    (d : ConvexExteriorModel (convexHull ℝ (range z)))
    (hK : IsCompact (convexHull ℝ (range z))) :
    ∀ ε > 0, ∀ᶠ r in 𝓝[>] (1 : ℝ),
      exteriorCircleLength d.openMap r ≤ hullPerimeter z + ε := by
  intro ε hε
  have hπ : 0 < 2 * Real.pi := by positivity
  obtain ⟨δ, hδ, hclose⟩ := d.exists_circle_collar hK (div_pos hε hπ)
  have hrad : ∀ᶠ r in 𝓝[>] (1 : ℝ), r < 1 + δ :=
    (eventually_lt_nhds (show (1 : ℝ) < 1 + δ by linarith)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hrad, self_mem_nhdsWithin] with r hrδ hr
  have hr1 : 1 < r := hr
  have hh := model_circle_length_le_support d.q_analytic d.q_zero d.capacity_pos
    (fun _ hz => d.D_ne_zero hK hz)
    (fun _ hz => (d.criterion_pos hK (convex_convexHull ℝ _) hz).le)
    hr1 (support_continuous z) (support_periodic z)
    (fun t θ => projection_le_support_add_of_infDist_lt z ⟨d.center, d.center_mem⟩
      (hclose r hr1 hrδ t) θ)
  change exteriorCircleLength d.openMap r ≤ hullPerimeter z +
    2 * Real.pi * (ε / (2 * Real.pi)) at hh
  convert hh using 1
  field_simp

theorem circleLength_map_upper {n : ℕ} (z : Points n)
    (d : ConvexExteriorModel (convexHull ℝ (range z)))
    (hK : IsCompact (convexHull ℝ (range z))) :
    ∀ ε > 0, ∀ᶠ r in 𝓝[>] (1 : ℝ),
      exteriorCircleLength d.map r ≤ hullPerimeter z + ε := by
  intro ε hε
  filter_upwards [d.circleLength_upper z hK ε hε, self_mem_nhdsWithin] with r hr hr1
  rwa [d.circleLength_map_eq_open hr1]

theorem radialMeanNorm_upper {n : ℕ} (z : Points n)
    (d : ConvexExteriorModel (convexHull ℝ (range z)))
    (hK : IsCompact (convexHull ℝ (range z))) :
    ∀ ε > 0, ∀ᶠ ρ in 𝓝[<] (1 : ℝ),
      d.capacity * radialMeanNorm d.D ρ ≤ hullPerimeter z / (2 * Real.pi) + ε :=
  radialMeanNorm_upper_of_circleLength_upper d.q_analytic d.capacity_pos d.q_zero
    d.center (d.circleLength_upper z hK)

theorem radialMeanNorm_normalized_upper {n : ℕ} (z : Points n)
    (d : ConvexExteriorModel (convexHull ℝ (range z)))
    (hK : IsCompact (convexHull ℝ (range z))) (hP : hullPerimeter z = 2 * Real.pi) :
    ∀ ε > 0, ∀ᶠ ρ in 𝓝[<] (1 : ℝ),
      d.capacity * radialMeanNorm d.D ρ ≤ 1 + ε := by
  have hh := d.radialMeanNorm_upper z hK
  simpa only [hP, div_self (show 2 * Real.pi ≠ 0 by positivity)] using hh

#print axioms circleLength_upper
#print axioms circleLength_map_upper
#print axioms radialMeanNorm_normalized_upper

end
end ExteriorReduction.ConvexExteriorModel
