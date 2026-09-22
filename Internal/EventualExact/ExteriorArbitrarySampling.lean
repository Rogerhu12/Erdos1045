import Erdos1045.ExteriorClassical
import ExteriorEnvelopeCircle
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Every cyclic sample of the same actual exterior boundary has length at most
the perimeter of its convex hull. The sample need not be the original nodes. -/

noncomputable section

open scoped Topology

namespace Erdos1045.EventualExact.ExteriorArbitrarySampling

open Complex Metric Set Filter Configuration ExteriorBoundary ExteriorClassical
open ExteriorReduction HullGeometry

theorem map_eq_model {n : ℕ} {z : Points n} (d : ExteriorData z)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    d.map w = exteriorFromModel d.model (d.offset - deriv d.model 0) w := by
  rw [← laurentBoundaryMap_eq_exterior d.model_analytic (d.offset - deriv d.model 0) hw]
  simp only [ExteriorData.map, ExteriorData.coefficient, laurentBoundaryMap, d.model_zero]
  ring

theorem circleLength_eq_model {n : ℕ} {z : Points n} (d : ExteriorData z)
    {r : ℝ} (hr : 1 < r) :
    exteriorCircleLength d.map r =
      exteriorCircleLength (exteriorFromModel d.model (d.offset - deriv d.model 0)) r := by
  apply intervalIntegral.integral_congr
  intro t _
  have he : d.map =ᶠ[𝓝 ((r : ℂ) * unit t)]
      exteriorFromModel d.model (d.offset - deriv d.model 0) := by
    filter_upwards [exteriorDisk_isOpen.mem_nhds (exterior_circle_mem hr t)] with w hw
    exact map_eq_model d hw
  dsimp only
  rw [he.deriv_eq]

/-- Uniform radial convergence follows from continuity on a compact annulus;
it does not require a continuous boundary derivative. -/
theorem uniform_radial_close {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 1, ∀ t : ℝ,
      ‖d.map ((r : ℂ) * unit t) - d.map (unit t)‖ < ε := by
  let S : Set ℂ := closedExteriorDisk ∩ closedBall 0 2
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) 2).inter_left
    (isClosed_le continuous_const continuous_norm)
  have hcont : ContinuousOn d.map S := HF.map_continuous.mono (fun _ hw => hw.1)
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hS.uniformContinuousOn_of_continuous hcont) ε hε
  have hrδ : ∀ᶠ r : ℝ in 𝓝[>] 1, r < 1 + δ :=
    (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + δ)).filter_mono nhdsWithin_le_nhds
  have hr2 : ∀ᶠ r : ℝ in 𝓝[>] 1, r < 2 :=
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hrδ, hr2] with r hr hrδ hr2 t
  have hr1 : 1 < r := hr
  have hr0 : 0 < r := lt_trans zero_lt_one hr1
  have hn : ‖(r : ℂ) * unit t‖ = r := by simp [abs_of_pos hr0]
  have hx : (r : ℂ) * unit t ∈ S := by
    refine ⟨?_, ?_⟩
    · change 1 ≤ ‖(r : ℂ) * unit t‖
      rw [hn]
      exact hr1.le
    · rw [mem_closedBall, dist_zero_right, hn]
      exact hr2.le
  have hy : unit t ∈ S := by simp [S, closedExteriorDisk, mem_closedBall, dist_zero_right]
  have hd : dist ((r : ℂ) * unit t) (unit t) = r - 1 := by
    rw [dist_eq_norm, show (r : ℂ) * unit t - unit t = ((r - 1 : ℝ) : ℂ) * unit t by
      push_cast; ring]
    rw [norm_mul, norm_unit, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hr1)]
  have h := hclose _ hx _ hy (by rw [hd]; linarith)
  simpa only [dist_eq_norm] using h

theorem boundary_projection_le {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (t θ : ℝ) :
    (d.map (unit t) * Complex.exp (-((θ : ℂ) * I))).re ≤ support z θ := by
  have hK : IsCompact (hull z) := (finite_range z).isCompact_convexHull ℝ
  have hfront : d.map (unit t) ∈ frontier (hull z) := by
    rw [← HF.boundary_image]
    exact ⟨unit t, norm_unit t, rfl⟩
  exact projection_le_support_of_mem_convexHull z (hK.isClosed.frontier_subset hfront) θ

/-- The required upper limit is proved for arbitrary ExteriorData, not just
the specially constructed ConvexExteriorModel record. -/
theorem circleLength_upper {n : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) :
    ∀ ε > 0, ∀ᶠ r : ℝ in 𝓝[>] 1, exteriorCircleLength d.map r ≤ hullPerimeter z + ε := by
  intro ε hε
  have hπ : 0 < 2 * Real.pi := by positivity
  filter_upwards [uniform_radial_close d HF (div_pos hε hπ), self_mem_nhdsWithin] with r hr hr1
  have hbound (t θ : ℝ) :
      (exteriorFromModel d.model (d.offset - deriv d.model 0) ((r : ℂ) * unit t) *
        Complex.exp (-((θ : ℂ) * I))).re ≤ support z θ + ε / (2 * Real.pi) := by
    rw [← map_eq_model d (exterior_circle_mem hr1 t)]
    have hp := boundary_projection_le d HF t θ
    have hd : ((d.map ((r : ℂ) * unit t) - d.map (unit t)) *
        Complex.exp (-((θ : ℂ) * I))).re ≤ ‖d.map ((r : ℂ) * unit t) - d.map (unit t)‖ := by
      exact (re_le_norm _).trans_eq (by simp [Complex.norm_exp])
    rw [sub_mul, Complex.sub_re] at hd
    linarith [hr t]
  have he := ExteriorEnvelope.model_circle_length_le_support d.model_analytic d.model_zero
    d.capacity_pos d.model_derivative_ne d.model_criterion hr1
    (support_continuous z) (support_periodic z) hbound
  rw [circleLength_eq_model d hr1]
  change _ ≤ hullPerimeter z + 2 * Real.pi * (ε / (2 * Real.pi)) at he
  convert he using 1
  field_simp

/-- Arbitrary cyclic boundary sampling, with no assumption that the sample is
the distinguished node list carried by d. -/
theorem boundary_sampling_le {n m : ℕ} {z : Points n} (d : ExteriorData z)
    (HF : FaberIdentities d) (hm : 2 ≤ m) (b : CyclicAngles.Angles m) :
    boundaryLength (fun i : Fin m => d.map (unit (b.angle i))) ≤ hullPerimeter z := by
  exact boundary_polygon_le_of_circle_length_upper hm b
    (fun w hw => (HF.map_derivative w hw).differentiableAt.differentiableWithinAt)
    HF.map_continuous (circleLength_upper d HF)

end Erdos1045.EventualExact.ExteriorArbitrarySampling
