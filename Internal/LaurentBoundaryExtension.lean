import LaurentModelExpansion
import ExteriorInfinity
import ExteriorEnvelopeTopology
import Erdos1045.ClosedLaurent
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Sequences

/-! The continuous closed-exterior map from the actual absolutely convergent
Laurent series. It agrees with the conformal map on the open exterior. -/

namespace ExteriorReduction

open Complex Metric Set Filter
open Erdos1045.ExteriorClassical
open scoped Topology
noncomputable section

def closedExteriorDisk : Set ℂ := {w | 1 ≤ ‖w‖}

def laurentBoundaryMap (q : ℂ → ℂ) (A w : ℂ) : ℂ :=
  q 0 * w + (A + deriv q 0) + laurent (modelLaurentCoefficient q) w

theorem closedExterior_ne_zero {w : ℂ} (hw : w ∈ closedExteriorDisk) : w ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hw)

theorem laurent_continuousOn_closedExterior {a : ℕ → ℂ}
    (ha : Summable (fun m => ‖a m‖)) : ContinuousOn (laurent a) closedExteriorDisk := by
  apply continuousOn_tsum
  · intro m
    exact continuousOn_const.mul
      ((continuousOn_id.inv₀ (fun _ hw => closedExterior_ne_zero hw)).pow m)
  · exact ha
  · intro m w hw
    rw [norm_mul, norm_pow, norm_inv]
    apply mul_le_of_le_one_right (norm_nonneg _)
    exact pow_le_one₀ (inv_nonneg.mpr (norm_nonneg _))
      ((inv_le_one₀ (norm_pos_iff.mpr (closedExterior_ne_zero hw))).mpr hw)

theorem laurentBoundaryMap_continuousOn {q : ℂ → ℂ}
    (ha : SobolevCoefficients (modelLaurentCoefficient q)) (A : ℂ) :
    ContinuousOn (laurentBoundaryMap q A) closedExteriorDisk :=
  ((continuousOn_const.mul continuousOn_id).add continuousOn_const).add
    (laurent_continuousOn_closedExterior (Erdos1045.ClosedSeries.laurent_absolute _ ha))

theorem laurentBoundaryMap_eq_exterior {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A : ℂ)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    laurentBoundaryMap q A w = exteriorFromModel q A w :=
  (model_laurent_expansion hq A hw).symm

def radialApproach (k : ℕ) : ℝ := 1 + (1 / 2 : ℝ) ^ k

theorem radialApproach_gt_one (k : ℕ) : 1 < radialApproach k := by
  unfold radialApproach
  linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) k]

theorem radialApproach_tendsto : Tendsto radialApproach atTop (𝓝 1) := by
  change Tendsto (fun k : ℕ => 1 + (1 / 2 : ℝ) ^ k) atTop (𝓝 1)
  simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1))

theorem norm_radialApproach_mul {u : ℂ} (hu : ‖u‖ = 1) (k : ℕ) :
    ‖(radialApproach k : ℂ) * u‖ = radialApproach k := by
  rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_trans zero_lt_one (radialApproach_gt_one k))]

theorem radialApproach_mul_tendsto (u : ℂ) :
    Tendsto (fun k => (radialApproach k : ℂ) * u) atTop (𝓝 u) := by
  simpa using (Complex.continuous_ofReal.tendsto 1 |>.comp radialApproach_tendsto).mul_const u

theorem boundary_radial_tendsto {F : ℂ → ℂ}
    (hF : ContinuousOn F closedExteriorDisk) {u : ℂ} (hu : ‖u‖ = 1) :
    Tendsto (fun k => F ((radialApproach k : ℂ) * u)) atTop (𝓝 (F u)) := by
  apply (hF u (show u ∈ closedExteriorDisk by simp [closedExteriorDisk, hu])).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨radialApproach_mul_tendsto u,
    .of_forall fun k => by
      change 1 ≤ ‖(radialApproach k : ℂ) * u‖
      rw [norm_radialApproach_mul hu]
      exact (radialApproach_gt_one k).le⟩

/-- Any continuous extension of the actual exterior map sends the circle to
the frontier. The scalar inverse envelope is enough; no boundary inverse is used. -/
theorem boundary_image_subset_frontier {K : Set ℂ} {F Ψ Φ : ℂ → ℂ}
    (hF : ContinuousOn F closedExteriorDisk)
    (hEq : EqOn F Ψ exteriorDisk)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hU : Continuous (ExteriorEnvelope.inverseNormEnvelope K Φ)) :
    F '' sphere (0 : ℂ) 1 ⊆ frontier K := by
  rintro _ ⟨u, hu, rfl⟩
  have hun : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
  have hw (k : ℕ) : (radialApproach k : ℂ) * u ∈ exteriorDisk := by
    change 1 < ‖(radialApproach k : ℂ) * u‖
    rw [norm_radialApproach_mul hun]
    exact radialApproach_gt_one k
  have ht := boundary_radial_tendsto hF hun
  have hOut (k : ℕ) : F ((radialApproach k : ℂ) * u) ∈ Kᶜ := by
    rw [hEq (hw k)]
    exact hΨmap (hw k)
  have hUEq (k : ℕ) : ExteriorEnvelope.inverseNormEnvelope K Φ
      (F ((radialApproach k : ℂ) * u)) = radialApproach k := by
    rw [ExteriorEnvelope.inverseNormEnvelope_eq_norm (hOut k), hEq (hw k),
      hleft _ (hw k), norm_radialApproach_mul hun]
  have hUone : ExteriorEnvelope.inverseNormEnvelope K Φ (F u) = 1 := by
    have hh := (hU.tendsto (F u)).comp ht
    simp only [Function.comp_def, hUEq] at hh
    exact tendsto_nhds_unique hh radialApproach_tendsto
  have hFK : F u ∈ K := by
    by_contra hn
    rw [ExteriorEnvelope.inverseNormEnvelope_eq_norm hn] at hUone
    have hh := hΦmap hn
    change 1 < ‖Φ (F u)‖ at hh
    linarith
  rw [frontier_eq_closure_inter_closure]
  exact ⟨subset_closure hFK, mem_closure_of_tendsto ht (.of_forall hOut)⟩

/-- Every frontier point has a circle preimage. Only compactness of a bounded
sequence of inverse images is needed; boundary injectivity is not asserted. -/
theorem frontier_subset_boundary_image {K : Set ℂ} {F Ψ Φ : ℂ → ℂ}
    (hK : IsClosed K) (hF : ContinuousOn F closedExteriorDisk)
    (hEq : EqOn F Ψ exteriorDisk)
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hright : ∀ v ∈ Kᶜ, Ψ (Φ v) = v)
    (hU : Continuous (ExteriorEnvelope.inverseNormEnvelope K Φ)) :
    frontier K ⊆ F '' sphere (0 : ℂ) 1 := by
  intro x hx
  have hxK := hK.frontier_subset hx
  have hxC : x ∈ closure Kᶜ := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  obtain ⟨y, hyK, hy⟩ := mem_closure_iff_seq_limit.mp hxC
  have hn : Tendsto (fun n => ‖Φ (y n)‖) atTop (𝓝 1) := by
    have hh := (hU.tendsto x).comp hy
    simpa only [Function.comp_def, ExteriorEnvelope.inverseNormEnvelope_eq_one hxK,
      ExteriorEnvelope.inverseNormEnvelope_eq_norm (hyK _)] using hh
  have hb : ∃ᶠ n in atTop, Φ (y n) ∈ closedBall (0 : ℂ) 2 := by
    apply Filter.Eventually.frequently
    filter_upwards [hn.eventually (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with n hn
    exact mem_closedBall_zero_iff.mpr hn.le
  obtain ⟨u, _, φ, hφ, hu⟩ := (isCompact_closedBall (0 : ℂ) 2).tendsto_subseq' hb
  have hun : ‖u‖ = 1 := tendsto_nhds_unique hu.norm (hn.comp hφ.tendsto_atTop)
  have hFu : Tendsto (fun n => F (Φ (y (φ n)))) atTop (𝓝 (F u)) := by
    apply (hF u (show u ∈ closedExteriorDisk from hun.ge)).tendsto.comp
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hu, .of_forall fun n =>
      (show (1 : ℝ) ≤ ‖Φ (y (φ n))‖ from (hΦmap (hyK (φ n))).le)⟩
  have he : (fun n => F (Φ (y (φ n)))) = (fun n => y (φ n)) := by
    funext n
    rw [hEq (hΦmap (hyK (φ n))), hright _ (hyK (φ n))]
  rw [he] at hFu
  exact ⟨u, mem_sphere_zero_iff_norm.mpr hun, tendsto_nhds_unique hFu (hy.comp hφ.tendsto_atTop)⟩

theorem boundary_image_eq_frontier {K : Set ℂ} {F Ψ Φ : ℂ → ℂ}
    (hK : IsClosed K) (hF : ContinuousOn F closedExteriorDisk)
    (hEq : EqOn F Ψ exteriorDisk)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hright : ∀ v ∈ Kᶜ, Ψ (Φ v) = v)
    (hU : Continuous (ExteriorEnvelope.inverseNormEnvelope K Φ)) :
    F '' sphere (0 : ℂ) 1 = frontier K :=
  Set.Subset.antisymm (boundary_image_subset_frontier hF hEq hΨmap hΦmap hleft hU)
    (frontier_subset_boundary_image hK hF hEq hΦmap hright hU)

#print axioms laurentBoundaryMap_continuousOn
#print axioms boundary_image_subset_frontier
#print axioms boundary_image_eq_frontier

end
end ExteriorReduction
