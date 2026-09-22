import ExteriorExistence
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact

/-! Scalar boundary control for genuine exterior inverse maps. No boundary
extension or boundary injectivity of either conformal map is assumed. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

theorem bounds_of_norm_tendsto_infty {F : ℂ → ℂ}
    (hF : Tendsto (fun w => ‖F w‖) (cocompact ℂ) atTop) (B : ℝ) :
    ∃ R : ℝ, ∀ w : ℂ, R ≤ ‖w‖ → B ≤ ‖F w‖ := by
  have he := hF.eventually_ge_atTop B
  rw [← cobounded_eq_cocompact] at he
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  exact ⟨R, hR⟩

def inverseNormEnvelope (K : Set ℂ) (Φ : ℂ → ℂ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ K then 1 else ‖Φ z‖

theorem inverseNormEnvelope_eq_one {K : Set ℂ} {Φ : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ K) : inverseNormEnvelope K Φ z = 1 := by
  simp [inverseNormEnvelope, hz]

theorem inverseNormEnvelope_eq_norm {K : Set ℂ} {Φ : ℂ → ℂ} {z : ℂ}
    (hz : z ∉ K) : inverseNormEnvelope K Φ z = ‖Φ z‖ := by
  simp [inverseNormEnvelope, hz]

theorem one_le_inverseNormEnvelope {K : Set ℂ} {Φ : ℂ → ℂ}
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk) (z : ℂ) :
    1 ≤ inverseNormEnvelope K Φ z := by
  by_cases hz : z ∈ K
  · simp [inverseNormEnvelope, hz]
  · simpa [inverseNormEnvelope, hz] using (hΦmap hz).le

/-- The inverse modulus extends continuously with value one across the omitted
set. The only control at infinity used here is properness of the forward map. -/
theorem continuous_inverseNormEnvelope {K : Set ℂ} {Ψ Φ : ℂ → ℂ}
    (hK : IsClosed K)
    (hΨ : ContinuousOn Ψ exteriorDisk) (hΦ : ContinuousOn Φ Kᶜ)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hright : ∀ v ∈ Kᶜ, Ψ (Φ v) = v)
    (hΨinfty : Tendsto (fun w => ‖Ψ w‖) (cocompact ℂ) atTop) :
    Continuous (inverseNormEnvelope K Φ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ K
  · rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨R, hR⟩ := bounds_of_norm_tendsto_infty hΨinfty (‖x‖ + 1)
    let A : Set ℂ := closedBall 0 R ∩ {w : ℂ | 1 + ε ≤ ‖w‖}
    have hAc : IsCompact A := (isCompact_closedBall 0 R).inter_right
      (isClosed_le continuous_const continuous_norm)
    have hAext : A ⊆ exteriorDisk := by
      intro w hw
      exact lt_of_lt_of_le (by linarith : (1 : ℝ) < 1 + ε) hw.2
    have hImg : IsCompact (Ψ '' A) := hAc.image_of_continuousOn (hΨ.mono hAext)
    have hxImg : x ∉ Ψ '' A := by
      rintro ⟨w, hw, hweq⟩
      exact hΨmap (hAext hw) (hweq ▸ hx)
    have hn : {v : ℂ | v ∉ Ψ '' A ∧ ‖v‖ < ‖x‖ + 1} ∈ 𝓝 x := by
      exact Filter.inter_mem (hImg.isClosed.isOpen_compl.mem_nhds hxImg)
        (continuous_norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by linarith)))
    obtain ⟨δ, hδ, hδn⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    have hyn := hδn hy
    rw [inverseNormEnvelope_eq_one hx]
    have hu : 1 ≤ inverseNormEnvelope K Φ y := one_le_inverseNormEnvelope hΦmap y
    have huε : inverseNormEnvelope K Φ y < 1 + ε := by
      by_cases hyK : y ∈ K
      · simp only [inverseNormEnvelope_eq_one hyK]
        linarith
      · rw [inverseNormEnvelope_eq_norm hyK]
        by_contra hbad
        have hlower : 1 + ε ≤ ‖Φ y‖ := le_of_not_gt hbad
        have hupper : ‖Φ y‖ < R := by
          by_contra hupp
          have hh := hR (Φ y) (le_of_not_gt hupp)
          rw [hright y hyK] at hh
          exact (not_le_of_gt hyn.2) hh
        exact hyn.1 ⟨Φ y, ⟨mem_closedBall_zero_iff.mpr hupper.le, hlower⟩, hright y hyK⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu)]
    linarith
  · have hΦx := (hΦ.continuousAt (hK.isOpen_compl.mem_nhds hx)).norm
    apply hΦx.congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact inverseNormEnvelope_eq_norm hy

#print axioms continuous_inverseNormEnvelope

/-- Near the unit circle, the image of the exterior map lies uniformly close
to the omitted set. The proof uses compact bad sets and the inverse map;
there is no assertion of pointwise boundary values of `Ψ`. -/
theorem exists_collar_infDist_lt {K : Set ℂ} {Ψ Φ : ℂ → ℂ}
    (hΦ : ContinuousOn Φ Kᶜ)
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hΦinfty : Tendsto (fun v => ‖Φ v‖) (cocompact ℂ) atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < 1 + δ →
      infDist (Ψ w) K < ε := by
  obtain ⟨R, hR⟩ := bounds_of_norm_tendsto_infty hΦinfty 2
  let A : Set ℂ := closedBall 0 R ∩ {v : ℂ | ε ≤ infDist v K}
  have hAc : IsCompact A := (isCompact_closedBall 0 R).inter_right
    (isClosed_le continuous_const (continuous_infDist_pt K))
  have hAout : A ⊆ Kᶜ := by
    intro v hv hvK
    have hh : ε ≤ infDist v K := hv.2
    rw [infDist_zero_of_mem hvK] at hh
    exact (not_le_of_gt hε) hh
  have hnorm {w : ℂ} (hw : w ∈ exteriorDisk) (hw2 : ‖w‖ < 2) : ‖Ψ w‖ < R := by
    by_contra hbad
    have hh := hR (Ψ w) (le_of_not_gt hbad)
    rw [hleft w hw] at hh
    exact (not_le_of_gt hw2) hh
  by_cases hne : A.Nonempty
  · obtain ⟨v, hv, hmin⟩ := hAc.exists_isMinOn hne (hΦ.mono hAout).norm
    have hgap : 0 < ‖Φ v‖ - 1 := sub_pos.mpr (hΦmap (hAout hv))
    refine ⟨min 1 (‖Φ v‖ - 1), lt_min zero_lt_one hgap, ?_⟩
    intro w hw hwr
    have hw2 : ‖w‖ < 2 := by
      have hh := min_le_left (1 : ℝ) (‖Φ v‖ - 1)
      linarith
    by_contra hbad
    have hwA : Ψ w ∈ A := ⟨mem_closedBall_zero_iff.mpr (hnorm hw hw2).le,
      le_of_not_gt hbad⟩
    have hh := hmin hwA
    change ‖Φ v‖ ≤ ‖Φ (Ψ w)‖ at hh
    rw [hleft w hw] at hh
    have hd := min_le_right (1 : ℝ) (‖Φ v‖ - 1)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro w hw hwr
    by_contra hbad
    apply hne
    exact ⟨Ψ w, mem_closedBall_zero_iff.mpr (hnorm hw (by linarith)).le,
      le_of_not_gt hbad⟩

#print axioms exists_collar_infDist_lt

end
end ExteriorReduction.ExteriorEnvelope
