import ExteriorEnvelopeInfinity

/-! The exterior convexity criterion from actual convex omitted geometry,
holomorphic inverse maps, and their ordinary normalization at infinity. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

theorem rotatedAverage_envelope_le {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {c u v : ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk) (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hright : ∀ y ∈ Kᶜ, Ψ (Φ y) = y)
    (hc : c ≠ 0)
    (hΨratio : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hΦratio : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 c⁻¹))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u + v ≠ 0)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    inverseNormEnvelope K Φ (rotatedAverage Ψ u v w) ≤ ‖w‖ := by
  have hΨinfty := norm_tendsto_infty_of_ratio hΨratio hc
  have hΦinfty := norm_tendsto_infty_of_ratio hΦratio (inv_ne_zero hc)
  have hU := continuous_inverseNormEnvelope hK.isClosed hΨ.continuousOn hΦ.continuousOn
    hΨmap hΦmap hright hΨinfty
  have hqc := continuous_planeEnvelope hU (rotatedAverage_continuousOn hΨ.continuousOn hu hv)
    (fun ε hε => rotatedAverage_envelope_collar hK hne hconv hU hΦ.continuousOn
      hΦmap hleft hΦinfty hu hv hε)
  have hqbound := ExteriorConvexCriterion.scalar_envelope_maximum hqc
    (fun z hz => planeEnvelope_local_norm hK.isClosed hΨ hΦ hu hv hz)
    (fun R hR => (planeEnvelope_tendsto_infty hK hc hΨratio hΦratio hu hv huv).eventually
      (Iio_mem_nhds ((unit_average_norm_le_one hu hv).trans_lt hR))) w
  rw [planeEnvelope_eq_outside hw] at hqbound
  exact (div_le_one (zero_lt_one.trans hw)).mp hqbound

/-- Convexity of the omitted compact set implies the exterior analytic
criterion. The proof does not use reflection, a boundary homeomorphism,
Schwarz--Christoffel, or convergence of Riemann maps on varying domains. -/
theorem exterior_convex_criterion_nonneg {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {c : ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk) (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hright : ∀ y ∈ Kᶜ, Ψ (Φ y) = y)
    (hc : c ≠ 0)
    (hΨratio : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hΦratio : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 c⁻¹))
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    0 ≤ (1 + w * deriv (deriv Ψ) w / deriv Ψ w).re := by
  have hlocleft : Φ ∘ Ψ =ᶠ[𝓝 w] id := by
    filter_upwards [exteriorDisk_isOpen.mem_nhds hw] with z hz
    exact hleft z hz
  have hΨw := hΨ w hw
  have hΦw := hΦ (Ψ w) (hΨmap hw)
  apply ExteriorConvexCriterion.logDeriv_nonneg_of_local_rotation_bound
    (norm_pos_iff.mp (zero_lt_one.trans hw)) hΨw hΦw hlocleft
  have hmean := InteriorConvexCriterion.rotationMean_analyticAt_zero hΨw
  have hmean0 : InteriorConvexCriterion.rotationMean Ψ w 0 = Ψ w :=
    InteriorConvexCriterion.rotationMean_zero Ψ w
  have hmean_real : ContinuousAt
      (fun t : ℝ => InteriorConvexCriterion.rotationMean Ψ w (t : ℂ)) 0 :=
    ContinuousAt.comp (f := fun t : ℝ => (t : ℂ))
      (g := InteriorConvexCriterion.rotationMean Ψ w) hmean.continuousAt
      Complex.continuous_ofReal.continuousAt
  have hout : ∀ᶠ t : ℝ in 𝓝 0,
      InteriorConvexCriterion.rotationMean Ψ w (t : ℂ) ∉ K := by
    change (fun t : ℝ => InteriorConvexCriterion.rotationMean Ψ w (t : ℂ)) ⁻¹' Kᶜ ∈ 𝓝 0
    apply hmean_real.preimage_mem_nhds
    simpa only [Complex.ofReal_zero, hmean0] using
      hK.isClosed.isOpen_compl.mem_nhds (hΨmap hw)
  have hsum : ContinuousAt (fun t : ℝ =>
      Complex.exp (I * (t : ℂ)) + Complex.exp (-I * (t : ℂ))) 0 := by fun_prop
  have hsumne : ∀ᶠ t : ℝ in 𝓝 0,
      Complex.exp (I * (t : ℂ)) + Complex.exp (-I * (t : ℂ)) ≠ 0 :=
    hsum.eventually_ne (by norm_num)
  filter_upwards [hout, hsumne] with t ht htsum
  have h := rotatedAverage_envelope_le hK hne hconv hΨ hΦ hΨmap hΦmap hleft hright
    hc hΨratio hΦratio
    (show ‖Complex.exp (I * (t : ℂ))‖ = 1 by simp [Complex.norm_exp, Complex.mul_re])
    (show ‖Complex.exp (-I * (t : ℂ))‖ = 1 by simp [Complex.norm_exp, Complex.mul_re])
    htsum hw
  change inverseNormEnvelope K Φ (InteriorConvexCriterion.rotationMean Ψ w (t : ℂ)) ≤ ‖w‖ at h
  rwa [inverseNormEnvelope_eq_norm ht] at h

#print axioms exterior_convex_criterion_nonneg

end
end ExteriorReduction.ExteriorEnvelope
