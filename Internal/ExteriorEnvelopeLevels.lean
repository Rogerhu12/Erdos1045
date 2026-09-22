import ExteriorEnvelopeWeighted

/-! Convexity of the actual compact sublevel sets of the exterior inverse
modulus. Boundary interpolation is extended to the whole set by two scalar
maximum principles; no Jordan theorem or curvature theorem is used. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

def levelSet (K : Set ℂ) (Φ : ℂ → ℂ) (r : ℝ) : Set ℂ :=
  {z | inverseNormEnvelope K Φ z ≤ r}

theorem levelSet_isCompact {K : Set ℂ} {Φ : ℂ → ℂ}
    (hK : IsCompact K) (hU : Continuous (inverseNormEnvelope K Φ))
    (hΦinfty : Tendsto (fun z => ‖Φ z‖) (cocompact ℂ) atTop) (r : ℝ) :
    IsCompact (levelSet K Φ r) := by
  have hs : IsClosed (levelSet K Φ r) := isClosed_le hU continuous_const
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  obtain ⟨R, hR⟩ := bounds_of_norm_tendsto_infty hΦinfty (r + 1)
  apply (isCompact_closedBall (0 : ℂ) (max M R)).of_isClosed_subset hs
  intro z hz
  apply mem_closedBall_zero_iff.mpr
  by_cases hzK : z ∈ K
  · exact (hM z hzK).trans (le_max_left _ _)
  · have hzU : ‖Φ z‖ ≤ r := by
      simpa only [levelSet, mem_ofPred_eq, inverseNormEnvelope_eq_norm hzK] using hz
    have hzR : ‖z‖ < R := by
      by_contra hbad
      have hh := hR z (le_of_not_gt hbad)
      linarith
    exact hzR.le.trans (le_max_right _ _)

theorem frontier_levelSet_value {K : Set ℂ} {Φ : ℂ → ℂ}
    (hU : Continuous (inverseNormEnvelope K Φ)) {r : ℝ} {z : ℂ}
    (hz : z ∈ frontier (levelSet K Φ r)) : inverseNormEnvelope K Φ z = r :=
  frontier_le_subset_eq hU continuous_const hz

theorem envelope_affine_local_norm {K : Set ℂ} {Φ F : ℂ → ℂ} {C : ℝ}
    (hK : IsClosed K) (hΦ : AnalyticOnNhd ℂ Φ Kᶜ) (hF : AnalyticOnNhd ℂ F univ)
    (hC : 1 ≤ C) {z : ℂ} (hz : C < inverseNormEnvelope K Φ (F z)) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ ∀ᶠ w in 𝓝 z,
      inverseNormEnvelope K Φ (F w) = ‖G w‖ := by
  have hzF : F z ∉ K := by
    intro hbad
    rw [inverseNormEnvelope_eq_one hbad] at hz
    exact (not_lt_of_ge hC) hz
  refine ⟨Φ ∘ F, (hΦ _ hzF).comp (hF z (mem_univ z)), ?_⟩
  have he : ∀ᶠ w in 𝓝 z, F w ∉ K :=
    (hF z (mem_univ z)).continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hzF)
  filter_upwards [he] with w hw
  exact inverseNormEnvelope_eq_norm hw

theorem level_boundary_convex_combination {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {c : ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk) (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hright : ∀ y ∈ Kᶜ, Ψ (Φ y) = y)
    (hc : c ≠ 0)
    (hΨratio : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hΦratio : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 c⁻¹))
    (hU : Continuous (inverseNormEnvelope K Φ))
    {r : ℝ} (hr : 1 < r) {x y : ℂ}
    (hx : x ∈ frontier (levelSet K Φ r)) (hy : y ∈ frontier (levelSet K Φ r))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    inverseNormEnvelope K Φ (a • x + b • y) ≤ r := by
  have hxU := frontier_levelSet_value hU hx
  have hyU := frontier_levelSet_value hU hy
  have hxK : x ∉ K := by intro h; rw [inverseNormEnvelope_eq_one h] at hxU; linarith
  have hyK : y ∉ K := by intro h; rw [inverseNormEnvelope_eq_one h] at hyU; linarith
  rw [inverseNormEnvelope_eq_norm hxK] at hxU
  rw [inverseNormEnvelope_eq_norm hyK] at hyU
  have hrpos : 0 < r := zero_lt_one.trans hr
  have hrne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hux : ‖Φ x / (r : ℂ)‖ = 1 := by
    rw [norm_div, hxU, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_self hrpos.ne']
  have huy : ‖Φ y / (r : ℂ)‖ = 1 := by
    rw [norm_div, hyU, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, div_self hrpos.ne']
  have hrr : (r : ℂ) ∈ exteriorDisk := by simpa [exteriorDisk, abs_of_pos hrpos] using hr
  have hh := weightedAverage_envelope_le hK hne hconv hΨ hΦ hΨmap hΦmap hleft hright hc
    hΨratio hΦratio hux huy ha hb hab hrr
  simpa only [weightedAverage, div_mul_cancel₀ _ hrne, hright x hxK, hright y hyK,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos, Complex.real_smul] using hh

theorem convex_levelSet {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {c : ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk) (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hright : ∀ y ∈ Kᶜ, Ψ (Φ y) = y)
    (hc : c ≠ 0)
    (hΨratio : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hΦratio : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 c⁻¹))
    {r : ℝ} (hr : 1 < r) : Convex ℝ (levelSet K Φ r) := by
  have hU := continuous_inverseNormEnvelope hK.isClosed hΨ.continuousOn hΦ.continuousOn
    hΨmap hΦmap hright (norm_tendsto_infty_of_ratio hΨratio hc)
  have hS := levelSet_isCompact hK hU (norm_tendsto_infty_of_ratio hΦratio (inv_ne_zero hc)) r
  intro x hx y hy a b ha hb hab
  have hboundary (p q : ℂ) (hp : p ∈ frontier (levelSet K Φ r))
      (hq : q ∈ frontier (levelSet K Φ r)) :
      inverseNormEnvelope K Φ (a • p + b • q) ≤ r :=
    level_boundary_convex_combination hK hne hconv hΨ hΦ hΨmap hΦmap hleft hright
      hc hΨratio hΦratio hU hr hp hq ha hb hab
  have hfirst (p : ℂ) (hp : p ∈ frontier (levelSet K Φ r)) :
      ∀ q ∈ levelSet K Φ r, inverseNormEnvelope K Φ (a • p + b • q) ≤ r := by
    have hF : AnalyticOnNhd ℂ (fun q : ℂ => a • p + b • q) univ := by
      intro q _
      simp only [Complex.real_smul]
      fun_prop
    exact scalar_envelope_maximum_on_compact hS (hU.comp (continuousOn_univ.mp hF.continuousOn))
      (fun q hq => hboundary p q hp hq)
      (fun q hq => envelope_affine_local_norm hK.isClosed hΦ hF hr.le hq)
  have hF : AnalyticOnNhd ℂ (fun p : ℂ => a • p + b • y) univ := by
    intro p _
    simp only [Complex.real_smul]
    fun_prop
  exact scalar_envelope_maximum_on_compact hS (hU.comp (continuousOn_univ.mp hF.continuousOn))
    (fun p hp => hfirst p hp y hy)
    (fun p hp => envelope_affine_local_norm hK.isClosed hΦ hF hr.le hp) x hx

#print axioms convex_levelSet

end
end ExteriorReduction.ExteriorEnvelope
