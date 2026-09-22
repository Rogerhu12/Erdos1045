import ExteriorEnvelopeGeneral

/-! Convex combinations of two points on any exterior level circle. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

def weightedAverage (Ψ : ℂ → ℂ) (a b : ℝ) (u v w : ℂ) : ℂ :=
  (a : ℂ) * Ψ (u * w) + (b : ℂ) * Ψ (v * w)

theorem weightedAverage_analytic {Ψ : ℂ → ℂ} {u v : ℂ}
    (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (a b : ℝ) : AnalyticOnNhd ℂ (weightedAverage Ψ a b u v) exteriorDisk := by
  intro w hw
  exact (analyticAt_const.mul ((hΨ _ (unit_mul_mem_exterior hu hw)).comp
    (analyticAt_const.mul analyticAt_id))).add
    (analyticAt_const.mul ((hΨ _ (unit_mul_mem_exterior hv hw)).comp
      (analyticAt_const.mul analyticAt_id)))

theorem weightedAverage_collar {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {u v : ℂ} {a b : ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hU : Continuous (inverseNormEnvelope K Φ))
    (hΦ : ContinuousOn Φ Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hΦinfty : Tendsto (fun y => ‖Φ y‖) (cocompact ℂ) atTop)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, 1 < ‖w‖ → ‖w‖ < 1 + δ →
      |inverseNormEnvelope K Φ (weightedAverage Ψ a b u v w) - 1| < ε := by
  have hsub : K ⊆ {x : ℂ | |inverseNormEnvelope K Φ x - 1| < ε} := by
    intro x hx
    simpa [inverseNormEnvelope_eq_one hx] using hε
  obtain ⟨η, hη, hηsub⟩ := hK.exists_thickening_subset_open
    (isOpen_lt ((hU.sub continuous_const).abs) continuous_const) hsub
  obtain ⟨δ, hδ, hcollar⟩ := exists_collar_infDist_lt hΦ hΦmap hleft hΦinfty hη
  refine ⟨δ, hδ, ?_⟩
  intro w hw hwr
  have hPu : Ψ (u * w) ∈ thickening η K := (mem_thickening_iff_infDist_lt hne).mpr
    (hcollar (u * w) (by simpa only [norm_mul, hu, one_mul] using hw)
      (by simpa only [norm_mul, hu, one_mul] using hwr))
  have hPv : Ψ (v * w) ∈ thickening η K := (mem_thickening_iff_infDist_lt hne).mpr
    (hcollar (v * w) (by simpa only [norm_mul, hv, one_mul] using hw)
      (by simpa only [norm_mul, hv, one_mul] using hwr))
  apply hηsub
  simpa only [weightedAverage, Complex.real_smul] using (hconv.thickening η) hPu hPv ha hb hab

theorem weightedAverage_ratio_tendsto {Ψ : ℂ → ℂ} {c u v : ℂ}
    (hΨ : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (a b : ℝ) :
    Tendsto (fun w => weightedAverage Ψ a b u v w / w) (cocompact ℂ)
      (𝓝 (c * ((a : ℂ) * u + (b : ℂ) * v))) := by
  have h := ((unit_mul_ratio_tendsto hΨ hu).const_mul (a : ℂ)).add
    ((unit_mul_ratio_tendsto hΨ hv).const_mul (b : ℂ))
  have heq : (a : ℂ) * (c * u) + (b : ℂ) * (c * v) =
      c * ((a : ℂ) * u + (b : ℂ) * v) := by ring
  rw [heq] at h
  convert h using 1
  funext w
  simp only [weightedAverage]
  ring

theorem weighted_unit_norm_le_one {u v : ℂ} {a b : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖(a : ℂ) * u + (b : ℂ) * v‖ ≤ 1 := by
  have hh := norm_add_le ((a : ℂ) * u) ((b : ℂ) * v)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    abs_of_nonneg hb, hu, hv, mul_one, hab] using hh

theorem weightedAverage_envelope_le {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {c u v : ℂ} {a b : ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hΨ : AnalyticOnNhd ℂ Ψ exteriorDisk) (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    (hΨmap : MapsTo Ψ exteriorDisk Kᶜ) (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (Ψ w) = w)
    (hright : ∀ y ∈ Kᶜ, Ψ (Φ y) = y)
    (hc : c ≠ 0)
    (hΨratio : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hΦratio : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 c⁻¹))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    inverseNormEnvelope K Φ (weightedAverage Ψ a b u v w) ≤ ‖w‖ := by
  have hΨinfty := norm_tendsto_infty_of_ratio hΨratio hc
  have hΦinfty := norm_tendsto_infty_of_ratio hΦratio (inv_ne_zero hc)
  have hU := continuous_inverseNormEnvelope hK.isClosed hΨ.continuousOn hΦ.continuousOn
    hΨmap hΦmap hright hΨinfty
  apply general_analytic_envelope_le hK hU hΦ hΦmap
    (weightedAverage_analytic hΨ hu hv a b)
    (fun ε hε => weightedAverage_collar hK hne hconv hU hΦ.continuousOn hΦmap hleft
      hΦinfty hu hv ha hb hab hε) hΦratio (weightedAverage_ratio_tendsto hΨratio hu hv a b) ?_ hw
  have he : c⁻¹ * (c * ((a : ℂ) * u + (b : ℂ) * v)) = (a : ℂ) * u + (b : ℂ) * v := by
    field_simp
  rw [he]
  exact weighted_unit_norm_le_one hu hv ha hb hab

#print axioms weightedAverage_envelope_le

end
end ExteriorReduction.ExteriorEnvelope
