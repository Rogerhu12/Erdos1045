import ExteriorEnvelopeRotation

/-! Asymptotics of the scalar envelope of two unit rotations. Only nonopposite
rotations are needed for the local variation at parameter zero. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

theorem tendsto_unit_mul_cocompact {u : ℂ} (hu : ‖u‖ = 1) :
    Tendsto (fun w : ℂ => u * w) (cocompact ℂ) (cocompact ℂ) := by
  have hn : Tendsto (fun w : ℂ => ‖u * w‖) (cocompact ℂ) atTop := by
    simpa only [norm_mul, hu, one_mul] using (tendsto_norm_cocompact_atTop (E := ℂ))
  simpa only [cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hn

theorem unit_mul_ratio_tendsto {Ψ : ℂ → ℂ} {c u : ℂ}
    (hΨ : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c)) (hu : ‖u‖ = 1) :
    Tendsto (fun w => Ψ (u * w) / w) (cocompact ℂ) (𝓝 (c * u)) := by
  have hune : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; norm_num)
  have h := (hΨ.comp (tendsto_unit_mul_cocompact hu)).mul_const u
  have he : (fun w : ℂ => Ψ (u * w) / (u * w) * u) =ᶠ[cocompact ℂ]
      (fun w => Ψ (u * w) / w) := by
    filter_upwards [eventually_ne_zero_cocompact] with w hw
    field_simp
  exact h.congr' he

theorem rotatedAverage_ratio_tendsto {Ψ : ℂ → ℂ} {c u v : ℂ}
    (hΨ : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    Tendsto (fun w => rotatedAverage Ψ u v w / w) (cocompact ℂ)
      (𝓝 (c * ((u + v) / 2))) := by
  have h := ((unit_mul_ratio_tendsto hΨ hu).add
    (unit_mul_ratio_tendsto hΨ hv)).div_const 2
  have heq : (c * u + c * v) / 2 = c * ((u + v) / 2) := by ring
  rw [heq] at h
  convert h using 1
  funext w
  simp only [rotatedAverage]
  ring

theorem norm_tendsto_infty_of_ratio {V : ℂ → ℂ} {a : ℂ}
    (hV : Tendsto (fun w => V w / w) (cocompact ℂ) (𝓝 a)) (ha : a ≠ 0) :
    Tendsto (fun w => ‖V w‖) (cocompact ℂ) atTop := by
  apply (tendsto_norm_cocompact_atTop (E := ℂ)).num (norm_pos_iff.mpr ha)
  simpa only [norm_div] using hV.norm

theorem planeEnvelope_tendsto_infty {K : Set ℂ} {Ψ Φ : ℂ → ℂ} {c u v : ℂ}
    (hK : IsCompact K) (hc : c ≠ 0)
    (hΨ : Tendsto (fun w => Ψ w / w) (cocompact ℂ) (𝓝 c))
    (hΦ : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 c⁻¹))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : u + v ≠ 0) :
    Tendsto (planeEnvelope (inverseNormEnvelope K Φ) (rotatedAverage Ψ u v))
      (cocompact ℂ) (𝓝 ‖(u + v) / 2‖) := by
  let V := rotatedAverage Ψ u v
  have hα : (u + v) / (2 : ℂ) ≠ 0 := div_ne_zero huv (by norm_num)
  have hVratio := rotatedAverage_ratio_tendsto hΨ hu hv
  have hVnorm := norm_tendsto_infty_of_ratio hVratio (mul_ne_zero hc hα)
  have hVproper : Tendsto V (cocompact ℂ) (cocompact ℂ) := by
    simpa only [cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hVnorm
  have hFinfty := (hΦ.comp hVproper).mul hVratio
  have hconst : c⁻¹ * (c * ((u + v) / 2)) = (u + v) / 2 := by
    field_simp
  rw [hconst] at hFinfty
  have hF : Tendsto (fun w => Φ (V w) / w) (cocompact ℂ) (𝓝 ((u + v) / 2)) := by
    apply hFinfty.congr'
    filter_upwards [hVproper.eventually eventually_ne_zero_cocompact] with w hw
    change Φ (V w) / V w * (V w / w) = Φ (V w) / w
    field_simp
  have he : (fun w => ‖Φ (V w) / w‖) =ᶠ[cocompact ℂ]
      planeEnvelope (inverseNormEnvelope K Φ) V := by
    filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop 1,
      hVproper.eventually hK.compl_mem_cocompact] with w hw hVw
    rw [planeEnvelope_eq_outside hw, inverseNormEnvelope_eq_norm hVw, norm_div]
  exact hF.norm.congr' he

theorem unit_average_norm_le_one {u v : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖(u + v) / 2‖ ≤ 1 := by
  have hh := norm_add_le u v
  rw [hu, hv] at hh
  rw [norm_div]
  norm_num
  linarith

#print axioms planeEnvelope_tendsto_infty

end
end ExteriorReduction.ExteriorEnvelope
