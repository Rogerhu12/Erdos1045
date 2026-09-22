import PositiveExteriorModel
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.Bornology.BoundedOperation

/-! Genuine normalizations and properness at infinity for the constructed
exterior map and inverse. Only differentiability at the inverted origin is
needed for the inverse map. -/

namespace ExteriorReduction

open Complex Set Metric Filter Bornology
open scoped Topology
noncomputable section

theorem tendsto_inv_cocompact_zero :
    Tendsto (fun w : ℂ => w⁻¹) (cocompact ℂ) (𝓝 0) := by
  simpa only [cobounded_eq_cocompact] using (tendsto_inv₀_cobounded (α := ℂ))

theorem eventually_ne_zero_cocompact : ∀ᶠ w : ℂ in cocompact ℂ, w ≠ 0 := by
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop 0] with w hw
  exact norm_pos_iff.mp hw

theorem tendsto_sub_const_cocompact (A : ℂ) :
    Tendsto (fun w : ℂ => w - A) (cocompact ℂ) (cocompact ℂ) := by
  simpa only [cobounded_eq_cocompact] using tendsto_sub_const_cobounded A

theorem exteriorFromModel_ratio_tendsto {q : ℂ → ℂ}
    (hq : ContinuousAt q 0) (A : ℂ) :
    Tendsto (fun w => exteriorFromModel q A w / w) (cocompact ℂ) (𝓝 (q 0)) := by
  have hh := ((tendsto_const_nhds (x := A)).mul tendsto_inv_cocompact_zero).add
    (hq.tendsto.comp tendsto_inv_cocompact_zero)
  have he : (fun w : ℂ => A * w⁻¹ + q w⁻¹) =ᶠ[cocompact ℂ]
      (fun w => exteriorFromModel q A w / w) := by
    filter_upwards [eventually_ne_zero_cocompact] with w hw
    simp only [exteriorFromModel]
    field_simp
  simpa only [mul_zero, zero_add] using hh.congr' he

theorem exteriorFromModel_norm_atTop {q : ℂ → ℂ}
    (hq : ContinuousAt q 0) (hq0 : q 0 ≠ 0) (A : ℂ) :
    Tendsto (fun w => ‖exteriorFromModel q A w‖) (cocompact ℂ) atTop := by
  apply (tendsto_norm_cocompact_atTop (E := ℂ)).num (norm_pos_iff.mpr hq0)
  simpa only [norm_div] using (exteriorFromModel_ratio_tendsto hq A).norm

theorem laurentModel_continuousAt_zero {f : ℂ → ℂ}
    (hf : DifferentiableAt ℂ f 0) (hdf : deriv f 0 ≠ 0) :
    ContinuousAt (laurentModel f) 0 := by
  exact (continuousAt_dslope_same.mpr hf).inv₀ (by simpa using hdf)

theorem exteriorInverse_shifted_ratio {f : ℂ → ℂ} (hf0 : f 0 = 0) (A : ℂ)
    {p : ℂ} (hp : p - A ≠ 0) :
    exteriorInverseFromDisk f A p / (p - A) = laurentModel f (p - A)⁻¹ := by
  rw [laurentModel_eq_div hf0 (inv_ne_zero hp)]
  simp only [exteriorInverseFromDisk, div_eq_mul_inv]
  ring

theorem exteriorInverse_shifted_ratio_tendsto {f : ℂ → ℂ}
    (hf : DifferentiableAt ℂ f 0) (hf0 : f 0 = 0) (hdf : deriv f 0 ≠ 0) (A : ℂ) :
    Tendsto (fun p => exteriorInverseFromDisk f A p / (p - A))
      (cocompact ℂ) (𝓝 ((deriv f 0)⁻¹)) := by
  have ht := tendsto_inv_cocompact_zero.comp (tendsto_sub_const_cocompact A)
  have hl := (laurentModel_continuousAt_zero hf hdf).tendsto.comp ht
  have he : (fun p => laurentModel f (p - A)⁻¹) =ᶠ[cocompact ℂ]
      (fun p => exteriorInverseFromDisk f A p / (p - A)) := by
    filter_upwards [(tendsto_sub_const_cocompact A).eventually eventually_ne_zero_cocompact]
      with p hp
    exact (exteriorInverse_shifted_ratio hf0 A hp).symm
  simpa only [laurentModel_zero] using hl.congr' he

theorem exteriorInverse_norm_atTop {f : ℂ → ℂ}
    (hf : DifferentiableAt ℂ f 0) (hf0 : f 0 = 0) (hdf : deriv f 0 ≠ 0) (A : ℂ) :
    Tendsto (fun p => ‖exteriorInverseFromDisk f A p‖) (cocompact ℂ) atTop := by
  have hn := (tendsto_norm_cocompact_atTop (E := ℂ)).comp
    (tendsto_sub_const_cocompact A)
  apply hn.num (norm_pos_iff.mpr (inv_ne_zero hdf))
  simpa only [norm_div, Function.comp_def] using
    (exteriorInverse_shifted_ratio_tendsto hf hf0 hdf A).norm

theorem exteriorInverse_ratio_tendsto {f : ℂ → ℂ}
    (hf : DifferentiableAt ℂ f 0) (hf0 : f 0 = 0) (hdf : deriv f 0 ≠ 0) (A : ℂ) :
    Tendsto (fun p => exteriorInverseFromDisk f A p / p)
      (cocompact ℂ) (𝓝 ((deriv f 0)⁻¹)) := by
  have hs : Tendsto (fun p : ℂ => (p - A) / p) (cocompact ℂ) (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℂ))).sub
      ((tendsto_const_nhds (x := A)).mul tendsto_inv_cocompact_zero)
    have he : (fun p : ℂ => 1 - A * p⁻¹) =ᶠ[cocompact ℂ] (fun p => (p - A) / p) := by
      filter_upwards [eventually_ne_zero_cocompact] with p hp
      field_simp
    simpa only [mul_zero, sub_zero] using hh.congr' he
  have hh := (exteriorInverse_shifted_ratio_tendsto hf hf0 hdf A).mul hs
  have he : (fun p => exteriorInverseFromDisk f A p / (p - A) * ((p - A) / p))
      =ᶠ[cocompact ℂ] (fun p => exteriorInverseFromDisk f A p / p) := by
    filter_upwards [(tendsto_sub_const_cocompact A).eventually eventually_ne_zero_cocompact]
      with p hp
    field_simp
  simpa only [mul_one] using hh.congr' he

#print axioms exteriorFromModel_norm_atTop
#print axioms exteriorInverse_norm_atTop
#print axioms exteriorInverse_ratio_tendsto

end
end ExteriorReduction
