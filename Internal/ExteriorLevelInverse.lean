import ExteriorLevelCauchy
import ExteriorInfinity

namespace ExteriorReduction
open Complex Metric Set Filter
open scoped Topology
noncomputable section

/-- An arbitrary exterior biholomorphism has the continuous inverse-modulus
envelope, with the inverse chosen canonically on its image. -/
theorem continuous_inverseNormEnvelope_invFunOn {K : Set ℂ} {Ψ : ℂ → ℂ}
    (hK : IsClosed K) (hΨ : DifferentiableOn ℂ Ψ exteriorDisk)
    (hbij : BijOn Ψ exteriorDisk Kᶜ)
    (hproper : Tendsto (fun w => ‖Ψ w‖) (cocompact ℂ) atTop) :
    Continuous (ExteriorEnvelope.inverseNormEnvelope K (Function.invFunOn Ψ exteriorDisk)) := by
  have hinv := hbij.invOn_invFunOn
  have hmap := hbij.surjOn.mapsTo_invFunOn
  have hΦ := RiemannBiholomorphic.differentiableOn_inverse exteriorDisk_isOpen
    hK.isOpen_compl hΨ hbij hmap hinv
  exact ExteriorEnvelope.continuous_inverseNormEnvelope hK hΨ.continuousOn hΦ.continuousOn
    hbij.mapsTo hmap (fun _ hv => hinv.2 hv) hproper

/-- The model at infinity gives properness for every exterior map agreeing
with that model on the open exterior, independently of boundary values. -/
theorem norm_atTop_of_exterior_model {q Ψ : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) (A : ℂ)
    (hmatch : ∀ w ∈ exteriorDisk, Ψ w = A + w * q w⁻¹) :
    Tendsto (fun w => ‖Ψ w‖) (cocompact ℂ) atTop := by
  have hh := exteriorFromModel_norm_atTop
    ((hq 0 (by simp)).continuousAt) hq0 A
  apply hh.congr'
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℂ)).eventually_gt_atTop 1] with w hw
  simpa only [exteriorFromModel] using congrArg norm (hmatch w hw).symm

/-- The actual Cauchy--Bernstein--Walsh estimate for an exterior bijection.
Inverse holomorphy and continuity of the filled inverse modulus are derived. -/
theorem cauchy_bernstein_walsh_of_bijective (p : Polynomial ℂ) (A : ℂ)
    {K : Set ℂ} {q Ψ : ℂ → ℂ} (hK : K.Nonempty) (hKclosed : IsClosed K)
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    (hΨ : ContinuousOn Ψ {w : ℂ | 1 ≤ ‖w‖})
    (hΨdiff : DifferentiableOn ℂ Ψ exteriorDisk) (hbij : BijOn Ψ exteriorDisk Kᶜ)
    (hmatch : ∀ w ∈ exteriorDisk, Ψ w = A + w * q w⁻¹)
    (hboundaryMap : ∀ w : ℂ, ‖w‖ = 1 → Ψ w ∈ K)
    (hboundarySurj : ∀ v ∈ frontier K, ∃ u : ℂ, ‖u‖ = 1 ∧ Ψ u = v)
    {r h : ℝ} (hr : 1 < r) (hh : 0 < h)
    (hsep : ∀ u v : ℂ, ‖u‖ = r → ‖v‖ = 1 → h ≤ ‖Ψ u - Ψ v‖)
    (hp : ∀ x ∈ K, ‖p.eval x‖ ≤ 1) :
    ∀ x ∈ K, ‖p.derivative.eval x‖ ≤ 2 * r ^ p.natDegree / h := by
  have hproper := norm_atTop_of_exterior_model hq hq0 A hmatch
  have hU := continuous_inverseNormEnvelope_invFunOn hKclosed hΨdiff hbij hproper
  exact cauchy_bernstein_walsh_actual p A hK hq hΨ hmatch hboundaryMap hboundarySurj
    hbij.surjOn.mapsTo_invFunOn (fun _ hv => hbij.invOn_invFunOn.2 hv) hU hr hh hsep hp

#print axioms cauchy_bernstein_walsh_of_bijective
end
end ExteriorReduction
