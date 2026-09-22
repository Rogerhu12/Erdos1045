import ExteriorCriterionComplete
import NormalizedDerivative

/-! The geometric criterion applies to the derivative of the actual analytic
model at infinity. This file connects that criterion to the previously proved
normalized derivative estimates. -/

namespace ExteriorReduction.ExteriorEnvelope

open Complex Metric Set Filter Bornology
open scoped Topology

noncomputable section

theorem modelDerivative_criterion_eq {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    (A : ℂ) {w : ℂ} (hw : w ∈ exteriorDisk) :
    derivativeCriterion (modelDerivative q) w⁻¹ =
      1 + w * deriv (deriv (exteriorFromModel q A)) w / deriv (exteriorFromModel q A) w := by
  have hwne : w ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hw)
  have hD := modelDerivative_analytic hq hq0
  have he : deriv (exteriorFromModel q A) =ᶠ[𝓝 w]
      (fun v => q 0 * modelDerivative q v⁻¹) := by
    filter_upwards [exteriorDisk_isOpen.mem_nhds hw] with v hv
    exact exteriorFromModel_normalized_deriv hq hq0 A hv
  have hd := (((hD _ (inv_mem_disk_of_exterior hw)).differentiableAt.hasDerivAt).comp w
    (hasDerivAt_inv hwne)).const_mul (q 0)
  simp only [Function.comp_apply] at hd
  rw [he.deriv_eq, hd.deriv, exteriorFromModel_normalized_deriv hq hq0 A hw]
  unfold derivativeCriterion
  by_cases hDz : modelDerivative q w⁻¹ = 0
  · simp [hDz]
  · field_simp
    ring

/-- Nonnegativity for the model derivative follows from the actual convex
omitted set and exterior inverse maps, not from an additional criterion axiom. -/
theorem modelDerivative_criterion_nonneg {K : Set ℂ} {q Φ : ℂ → ℂ} {A : ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    (hΨ : AnalyticOnNhd ℂ (exteriorFromModel q A) exteriorDisk)
    (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    (hΨmap : MapsTo (exteriorFromModel q A) exteriorDisk Kᶜ)
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (exteriorFromModel q A w) = w)
    (hright : ∀ y ∈ Kᶜ, exteriorFromModel q A (Φ y) = y)
    (hΦratio : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 (q 0)⁻¹)) :
    ∀ z ∈ ball (0 : ℂ) 1, 0 ≤ (derivativeCriterion (modelDerivative q) z).re := by
  intro z hz
  by_cases hz0 : z = 0
  · simp [hz0, derivativeCriterion]
  have hw := inv_mem_exterior_of_disk hz hz0
  have hc := exterior_convex_criterion_nonneg hK hne hconv hΨ hΦ hΨmap hΦmap hleft hright
    hq0 (exteriorFromModel_ratio_tendsto (hq 0 (by simp)).continuousAt A) hΦratio hw
  rwa [← modelDerivative_criterion_eq hq hq0 A hw, inv_inv] at hc

theorem modelDerivative_criterion_pos {K : Set ℂ} {q Φ : ℂ → ℂ} {A : ℂ}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0)
    (hDne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative q z ≠ 0)
    (hΨ : AnalyticOnNhd ℂ (exteriorFromModel q A) exteriorDisk)
    (hΦ : AnalyticOnNhd ℂ Φ Kᶜ)
    (hΨmap : MapsTo (exteriorFromModel q A) exteriorDisk Kᶜ)
    (hΦmap : MapsTo Φ Kᶜ exteriorDisk)
    (hleft : ∀ w ∈ exteriorDisk, Φ (exteriorFromModel q A w) = w)
    (hright : ∀ y ∈ Kᶜ, exteriorFromModel q A (Φ y) = y)
    (hΦratio : Tendsto (fun y => Φ y / y) (cocompact ℂ) (𝓝 (q 0)⁻¹)) :
    ∀ z ∈ ball (0 : ℂ) 1, 0 < (derivativeCriterion (modelDerivative q) z).re := by
  exact ConvexCriterion.realPart_pos_of_nonneg
    (analytic_derivativeCriterion (modelDerivative_analytic hq hq0) hDne).differentiableOn
    (by simp [derivativeCriterion])
    (modelDerivative_criterion_nonneg hK hne hconv hq hq0 hΨ hΦ hΨmap hΦmap hleft hright hΦratio)

#print axioms modelDerivative_criterion_nonneg
#print axioms modelDerivative_criterion_pos

/-- Applied to the actual Riemann map and its inverse, the model criterion has
no extra geometric or boundary assumptions. -/
theorem laurentModel_criterion_pos {K : Set ℂ}
    (hK : IsCompact K) (hconv : Convex ℝ K) {A : ℂ} (hA : A ∈ K)
    {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (invertedComplement K A))
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hbij : BijOn f (invertedComplement K A) (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (invertedComplement K A))
    (hinv : InvOn g f (invertedComplement K A) (ball 0 1))
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    ∀ z ∈ ball (0 : ℂ) 1,
      0 < (derivativeCriterion (modelDerivative (laurentModel g)) z).re := by
  have hderiv : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0 := fun z hz =>
    RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
      isOpen_ball (invertedComplement_isOpen hK A) hg hf hgmap hinv.2 hz
  have hgd0 : deriv g 0 ≠ 0 := hderiv 0 (by simp)
  have hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0 :=
    fun z hz hz0 => StarLike.value_ne_zero hinv.2 hg0 hz hz0
  have hq := laurentModel_analytic hg hg0 hgd0 hgne
  have hq0 : laurentModel g 0 ≠ 0 := laurentModel_ne_zero hg0 hgd0 hgne (by simp)
  have hDne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative (laurentModel g) z ≠ 0 :=
    fun z hz => modelDerivative_ne_zero hg hg0 hgne hderiv hz
  obtain ⟨hΨ, hΦ, hΨbij, hΦmap, hΨinv, _⟩ :=
    laurentModel_exterior_biholomorphic hK hA hf hg hbij hgmap hinv hf0 hg0
  have hfzero : DifferentiableAt ℂ f 0 := hf.differentiableAt
    ((invertedComplement_isOpen hK A).mem_nhds (zero_mem_invertedComplement K A))
  have hfg : deriv f 0 * deriv g 0 = 1 := by
    have he : f ∘ g =ᶠ[𝓝 (0 : ℂ)] id := by
      filter_upwards [isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1)] with z hz
      exact hinv.2 hz
    have hfgzero : DifferentiableAt ℂ f (g 0) := by simpa [hg0] using hfzero
    have hd := hfgzero.hasDerivAt.comp 0
      (hg.differentiableAt (isOpen_ball.mem_nhds (by simp : (0 : ℂ) ∈ ball 0 1))).hasDerivAt
    have he' := he.deriv_eq
    rw [hd.deriv] at he'
    simpa [hg0] using he'
  have hfd0 : deriv f 0 ≠ 0 := by intro he; simp [he] at hfg
  have hfd : deriv f 0 = laurentModel g 0 := by
    rw [laurentModel_zero]
    apply mul_right_cancel₀ hgd0
    simpa [hgd0] using hfg
  have hΦratio : Tendsto (fun y => exteriorInverseFromDisk f A y / y)
      (cocompact ℂ) (𝓝 (laurentModel g 0)⁻¹) := by
    simpa only [hfd] using exteriorInverse_ratio_tendsto hfzero hf0 hfd0 A
  exact modelDerivative_criterion_pos hK ⟨A, hA⟩ hconv hq hq0 hDne
    ((analyticOnNhd_iff_differentiableOn exteriorDisk_isOpen).mpr hΨ)
    ((analyticOnNhd_iff_differentiableOn hK.isClosed.isOpen_compl).mpr hΦ)
    hΨbij.mapsTo hΦmap hΨinv.1 hΨinv.2 hΦratio

theorem laurentModel_derivative_bound {K : Set ℂ}
    (hK : IsCompact K) (hconv : Convex ℝ K) {A : ℂ} (hA : A ∈ K)
    {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (invertedComplement K A))
    (hg : DifferentiableOn ℂ g (ball 0 1))
    (hbij : BijOn f (invertedComplement K A) (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (invertedComplement K A))
    (hinv : InvOn g f (invertedComplement K A) (ball 0 1))
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) :
    ∀ z ∈ ball (0 : ℂ) 1, ‖modelDerivative (laurentModel g) z‖ ≤ 1 + ‖z‖ ^ 2 := by
  have hderiv : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0 := fun z hz =>
    RiemannBiholomorphic.deriv_ne_zero_of_biholomorphic
      isOpen_ball (invertedComplement_isOpen hK A) hg hf hgmap hinv.2 hz
  have hgd0 : deriv g 0 ≠ 0 := hderiv 0 (by simp)
  have hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0 :=
    fun z hz hz0 => StarLike.value_ne_zero hinv.2 hg0 hz hz0
  have hq := laurentModel_analytic hg hg0 hgd0 hgne
  have hq0 : laurentModel g 0 ≠ 0 := laurentModel_ne_zero hg0 hgd0 hgne (by simp)
  have hDne : ∀ z ∈ ball (0 : ℂ) 1, modelDerivative (laurentModel g) z ≠ 0 :=
    fun z hz => modelDerivative_ne_zero hg hg0 hgne hderiv hz
  exact fun z hz => normalized_derivative_bound (modelDerivative_analytic hq hq0)
    hDne (modelDerivative_zero hq0)
    (modelDerivative_hasDerivAt_zero (hq 0 (by simp))).deriv
    (fun z hz => (laurentModel_criterion_pos hK hconv hA hf hg hbij hgmap hinv hf0 hg0 z hz).le) hz

#print axioms laurentModel_criterion_pos
#print axioms laurentModel_derivative_bound

end
end ExteriorReduction.ExteriorEnvelope
