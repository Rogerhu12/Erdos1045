import ExteriorExistence
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The analytic model at infinity of an actual exterior map

The removable extension q(z)=z/g(z) is constructed as the reciprocal of
the divided difference of g. Its derivative numerator q-zq' is analytic,
nonvanishing, and has zero first derivative at zero. Thus the normalized
exterior derivative is obtained from ordinary disk-map hypotheses.
-/

namespace ExteriorReduction

open Complex Set Metric Filter
open scoped Topology

noncomputable section

def laurentModel (g : ℂ → ℂ) (z : ℂ) : ℂ := (dslope g 0 z)⁻¹

def derivativeNumerator (q : ℂ → ℂ) (z : ℂ) : ℂ := q z - z * deriv q z

def modelDerivative (q : ℂ → ℂ) (z : ℂ) : ℂ := derivativeNumerator q z / q 0

@[simp] theorem laurentModel_zero (g : ℂ → ℂ) : laurentModel g 0 = (deriv g 0)⁻¹ := by
  simp [laurentModel]

theorem dslope_ne_zero_on_disk {g : ℂ → ℂ} (hg0 : g 0 = 0)
    (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) : dslope g 0 z ≠ 0 := by
  by_cases hz0 : z = 0
  · simpa [hz0] using hd0
  rw [dslope_of_ne _ hz0, slope_def_field, sub_zero, hg0, sub_zero]
  exact div_ne_zero (hgne z hz hz0) hz0

theorem laurentModel_analytic {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0)
    (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0) :
    AnalyticOnNhd ℂ (laurentModel g) (ball 0 1) := by
  have hds := (Complex.differentiableOn_dslope (ball_mem_nhds (0 : ℂ) zero_lt_one)).mpr hg
  exact (hds.inv (fun _ hz => dslope_ne_zero_on_disk hg0 hd0 hgne hz)).analyticOnNhd isOpen_ball

theorem laurentModel_ne_zero {g : ℂ → ℂ} (hg0 : g 0 = 0)
    (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) : laurentModel g z ≠ 0 :=
  inv_ne_zero (dslope_ne_zero_on_disk hg0 hd0 hgne hz)

theorem laurentModel_mul {g : ℂ → ℂ} (hg0 : g 0 = 0)
    (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) : laurentModel g z * g z = z := by
  have he := sub_smul_dslope g 0 z
  simp only [hg0, sub_zero, smul_eq_mul] at he
  rw [← he, laurentModel]
  field_simp [dslope_ne_zero_on_disk hg0 hd0 hgne hz]

theorem laurentModel_eq_div {g : ℂ → ℂ} (hg0 : g 0 = 0)
    {z : ℂ} (hz : z ≠ 0) : laurentModel g z = z / g z := by
  simp [laurentModel, dslope_of_ne _ hz, slope_def_field, hg0]

theorem derivativeNumerator_analytic {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) :
    AnalyticOnNhd ℂ (derivativeNumerator q) (ball 0 1) :=
  hq.sub (analyticOnNhd_id.mul hq.deriv)

@[simp] theorem derivativeNumerator_zero (q : ℂ → ℂ) : derivativeNumerator q 0 = q 0 := by
  simp [derivativeNumerator]

theorem derivativeNumerator_hasDerivAt_zero {q : ℂ → ℂ} (hq : AnalyticAt ℂ q 0) :
    HasDerivAt (derivativeNumerator q) 0 0 := by
  convert! hq.differentiableAt.hasDerivAt.sub
    ((hasDerivAt_id (0 : ℂ)).mul hq.deriv.differentiableAt.hasDerivAt) using 1
  simp

theorem derivativeNumerator_eq {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0)
    (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    derivativeNumerator (laurentModel g) z = laurentModel g z ^ 2 * deriv g z := by
  have hq := laurentModel_analytic hg hg0 hd0 hgne
  have he : (fun w => laurentModel g w * g w) =ᶠ[𝓝 z] (fun w => w) := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact laurentModel_mul hg0 hd0 hgne hw
  have hproduct := (hq z hz).differentiableAt.hasDerivAt.mul
    (hg.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hd := (hproduct.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id z)
  have hzq := laurentModel_mul hg0 hd0 hgne hz
  unfold derivativeNumerator
  linear_combination -laurentModel g z * hd + deriv (laurentModel g) z * hzq

theorem modelDerivative_analytic {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (hq0 : q 0 ≠ 0) :
    AnalyticOnNhd ℂ (modelDerivative q) (ball 0 1) :=
  (derivativeNumerator_analytic hq).div analyticOnNhd_const (fun _ _ => hq0)

theorem modelDerivative_zero {q : ℂ → ℂ} (hq0 : q 0 ≠ 0) : modelDerivative q 0 = 1 := by
  simp [modelDerivative, hq0]

theorem modelDerivative_hasDerivAt_zero {q : ℂ → ℂ}
    (hq : AnalyticAt ℂ q 0) : HasDerivAt (modelDerivative q) 0 0 := by
  convert! (derivativeNumerator_hasDerivAt_zero hq).div_const (q 0) using 1
  simp

theorem modelDerivative_ne_zero {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (ball 0 1)) (hg0 : g 0 = 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    (hderiv : ∀ z ∈ ball (0 : ℂ) 1, deriv g z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) : modelDerivative (laurentModel g) z ≠ 0 := by
  have hd0 := hderiv 0 (by simp)
  unfold modelDerivative
  rw [derivativeNumerator_eq hg hg0 hd0 hgne hz]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero 2 (laurentModel_ne_zero hg0 hd0 hgne hz))
    (hderiv z hz)) (laurentModel_ne_zero hg0 hd0 hgne (by simp))

/-- The Laurent model is tied to the actual map, not an abstract coefficient witness. -/
theorem exterior_eq_laurentModel {g : ℂ → ℂ} (hg0 : g 0 = 0) (a : ℂ)
    {w : ℂ} (hw : w ≠ 0) : a + (g w⁻¹)⁻¹ = a + w * laurentModel g w⁻¹ := by
  rw [laurentModel_eq_div hg0 (inv_ne_zero hw)]
  field_simp

#print axioms derivativeNumerator_eq
#print axioms modelDerivative_ne_zero

end
end ExteriorReduction
