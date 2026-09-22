import AnalyticLaurentModel
import InversionCenterChange
import PositiveNormalization

/-! The actual Faber kernel of a single exterior parametrization.
Its holomorphic extension, normalization and positive real part are derived
from the conformal disk map and convexity, uniformly over all points of K. -/

namespace ExteriorReduction

open Complex Set Metric
noncomputable section

def geometricKernel (q : ℂ → ℂ) (a x z : ℂ) : ℂ :=
  derivativeNumerator q z / (q z + (a - x) * z)

theorem modelDenominator_factor {g : ℂ → ℂ} (hg0 : g 0 = 0)
    (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    {a x z : ℂ} (hz : z ∈ ball 0 1) :
    laurentModel g z + (a - x) * z =
      laurentModel g z * (1 + (a - x) * g z) := by
  have he := laurentModel_mul hg0 hd0 hgne hz
  linear_combination -(a - x) * he

theorem modelDenominator_ne_zero {K : Set ℂ} {g : ℂ → ℂ} {a x : ℂ}
    (hx : x ∈ K) (hgmap : MapsTo g (ball 0 1) (invertedComplement K a))
    (hg0 : g 0 = 0) (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    laurentModel g z + (a - x) * z ≠ 0 := by
  rw [modelDenominator_factor hg0 hd0 hgne hz]
  exact mul_ne_zero (laurentModel_ne_zero hg0 hd0 hgne hz)
    (changeInversionCenter_denominator_ne_zero hx (hgmap hz))

theorem geometricKernel_analytic {K : Set ℂ} {g : ℂ → ℂ} {a x : ℂ}
    (hx : x ∈ K) (hg : DifferentiableOn ℂ g (ball 0 1))
    (hgmap : MapsTo g (ball 0 1) (invertedComplement K a))
    (hg0 : g 0 = 0) (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0) :
    AnalyticOnNhd ℂ (geometricKernel (laurentModel g) a x) (ball 0 1) := by
  have hq := laurentModel_analytic hg hg0 hd0 hgne
  exact (derivativeNumerator_analytic hq).div
    (hq.add (analyticOnNhd_const.mul analyticOnNhd_id))
    (fun _ hz => modelDenominator_ne_zero hx hgmap hg0 hd0 hgne hz)

@[simp] theorem geometricKernel_zero {q : ℂ → ℂ} (hq0 : q 0 ≠ 0) (a x : ℂ) :
    geometricKernel q a x 0 = 1 := by
  simp [geometricKernel, hq0]

theorem geometricKernel_eq {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hg0 : g 0 = 0) (hd0 : deriv g 0 ≠ 0)
    (hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0)
    {a x z : ℂ} (hz : z ∈ ball 0 1) (hz0 : z ≠ 0) :
    geometricKernel (laurentModel g) a x z =
      z * deriv g z / (g z * (1 + (a - x) * g z)) := by
  unfold geometricKernel
  rw [derivativeNumerator_eq hg hg0 hd0 hgne hz,
    modelDenominator_factor hg0 hd0 hgne hz]
  have hq := laurentModel_ne_zero hg0 hd0 hgne hz
  have hgz := hgne z hz hz0
  calc
    _ = (laurentModel g z * g z) * deriv g z /
        (g z * (1 + (a - x) * g z)) := by field_simp
    _ = _ := by rw [laurentModel_mul hg0 hd0 hgne hz]

theorem geometricKernel_re_nonneg {K : Set ℂ} {a x : ℂ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (ha : a ∈ K) (hx : x ∈ K)
    {g f : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hf : DifferentiableOn ℂ f (invertedComplement K a))
    (hgmap : MapsTo g (ball 0 1) (invertedComplement K a))
    (hfmap : MapsTo f (invertedComplement K a) (ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, f (g z) = z) (hg0 : g 0 = 0)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    0 ≤ (geometricKernel (laurentModel g) a x z).re := by
  have hd0 := StarLike.derivative_ne_zero (invertedComplement_isOpen hK a)
    hg hf hgmap hleft (show (0 : ℂ) ∈ ball 0 1 by simp)
  have hgne : ∀ w ∈ ball (0 : ℂ) 1, w ≠ 0 → g w ≠ 0 :=
    fun _ hw hw0 => StarLike.value_ne_zero hleft hg0 hw hw0
  by_cases hz0 : z = 0
  · subst z
    rw [geometricKernel_zero (laurentModel_ne_zero hg0 hd0 hgne (by simp))]
    norm_num
  rw [geometricKernel_eq hg hg0 hd0 hgne hz hz0]
  exact inversionCenter_kernel_re_nonneg hK hconv ha hx hg hf hgmap hfmap hleft hg0 hz hz0

#print axioms geometricKernel_re_nonneg

end
end ExteriorReduction
