import GeometricFaberKernel
import LaurentKernelSeries

/-! The Faber bound for an actual conformal map of a convex complement.
All kernel positivity, nonvanishing and coefficient identities are proved
from the geometric hypotheses. There is no classical Faber theorem input. -/

namespace ExteriorReduction

open Complex Set Metric
noncomputable section

def modelFaberValue (q : ℂ → ℂ) (A x : ℂ) (k : ℕ) : ℂ :=
  FaberKernel.value (FaberKernel.laurentCoefficients (FaberKernel.taylorCoefficients q))
    (FaberKernel.laurentVariable (FaberKernel.taylorCoefficients q) A x) k

@[simp] theorem modelFaberValue_zero (q : ℂ → ℂ) (A x : ℂ) :
    modelFaberValue q A x 0 = 1 := FaberKernel.value_zero _ _

/-- A single disk parametrization supplies the bound at every point of K,
including boundary points and the degenerate case of a line segment. -/
theorem convex_faber_bound {K : Set ℂ} {A x : ℂ}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hA : A ∈ K) (hx : x ∈ K)
    {g f : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 1))
    (hf : DifferentiableOn ℂ f (invertedComplement K A))
    (hgmap : MapsTo g (ball 0 1) (invertedComplement K A))
    (hfmap : MapsTo f (invertedComplement K A) (ball 0 1))
    (hleft : ∀ z ∈ ball (0 : ℂ) 1, f (g z) = z) (hg0 : g 0 = 0)
    (k : ℕ) : ‖modelFaberValue (laurentModel g) A x k‖ ≤ 2 := by
  by_cases hk : k = 0
  · subst k
    simp
  have hd0 := StarLike.derivative_ne_zero (invertedComplement_isOpen hK A)
    hg hf hgmap hleft (show (0 : ℂ) ∈ ball 0 1 by simp)
  have hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0 :=
    fun _ hz hz0 => StarLike.value_ne_zero hleft hg0 hz hz0
  exact FaberKernel.faber_bound_of_positive_laurent_model
    (laurentModel_analytic hg hg0 hd0 hgne) A x
    (fun _ hz => modelDenominator_ne_zero hx hgmap hg0 hd0 hgne hz)
    (fun _ hz => geometricKernel_re_nonneg hK hconv hA hx hg hf hgmap hfmap hleft hg0 hz)
    k hk

/-- Normalization and all Faber bounds are produced together from only compact
convex geometry and two different points. In particular the map does not depend
on the evaluation point x or on the polynomial index k. -/
theorem exists_normalized_convex_faber_model {K : Set ℂ}
    (hK : IsCompact K) (hconv : Convex ℝ K) {A y : ℂ}
    (hA : A ∈ K) (hy : y ∈ K) (hyA : y ≠ A) :
    ∃ (f g : ℂ → ℂ) (c : ℝ), 0 < c ∧
      DifferentiableOn ℂ f (invertedComplement K A) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f (invertedComplement K A) (ball 0 1) ∧
      MapsTo g (ball 0 1) (invertedComplement K A) ∧
      InvOn g f (invertedComplement K A) (ball 0 1) ∧
      f 0 = 0 ∧ g 0 = 0 ∧ laurentModel g 0 = (c : ℂ) ∧
      AnalyticOnNhd ℂ (laurentModel g) (ball 0 1) ∧
      (∀ x ∈ K, ∀ k, ‖modelFaberValue (laurentModel g) A x k‖ ≤ 2) := by
  obtain ⟨f, g, c, hc, hf, hg, hbij, hgmap, hinv, hf0, hg0, hdg⟩ :=
    exists_positive_inverted_biholomorphic hK hconv hA hy hyA
  have hd0 := StarLike.derivative_ne_zero (invertedComplement_isOpen hK A)
    hg hf hgmap (fun _ hz => hinv.2 hz) (show (0 : ℂ) ∈ ball 0 1 by simp)
  have hgne : ∀ z ∈ ball (0 : ℂ) 1, z ≠ 0 → g z ≠ 0 :=
    fun _ hz hz0 => StarLike.value_ne_zero (fun _ hv => hinv.2 hv) hg0 hz hz0
  refine ⟨f, g, c, hc, hf, hg, hbij, hgmap, hinv, hf0, hg0, ?_,
    laurentModel_analytic hg hg0 hd0 hgne, ?_⟩
  · simp [hdg]
  · intro x hx k
    exact convex_faber_bound hK hconv hA hx hg hf hgmap hbij.mapsTo
      (fun _ hz => hinv.2 hz) hg0 k

#print axioms convex_faber_bound
#print axioms exists_normalized_convex_faber_model

end
end ExteriorReduction
