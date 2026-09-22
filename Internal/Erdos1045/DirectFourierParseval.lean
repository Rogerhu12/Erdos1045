import Erdos1045.FourierDefinitions
import Mathlib.Analysis.Fourier.AddCircle

/-! Parseval for the actual absolutely convergent series, obtained from finite
orthogonality and convergence in continuous functions. No Sobolev realization
or external Fourier interface is used. -/

namespace Erdos1045.DirectFourier

open MeasureTheory AddCircle
open scoped BigOperators ComplexConjugate
noncomputable section

local instance period_pos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

abbrev Circle := AddCircle (2 * Real.pi)
abbrev CircleL2 := Lp ℂ 2 (haarAddCircle (T := 2 * Real.pi))

def monomial (m : ℕ) : C(Circle, ℂ) := fourier (-(m : ℤ))

theorem monomial_coe (m : ℕ) (t : ℝ) :
    monomial m (t : Circle) = FaberFourier.character m t := by
  rw [monomial, fourier_coe_apply]
  unfold FaberFourier.character
  congr 1
  push_cast
  field_simp

theorem monomial_norm (m : ℕ) : ‖monomial m‖ = 1 := by
  exact fourier_norm _

def sumMap (d : ℕ → ℂ) : C(Circle, ℂ) := ∑' m, d m • monomial m

theorem summable_monomials {d : ℕ → ℂ} (hd : Summable (fun m => ‖d m‖)) :
    Summable (fun m => d m • monomial m) := by
  apply Summable.of_norm
  simpa only [norm_smul, monomial_norm, mul_one] using hd

theorem sumMap_coe {d : ℕ → ℂ} (hd : Summable (fun m => ‖d m‖)) (t : ℝ) :
    sumMap d (t : Circle) = FaberFourier.series d t := by
  have hs := (ContinuousMap.evalCLM ℂ (t : Circle)).hasSum (summable_monomials hd).hasSum
  simpa only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply, smul_eq_mul,
    monomial_coe, FaberFourier.series, sumMap] using hs.tsum_eq.symm

theorem sumMap_l2_hasSum {d : ℕ → ℂ} (hd : Summable (fun m => ‖d m‖)) :
    HasSum (fun m => d m • (fourierLp 2 (-(m : ℤ)) : CircleL2))
      (ContinuousMap.toLp 2 haarAddCircle ℂ (sumMap d)) := by
  simpa only [sumMap, map_smul, monomial, fourierLp] using
    (ContinuousMap.toLp 2 haarAddCircle ℂ).hasSum (summable_monomials hd).hasSum

theorem l2_square (f : C(Circle, ℂ)) :
    ‖ContinuousMap.toLp 2 haarAddCircle ℂ f‖ ^ 2 =
      ∫ t : Circle, ‖f t‖ ^ 2 ∂haarAddCircle := by
  let g : CircleL2 := ContinuousMap.toLp 2 haarAddCircle ℂ f
  have h := congr_arg Complex.re (L2.inner_def g g)
  change RCLike.re (inner ℂ g g) = RCLike.re
    (∫ t : Circle, inner ℂ (g t) (g t) ∂haarAddCircle) at h
  rw [← integral_re] at h
  · change ‖g‖ ^ 2 = _
    rw [@norm_sq_eq_re_inner ℂ]
    rw [h]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle f] with t ht
    rw [← norm_sq_eq_re_inner]
    change ‖(ContinuousMap.toLp 2 haarAddCircle ℂ f) t‖ ^ 2 = _
    rw [ht]
  · exact L2.integrable_inner g g

theorem sumMap_parseval {d : ℕ → ℂ} (hd : Summable (fun m => ‖d m‖)) :
    HasSum (fun m => ‖d m‖ ^ 2) (∫ t : Circle, ‖sumMap d t‖ ^ 2 ∂haarAddCircle) := by
  have ho : Orthonormal ℂ (fun m : ℕ => (fourierLp 2 (-(m : ℤ)) : CircleL2)) :=
    orthonormal_fourier.comp _ (fun a b h => by exact_mod_cast neg_injective h)
  have hs := (sumMap_l2_hasSum hd).norm.pow 2
  rw [l2_square] at hs
  have heq (s : Finset ℕ) :
      ‖∑ m ∈ s, d m • (fourierLp 2 (-(m : ℤ)) : CircleL2)‖ ^ 2 =
        ∑ m ∈ s, ‖d m‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, ho.inner_sum]
    simp [map_sum, RCLike.mul_re, Complex.normSq_apply, Complex.sq_norm]
  change Filter.Tendsto _ _ _
  simpa only [heq] using hs

theorem series_continuous {d : ℕ → ℂ} (hd : Summable (fun m => ‖d m‖)) :
    Continuous (FaberFourier.series d) := by
  have h : Continuous (fun t : ℝ => sumMap d (t : Circle)) := by fun_prop
  simpa only [sumMap_coe hd] using h

theorem series_square_integrable {d : ℕ → ℂ} (hd : Summable (fun m => ‖d m‖)) :
    Integrable (fun t => ‖FaberFourier.series d t‖ ^ 2) FaberFourier.circleMeasure := by
  exact ((series_continuous hd).norm.pow 2).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self

theorem circle_energy_eq {d : ℕ → ℂ} (hd : Summable (fun m => ‖d m‖)) :
    FaberFourier.energy (FaberFourier.series d) =
      (2 * Real.pi) * (∫ t : Circle, ‖sumMap d t‖ ^ 2 ∂haarAddCircle) := by
  unfold FaberFourier.energy FaberFourier.circleMeasure
  rw [← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  simp_rw [← sumMap_coe hd]
  have h := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
    (fun t : Circle => ‖sumMap d t‖ ^ 2)
  simp only [zero_add] at h
  rw [h, volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * Real.pi), smul_eq_mul]

/-- Ordinary Parseval for the actual analytic series, with no classical
Fourier assumptions. -/
theorem parseval (d : ℕ → ℂ) (hd : Summable (fun m => ‖d m‖)) :
    Summable (fun m => ‖d m‖ ^ 2) ∧
    Integrable (fun t => ‖FaberFourier.series d t‖ ^ 2) FaberFourier.circleMeasure ∧
      FaberFourier.energy (FaberFourier.series d) =
        2 * Real.pi * (∑' m, ‖d m‖ ^ 2) := by
  have hp := sumMap_parseval hd
  exact ⟨hp.summable, series_square_integrable hd, by rw [circle_energy_eq hd, hp.tsum_eq]⟩

end
end Erdos1045.DirectFourier
