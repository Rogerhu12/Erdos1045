import StructuralNote.CommonFiberHessian
import StructuralNote.HessianEnergyPositive

/-! Strictly negative actual second log-discriminant derivative on every
nonzero admissible affine direction of the common fiber. -/

namespace StructuralNote.CommonFiberLogCurvature

open Erdos1045 Erdos1045.EventualExact Complex Filter SchurSpectrum LensClosure
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberFirstDerivative CommonFiberSecondDerivative CommonFiberFullSecond
open CommonFiberDifferentialEstimate CommonFiberSmallCoefficients CommonFiberHessianGeometryDomain
open LogDiscriminantSecondDerivative LogDiscriminantHessian HessianErrorLimits CommonFiberHessian
open scoped BigOperators Topology
noncomputable section

theorem eventual_actual_log_formula : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
      (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
      (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ),
    (∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s) →
    HasDerivAt ξ' ξ'' x → InDomain hm (θ x) (v x) → ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 x, closure (phase hm (θ s)) (fun j => 2 * Real.cos (halfAngle hm (θ s) j))
      σ (coordinates hm (v s)) (ξ s) = 0) →
    HasDerivAt (deriv (fun s => Real.log (Configuration.discriminant
      (configuration hm (θ s) (v s) σ (ξ s)))))
      (second (configuration hm (θ x) (v x) σ (ξ x))
        (fullVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x))
        (fullAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'')) x := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  filter_upwards [eventual_size_conditions, hnat.eventually eventual_error_small] with m hsize herr
  intro hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hσ hz
  have hp := hfirst.self_of_nhds
  have hsmall := domain_jacobian_small hsize.1 (θ x) (v x) σ hdom hroot hsize.2.1
  have ht (j : Fin m) : heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4 := by
    have hj := hsmall j
    have hb : |heightParameter (coordinates hm (v x)) (ξ x) j| ≤ 1 / 4 := by
      linarith [abs_nonneg (phase hm (θ x) j - LensClosure.midpoint m j)]
    nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have htn : ∀ᶠ s in 𝓝 x, ∀ j, heightParameter (coordinates hm (v s)) (ξ s) j ^ 2 < 4 := by
    rw [Filter.eventually_all]
    intro j
    have hd := LensClosurePathDerivatives.heightParameter_hasDerivAt
      (coordinates_hasDerivAt hm hp.2.1) hp.2.2 j
    exact (hd.continuousAt.pow 2).tendsto.eventually (eventually_lt_nhds (ht j))
  have hf : ∀ᶠ s in 𝓝 x,
      (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s ∧
      (∀ j, heightParameter (coordinates hm (v s)) (ξ s) j ^ 2 < 4) := by
    filter_upwards [hfirst, htn] with s hs hts
    exact ⟨hs.1, hs.2.1, hs.2.2, hts⟩
  have hi := domain_configuration_injective (by omega : 8 ≤ m) (θ x) (v x) σ (ξ x)
    hdom hσ hroot hz.self_of_nhds hsize.2.2.1 (by
      have hh : chordError (2 * m) < 1 := lt_of_le_of_lt herr.1 (by norm_num)
      simpa only [chordError, Nat.cast_mul, Nat.cast_ofNat] using hh)
  simpa only [second_eq_quadratic_add_acceleration] using
    actual_log_second_derivative hm σ hf hξ' hi

theorem eventual_actual_strict_curvature : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
      (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
      (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ),
    (∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s) →
    HasDerivAt ξ' ξ'' x → InDomain hm (θ x) (v x) → ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    HalfPeriodic hm (fun j => (η j : ℂ)) → (∑ j, (η j : ℂ)) = 0 →
    ParameterSpace hm h → (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 x, closure (phase hm (θ s)) (fun j => 2 * Real.cos (halfAngle hm (θ s) j))
      σ (coordinates hm (v s)) (ξ s) = 0) → η ≠ 0 ∨ h ≠ 0 →
    deriv (deriv (fun s => Real.log (Configuration.discriminant
      (configuration hm (θ s) (v s) σ (ξ s))))) x < 0 := by
  filter_upwards [eventual_actual_log_formula, eventual_actual_hessian,
    eventually_ge_atTop 2] with m hformula hhessian hm2
  intro hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hη hmean hh hσ hz hne
  have hd := hformula hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hσ hz
  have hb := hhessian hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hη hmean hh hσ hz
  have hpos := HessianEnergyPositive.total_energy_pos (by omega : 2 ≤ 2 * m) η h hmean hh.2.1 hne
  rw [hd.deriv]
  have he := pairEnergy_nonneg (by omega : 0 < 2 * m) (fun j => (η j : ℂ))
  linarith

end
end StructuralNote.CommonFiberLogCurvature
