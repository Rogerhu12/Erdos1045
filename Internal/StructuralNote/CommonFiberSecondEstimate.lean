import StructuralNote.CommonFiberAccelerationSource
import StructuralNote.SecondDerivativeBudget

/-! The uniform second differential estimate (9.10) on the literal common
domain. Neither a source estimate nor a bound on the root derivative is assumed. -/

namespace StructuralNote.CommonFiberSecondEstimate

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberFirstDerivative CommonFiberSecondDerivative CommonFiberDerivativeEnergy
open CommonFiberDifferentialEstimate CommonFiberSmallCoefficients CommonFiberHeightEstimate
open CommonFiberAccelerationSource SecondDerivativeBudget SchurSpectrum Filter
open scoped BigOperators Topology
noncomputable section

theorem second_derivative_bound {m : ℕ} (hm : 128 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' ξ'' : ℂ)
    (hdom : InDomain (by omega) θ v) (hξ : ‖ξ‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hmean : ∑ j, (η j : ℂ) = 0) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0)
    (hzz : (∑ j, acceleration (by omega) θ v σ ξ η h ξ' ξ'' j) = 0)
    (hσ : ∀ j, |σ j| ≤ 1) (hscale : energyRadius (2 * m) ≤ 1 / (2 * m : ℝ))
    (horder : 10 * (logOrder (2 * m) : ℝ) + 1024 ≤ 2 * m) :
    (∑ j, ‖centerAcceleration (by omega) θ v σ ξ η h ξ' ξ'' j‖) ≤
      1000000000 * ((pairEnergy (by omega) h + pairEnergy (by omega) (fun j => (η j : ℂ))) /
        (2 * m : ℝ) + Real.sqrt (pairEnergy (by omega) h *
          pairEnergy (by omega) (fun j => (η j : ℂ))) / Real.sqrt (2 * m : ℝ)) := by
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have hn25 : (25 : ℝ) ≤ 2 * m := by exact_mod_cast (show 25 ≤ 2 * m by omega)
  have hsmall := domain_jacobian_small hm θ v σ hdom hξ hscale
  have hB : bodyNorm (by omega) θ v σ ξ ≤ 2 / (2 * m : ℝ) := by
    calc
      _ ≤ (10 * (logOrder (2 * m) : ℝ) + 1049) / (2 * m : ℝ) ^ 2 :=
        domain_bodyNorm_bound (by omega) θ v σ hdom hξ hσ horder
      _ ≤ (2 * (2 * m)) / (2 * m : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
      _ = _ := by field_simp
  have hS := domain_sineNorm_bound (by omega) θ v hdom horder
  have ht (j : Fin m) : |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 := by
    have hj := hsmall j
    linarith [abs_nonneg (phase (by omega) θ j - LensClosure.midpoint m j)]
  have hsource := source_sum_bound (by omega) θ v σ ξ η h ξ'
    (B := 2 / (2 * m : ℝ)) (S := 5 / (2 * m : ℝ)) (by positivity) hσ ht
    (fun j => (norm_le_pi_norm (fun k : Fin m => body
      (2 * Real.cos (halfAngle (by omega) θ k)) (σ k)
      (heightParameter (coordinates (by omega) v) ξ k)) j).trans hB)
    (fun j => ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm
      (fun k : Fin m => Real.sin (halfAngle (by omega) θ k)) j)).trans hS)
  have havg := average_energy (by omega) η hmean
  have hdiff := half_difference_energy (by omega) η
  have hd : (2 * m : ℝ) ^ 2 * (∑ j : Fin m,
      angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2) ≤
        128 * pairEnergy (by omega) (fun j => (η j : ℂ)) := by
    have hp : 8 * Real.pi ^ 2 ≤ 128 := by nlinarith [Real.pi_pos, Real.pi_lt_four]
    exact hdiff.trans (mul_le_mul_of_nonneg_right hp (pairEnergy_nonneg _ _))
  have hu := domain_height_velocity_energy hm θ v σ ξ η h ξ' hdom hξ hmean hh hz hσ hscale horder
  have hmix := mixed_sum_bound
    (fun j : Fin m => angleAverage (by omega) η (CommonClosureEnergy.halfIndex j))
    (heightParameter (coordinates (by omega) h) ξ') (by linarith : (1 : ℝ) ≤ 2 * m)
    (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _) havg hu
  have htotal := acceleration_budget (by linarith : (1 : ℝ) ≤ 2 * m)
    (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _) (by positivity)
    havg hd hu hmix hsource
  exact (centerAcceleration_source_bound (by omega) θ v σ ξ η h ξ' ξ'' hσ hsmall hzz).trans htotal

/-- Actual closed paths satisfy (9.10). Ordinary differentiability is the only
path regularity input; the small-height neighborhood follows from the domain. -/
theorem eventual_actual_second_derivative : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
      (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
      (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ),
    (∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s) →
    HasDerivAt ξ' ξ'' x → InDomain hm (θ x) (v x) → ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    (∑ j, (η j : ℂ)) = 0 → ParameterSpace hm h → (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 x, closure (phase hm (θ s)) (fun j => 2 * Real.cos (halfAngle hm (θ s) j))
      σ (coordinates hm (v s)) (ξ s) = 0) →
    (∀ j, HasDerivAt (fun s => centerVelocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j)
      (centerAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j) x) ∧
    (∑ j, ‖centerAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j‖) ≤
      1000000000 * ((pairEnergy (by omega) h + pairEnergy (by omega) (fun j => (η j : ℂ))) /
        (2 * m : ℝ) + Real.sqrt (pairEnergy (by omega) h *
          pairEnergy (by omega) (fun j => (η j : ℂ))) / Real.sqrt (2 * m : ℝ)) := by
  filter_upwards [eventual_size_conditions] with m hsize
  intro hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hmean hh hσ hz
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
  refine ⟨centerVelocity_hasDerivAt hm σ hp.1 hp.2.1 hp.2.2 hξ' ht, ?_⟩
  exact second_derivative_bound hsize.1 (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' hdom hroot hmean hh
    (velocity_sum_eq_zero hm σ hp.1 hp.2.1 hp.2.2 ht hz)
    (acceleration_sum_eq_zero hm σ hf hξ' hz) hσ hsize.2.1 hsize.2.2.1

end
end StructuralNote.CommonFiberSecondEstimate
