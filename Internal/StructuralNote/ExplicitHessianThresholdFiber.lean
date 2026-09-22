import StructuralNote.ExplicitHessianThreshold
import StructuralNote.CommonFiberHessian
import StructuralNote.CommonFiberCanonicalObjective
import StructuralNote.CommonDomainSegments
import Mathlib.Analysis.Convex.Deriv

/-! Pointwise common-fiber differential and Hessian estimates above the
explicit order threshold. -/

namespace StructuralNote.ExplicitHessianThresholdFiber

open Erdos1045 Erdos1045.EventualExact Complex Filter SchurSpectrum LensClosure
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius DiscreteEnergy
open CommonFiberGeometry CommonFiberFirstDerivative CommonFiberSecondDerivative CommonFiberFullSecond
open CommonFiberDifferentialEstimate CommonFiberSecondEstimate CommonFiberSmallCoefficients
open CommonFiberHessianGeometryChord CommonFiberHessianGeometryGradient CommonFiberHessianGeometryVelocity
open CommonFiberHessianGeometryDomain
open LogDiscriminantSecondDerivative LogDiscriminantHessian HessianComparison HessianErrorLimits
open ExplicitHessianThreshold
open CommonFiberSmooth CommonFiberCanonical CommonFiberCanonicalPaths CommonFiberCanonicalObjective
open CommonDomainSegments CommonDomainConvexity
open scoped BigOperators Topology ContDiff
noncomputable section

/-- The first actual common-fiber derivative estimate at every even order
above `orderThreshold`. -/
theorem actual_first_derivative {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
    (ξ : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (x : ℝ) (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ ξ' x)
    (hdom : InDomain hm (θ x) (v x)) (hroot : ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hmean : (∑ j, (η j : ℂ)) = 0) (hh : ParameterSpace hm h)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ
      (coordinates hm (v s)) (ξ s) = 0) :
    (∀ j, HasDerivAt (fun s => CommonFiberGeometry.center hm (θ s) (v s) σ (ξ s) j)
      (centerVelocity hm (θ x) (v x) σ (ξ x) η h ξ' j) x) ∧
    pairEnergy (by omega) (centerVelocity hm (θ x) (v x) σ (ξ x) η h ξ' - h) ≤
      4000000000 / (2 * m : ℝ) * pairEnergy (by omega) (fun j => (η j : ℂ)) +
      4000000000 * (logOrder (2 * m) : ℝ) ^ 2 * Real.log (2 * m : ℝ) /
        (2 * m : ℝ) ^ 3 * pairEnergy (by omega) h := by
  have hsize := size_conditions hn
  have hs := domain_jacobian_small hsize.1 (θ x) (v x) σ hdom hroot hsize.2.1
  have ht (j : Fin m) : heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4 := by
    have hj := hs j
    have hb : |heightParameter (coordinates hm (v x)) (ξ x) j| ≤ 1 / 4 := by
      linarith [abs_nonneg (phase hm (θ x) j - LensClosure.midpoint m j)]
    nlinarith only [(abs_le.mp hb).1, (abs_le.mp hb).2]
  refine ⟨center_hasDerivAt hm σ hθ hv hξ ht, ?_⟩
  exact first_derivative_energy_bound hsize.1 (θ x) (v x) σ (ξ x) η h ξ' hdom hroot
    hmean hh (velocity_sum_eq_zero hm σ hθ hv hξ ht hz) hσ hsize.2.1
    hsize.2.2.1 hsize.2.2.2

/-- The second actual common-fiber derivative estimate at every even order
above `orderThreshold`. -/
theorem actual_second_derivative {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
    (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ)
    (hfirst : ∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s)
    (hξ' : HasDerivAt ξ' ξ'' x) (hdom : InDomain hm (θ x) (v x))
    (hroot : ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2) (hmean : (∑ j, (η j : ℂ)) = 0)
    (hh : ParameterSpace hm h) (hσ : ∀ j, |σ j| ≤ 1)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ
      (coordinates hm (v s)) (ξ s) = 0) :
    (∀ j, HasDerivAt (fun s => centerVelocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j)
      (centerAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j) x) ∧
    (∑ j, ‖centerAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j‖) ≤
      1000000000 * ((pairEnergy (by omega) h +
        pairEnergy (by omega) (fun j => (η j : ℂ))) / (2 * m : ℝ) +
        Real.sqrt (pairEnergy (by omega) h * pairEnergy (by omega) (fun j => (η j : ℂ))) /
          Real.sqrt (2 * m : ℝ)) := by
  have hsize := size_conditions hn
  have hp := hfirst.self_of_nhds
  have hsmall := domain_jacobian_small hsize.1 (θ x) (v x) σ hdom hroot hsize.2.1
  have ht (j : Fin m) : heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4 := by
    have hj := hsmall j
    have hb : |heightParameter (coordinates hm (v x)) (ξ x) j| ≤ 1 / 4 := by
      linarith [abs_nonneg (phase hm (θ x) j - LensClosure.midpoint m j)]
    nlinarith only [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have htn : ∀ᶠ s in 𝓝 x, ∀ j,
      heightParameter (coordinates hm (v s)) (ξ s) j ^ 2 < 4 := by
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
  exact second_derivative_bound hsize.1 (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' hdom
    hroot hmean hh (velocity_sum_eq_zero hm σ hp.1 hp.2.1 hp.2.2 ht hz)
    (acceleration_sum_eq_zero hm σ hf hξ' hz) hσ hsize.2.1 hsize.2.2.1

/-- At the explicit threshold, the actual velocity differs from the regular
linear velocity by at most `1 / 10000` in pair-energy norm. -/
theorem actual_velocity_error_small {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
    (ξ : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (x : ℝ) (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ ξ' x)
    (hdom : InDomain hm (θ x) (v x)) (hroot : ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hmean : (∑ j, (η j : ℂ)) = 0) (hh : ParameterSpace hm h)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ
      (coordinates hm (v s)) (ξ s) = 0) :
    pairEnergy (by omega) (velocityError hm (θ x) (v x) σ (ξ x) η h ξ') ≤
      (1 / 10000 : ℝ) ^ 2 *
        (realEnergy (by omega) η + pairEnergy (by omega) h) := by
  have hsize := size_conditions hn
  have hf := (actual_first_derivative hn hm θ v ξ η h ξ' x σ hθ hv hξ hdom hroot
    hmean hh hσ hz).2
  have hcoarse := velocity_energy_coarse hm (θ x) (v x) σ (ξ x) η h ξ' hdom hmean
    hsize.2.1 hf
  have hcoef := velocity_coefficient_small hn
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hcoef
  exact hcoarse.trans (mul_le_mul_of_nonneg_right hcoef
    (add_nonneg (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _)))

/-- The pointwise actual common-fiber Hessian estimate at every even order
above the explicit threshold. -/
theorem actual_hessian {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
    (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ)
    (hfirst : ∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s)
    (hξ' : HasDerivAt ξ' ξ'' x) (hdom : InDomain hm (θ x) (v x))
    (hroot : ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hη : HalfPeriodic hm (fun j => (η j : ℂ))) (hmean : (∑ j, (η j : ℂ)) = 0)
    (hh : ParameterSpace hm h) (hσ : ∀ j, |σ j| ≤ 1)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ
      (coordinates hm (v s)) (ξ s) = 0) :
    second (configuration hm (θ x) (v x) σ (ξ x))
      (fullVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x))
      (fullAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'') ≤
        -pairEnergy (by omega) h / 64 - pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hsize := size_conditions hn
  have herr := error_small hn
  have hp := hfirst.self_of_nhds
  have hz0 := hz.self_of_nhds
  have hsmall := domain_jacobian_small hsize.1 (θ x) (v x) σ hdom hroot hsize.2.1
  have ht (j : Fin m) : heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4 := by
    have hj := hsmall j
    have hb : |heightParameter (coordinates hm (v x)) (ξ x) j| ≤ 1 / 4 := by
      linarith [abs_nonneg (phase hm (θ x) j - LensClosure.midpoint m j)]
    nlinarith only [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have htn : ∀ᶠ s in 𝓝 x, ∀ j,
      heightParameter (coordinates hm (v s)) (ξ s) j ^ 2 < 4 := by
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
  have ha := HessianAcceleration.centerAcceleration_halfPeriodic hm (θ x) (v x) σ (ξ x)
    η h (ξ' x) ξ'' (acceleration_sum_eq_zero hm σ hf hξ' hz)
  have hvel := actual_velocity_error_small hn hm θ v ξ η h (ξ' x) x σ hp.1 hp.2.1
    hp.2.2 hdom hroot hmean hh hσ hz
  have hacc := (actual_second_derivative hn hm θ v ξ ξ' η h ξ'' x σ hfirst hξ'
    hdom hroot hmean hh hσ hz).2
  have hacc' := hacc.trans (acceleration_bound (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _))
  have hgrad := domain_gradient_bound (by omega : 8 ≤ m) (θ x) (v x) σ (ξ x)
    hdom hσ hroot hz0 hsize.2.2.1
    (by simpa only [chordError, Nat.cast_mul, Nat.cast_ofNat] using herr.1)
  have hroots : SignedPressureAngular.root (2 * m) = HessianReferencePotential.root (2 * m) := rfl
  rw [hroots] at hgrad
  have hrel := domain_relative_denominator (by omega : 8 ≤ m) (θ x) (v x) σ (ξ x)
    hdom hσ hroot hz0 hsize.2.2.1
  have hr (j : Fin (2 * m)) :
      ‖diameterVector (θ x) j - HessianReferencePotential.root (2 * m) j‖ ≤
        phaseError (2 * m) := by
    have hb := (angularError_point (θ x) j).trans
      (domain_theta_coarse hm (θ x) (v x) hdom j)
    simpa only [angularError, SignedPressureAngular.root, HessianReferencePotential.root,
      phaseError, Nat.cast_mul, Nat.cast_ofNat] using hb
  have hg0 : 0 ≤ gradientBound (2 * m) := by
    unfold gradientBound
    have hl : 0 ≤ Real.log ((2 * m : ℕ) : ℝ) := by
      have hl' : 0 ≤ Real.log (2 * m : ℝ) := by linarith [hsize.2.2.2]
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hl'
    positivity
  have hb := second_upper_bound (by omega : 2 ≤ m)
    (configuration hm (θ x) (v x) σ (ξ x)) (diameterVector (θ x))
    (centerVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x))
    (centerAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'') η h
    (δ := chordError (2 * m)) (ε := 1 / 10000) (G := gradientBound (2 * m))
    (K := accelerationBound (2 * m)) (r := phaseError (2 * m))
    (by unfold chordError; positivity) herr.1 (by norm_num) hg0
    (by unfold phaseError; positivity) hη hmean hh ha (diameterVector_norm (θ x)) hr
    (by change ∀ j, _ ≤ 600 * (logOrder (2 * m) : ℝ) *
          (1 + Real.log ((2 * m : ℕ) : ℝ))
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgrad)
    (by simpa only [chordError, Nat.cast_mul, Nat.cast_ofNat,
      SignedPressureAngular.root, HessianReferencePotential.root] using hrel)
    (by rw [velocityError_eq] at hvel
        change pairEnergy (by omega) (fun j => I * angularError (θ x) j * (η j : ℂ) +
          (centerVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x) j - h j)) ≤ _ at hvel
        exact hvel)
    (by simpa only [accelerationBound, Nat.cast_mul, Nat.cast_ofNat] using hacc')
  exact absorb_error (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _) herr.2 hb

/-- The exact second derivative formula needed to turn the pointwise Hessian
bound into strict curvature. -/
theorem actual_log_formula {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
    (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ)
    (hfirst : ∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s)
    (hξ' : HasDerivAt ξ' ξ'' x) (hdom : InDomain hm (θ x) (v x))
    (hroot : ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2) (hσ : ∀ j, |σ j| ≤ 1)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ
      (coordinates hm (v s)) (ξ s) = 0) :
    HasDerivAt (deriv (fun s => Real.log (Configuration.discriminant
      (configuration hm (θ s) (v s) σ (ξ s)))))
      (second (configuration hm (θ x) (v x) σ (ξ x))
        (fullVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x))
        (fullAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'')) x := by
  have hsize := size_conditions hn
  have herr := error_small hn
  have hp := hfirst.self_of_nhds
  have hsmall := domain_jacobian_small hsize.1 (θ x) (v x) σ hdom hroot hsize.2.1
  have ht (j : Fin m) : heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4 := by
    have hj := hsmall j
    have hb : |heightParameter (coordinates hm (v x)) (ξ x) j| ≤ 1 / 4 := by
      linarith [abs_nonneg (phase hm (θ x) j - LensClosure.midpoint m j)]
    nlinarith only [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have htn : ∀ᶠ s in 𝓝 x, ∀ j,
      heightParameter (coordinates hm (v s)) (ξ s) j ^ 2 < 4 := by
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

/-- Strict negativity of the actual log-discriminant curvature, with the same
explicit even-order threshold. -/
theorem actual_strict_curvature {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
    (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ)
    (hfirst : ∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s)
    (hξ' : HasDerivAt ξ' ξ'' x) (hdom : InDomain hm (θ x) (v x))
    (hroot : ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2)
    (hη : HalfPeriodic hm (fun j => (η j : ℂ))) (hmean : (∑ j, (η j : ℂ)) = 0)
    (hh : ParameterSpace hm h) (hσ : ∀ j, |σ j| ≤ 1)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ
      (coordinates hm (v s)) (ξ s) = 0) (hne : η ≠ 0 ∨ h ≠ 0) :
    deriv (deriv (fun s => Real.log (Configuration.discriminant
      (configuration hm (θ s) (v s) σ (ξ s))))) x < 0 := by
  have hsize := size_conditions hn
  have hd := actual_log_formula hn hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hσ hz
  have hb := actual_hessian hn hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot
    hη hmean hh hσ hz
  have hpos := HessianEnergyPositive.total_energy_pos (by omega : 2 ≤ 2 * m)
    η h hmean hh.2.1 hne
  rw [hd.deriv]
  have he := pairEnergy_nonneg (by omega : 0 < 2 * m) (fun j => (η j : ℂ))
  linarith only [hb, hpos, he]

/-- Strict curvature of the canonical implicit-root fiber along a nonzero
affine direction. -/
theorem canonical_affine_curvature {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (σ : Fin m → ℝ) (x d : FreeParameters m) (t : ℝ)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hdom : ∀ᶠ s in 𝓝 t, affinePath x d s ∈ domain hm)
    (hdθ : HalfPeriodic hm (fun j => (d.1 j : ℂ)))
    (hdmean : (∑ j, (d.1 j : ℂ)) = 0) (hdv : ParameterSpace hm d.2)
    (hdne : d ≠ 0) :
    deriv (deriv (fun s => Real.log (Configuration.discriminant
      (fiber hm σ (affinePath x d s))))) t < 0 := by
  have hsize := size_conditions hn
  have hr := hsize.2.1
  have hderiv := affine_root_derivatives hsize.1 σ hr hσ x d t hdom
  have hfirst : ∀ᶠ s in 𝓝 t,
      (∀ j, HasDerivAt (fun r => (affinePath x d r).1 j) (d.1 j) s) ∧
      (∀ j, HasDerivAt (fun r => (affinePath x d r).2 j) (d.2 j) s) ∧
      HasDerivAt (fun r => root hm σ (affinePath x d r))
        (deriv (fun r => root hm σ (affinePath x d r)) s) s := by
    filter_upwards [hderiv.1] with s hs
    exact ⟨CommonFiberCanonicalCurvature.affine_angle_hasDerivAt x d s,
      CommonFiberCanonicalCurvature.affine_center_hasDerivAt x d s, hs⟩
  have hz := path_closure hsize.1 σ hr hσ (affinePath x d) t hdom
  have hs := root_spec hsize.1 σ (affinePath x d t) hr hσ hdom.self_of_nhds
  have hne : d.1 ≠ 0 ∨ d.2 ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hdne (Prod.ext hh.1 hh.2)
  exact actual_strict_curvature hn hm (fun s => (affinePath x d s).1)
    (fun s => (affinePath x d s).2) (fun s => root hm σ (affinePath x d s))
    (deriv (fun s => root hm σ (affinePath x d s))) d.1 d.2
    (deriv (deriv (fun s => root hm σ (affinePath x d s))) t) t σ hfirst hderiv.2
    hdom.self_of_nhds hs.1 hdθ hdmean hdv hσ hz hne

/-- Smoothness of the canonical objective on the domain, made pointwise by
the explicit threshold. -/
theorem logProduct_contDiffWithinAt {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (σ : Fin m → ℝ) (x : FreeParameters m)
    (hσ : ∀ j, |σ j| ≤ 1) (hx : x ∈ domain hm) :
    ContDiffWithinAt ℝ ∞ (logProduct hm σ) (domain hm) x := by
  have hsize := size_conditions hn
  have herr := error_small hn
  have hroot := root_spec hsize.1 σ x hsize.2.1 hσ hx
  have hi := domain_configuration_injective (by omega : 8 ≤ m) x.1 x.2 σ (root hm σ x)
    hx hσ hroot.1 hroot.2 hsize.2.2.1 (by
      have hh : chordError (2 * m) < 1 := lt_of_le_of_lt herr.1 (by norm_num)
      simpa only [chordError, Nat.cast_mul, Nat.cast_ofNat] using hh)
  exact CommonFiberCanonicalObjective.log_discriminant_contDiffWithinAt
    (fiber hm σ) (domain hm) x (fiber_contDiffWithinAt hsize.1 σ x hsize.2.1 hσ hx) hi

theorem logProduct_continuousOn {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (σ : Fin m → ℝ) (hσ : ∀ j, |σ j| ≤ 1) :
    ContinuousOn (logProduct hm σ) (domain hm) := by
  intro x hx
  exact (logProduct_contDiffWithinAt hn hm σ x hσ hx).continuousWithinAt

/-- The canonical log-product is strictly concave on the full common domain
at every even order above the explicit threshold. -/
theorem logProduct_strictConcaveOn {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (σ : Fin m → ℝ) (hσ : ∀ j, |σ j| ≤ 1) :
    StrictConcaveOn ℝ (domain hm) (logProduct hm σ) := by
  have hcont := logProduct_continuousOn hn hm σ hσ
  refine ⟨domain_convex hm, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let f : ℝ → ℝ := fun t => logProduct hm σ (affinePath x (y - x) t)
  have hmap : Set.MapsTo (affinePath x (y - x)) (Set.Icc 0 1) (domain hm) :=
    fun t ht => affine_between_mem hm x y hx hy ht
  have hf : ContinuousOn f (Set.Icc 0 1) :=
    hcont.comp (affinePath_contDiff x (y - x)).continuous.continuousOn hmap
  have hd := difference_direction hm x y hx hy
  have hne : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hstrict : StrictConcaveOn ℝ (Set.Icc 0 1) f := by
    apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) hf
    intro t ht
    rw [interior_Icc] at ht
    have hh := canonical_affine_curvature hn hm σ x (y - x) t hσ
      (affine_between_near hm x y hx hy ht) hd.1 hd.2.1 hd.2.2 hne
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply, f, logProduct] using hh
  have hh := hstrict.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
    (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have hz : affinePath x (y - x) 0 = x := by simp only [affinePath, zero_smul, add_zero]
  have ho : affinePath x (y - x) 1 = y := by simp only [affinePath, one_smul, add_sub_cancel]
  have hc : affinePath x (y - x) b = a • x + b • y := by
    rw [affine_between, show 1 - b = a by linarith]
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, f, hz, ho, hc] using hh

/-- Any two maximizers of the canonical objective on the common domain agree. -/
theorem logProduct_maximizer_unique {m : ℕ} (hn : orderThreshold ≤ 2 * m)
    (hm : 0 < m) (σ : Fin m → ℝ) (hσ : ∀ j, |σ j| ≤ 1)
    {x y : FreeParameters m} (hx : x ∈ domain hm) (hy : y ∈ domain hm)
    (hxmax : IsMaxOn (logProduct hm σ) (domain hm) x)
    (hymax : IsMaxOn (logProduct hm σ) (domain hm) y) : x = y := by
  exact (logProduct_strictConcaveOn hn hm σ hσ).eq_of_isMaxOn hxmax hymax hx hy

end
end StructuralNote.ExplicitHessianThresholdFiber
