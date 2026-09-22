import StructuralNote.HessianErrorLimits
import StructuralNote.CommonFiberHessianGeometryDomain
import StructuralNote.CommonFiberHessianGeometryVelocity

/-! Negative second derivative of the actual closed fiber. All smallness,
gradient, denominator, and derivative estimates follow from the common domain. -/

namespace StructuralNote.CommonFiberHessian

open Erdos1045 Erdos1045.EventualExact Complex Filter SchurSpectrum LensClosure
open CommonClosureEnergy CommonTangentialParameters CommonDomainClosure CommonDomainRadius
open CommonFiberGeometry CommonFiberFirstDerivative CommonFiberSecondDerivative CommonFiberFullSecond
open CommonFiberDifferentialEstimate CommonFiberSecondEstimate CommonFiberSmallCoefficients
open CommonFiberHessianGeometryChord CommonFiberHessianGeometryGradient CommonFiberHessianGeometryVelocity
open CommonFiberHessianGeometryDomain
open LogDiscriminantSecondDerivative LogDiscriminantHessian HessianComparison HessianErrorLimits
open scoped BigOperators Topology
noncomputable section

theorem injective_of_relative {ι : Type*} (z w : ι → ℂ) {δ : ℝ} (hδ : δ < 1)
    (hrelative : ∀ i j, i ≠ j → ‖(z i - z j) / (w i - w j) - 1‖ ≤ δ) :
    Function.Injective z := by
  intro i j hij
  by_contra hne
  have hh := hrelative i j hne
  rw [hij, sub_self, zero_div, zero_sub, norm_neg, norm_one] at hh
  linarith

theorem eventual_actual_hessian : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 0 < m) (θ : ℝ → Fin (2 * m) → ℝ) (v : ℝ → Fin (2 * m) → ℂ)
      (ξ ξ' : ℝ → ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
      (ξ'' : ℂ) (x : ℝ) (σ : Fin m → ℝ),
    (∀ᶠ s in 𝓝 x, (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s) →
    HasDerivAt ξ' ξ'' x → InDomain hm (θ x) (v x) → ‖ξ x‖ ≤ 1024 / (2 * m : ℝ) ^ 2 →
    HalfPeriodic hm (fun j => (η j : ℂ)) → (∑ j, (η j : ℂ)) = 0 →
    ParameterSpace hm h → (∀ j, |σ j| ≤ 1) →
    (∀ᶠ s in 𝓝 x, closure (phase hm (θ s)) (fun j => 2 * Real.cos (halfAngle hm (θ s) j))
      σ (coordinates hm (v s)) (ξ s) = 0) →
    second (configuration hm (θ x) (v x) σ (ξ x))
      (fullVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x))
      (fullAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'') ≤
        -pairEnergy (by omega) h / 64 - pairEnergy (by omega) (fun j => (η j : ℂ)) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    omega
  filter_upwards [eventual_size_conditions, hnat.eventually eventual_error_small,
    eventual_actual_velocity_error_small (1 / 10000) (by norm_num),
    eventual_actual_second_derivative] with m hsize herr hvelocity hsecond
  intro hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hη hmean hh hσ hz
  have hp := hfirst.self_of_nhds
  have hz0 := hz.self_of_nhds
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
  have ha := HessianAcceleration.centerAcceleration_halfPeriodic hm (θ x) (v x) σ (ξ x)
    η h (ξ' x) ξ'' (acceleration_sum_eq_zero hm σ hf hξ' hz)
  have hvel := hvelocity hm θ v ξ η h (ξ' x) x σ hp.1 hp.2.1 hp.2.2 hdom hroot hmean hh hσ hz
  have hacc := (hsecond hm θ v ξ ξ' η h ξ'' x σ hfirst hξ' hdom hroot hmean hh hσ hz).2
  have hacc' := hacc.trans (acceleration_bound (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _))
  have hgrad := domain_gradient_bound (by omega : 8 ≤ m) (θ x) (v x) σ (ξ x)
    hdom hσ hroot hz0 hsize.2.2.1 (by simpa only [chordError, Nat.cast_mul, Nat.cast_ofNat] using herr.1)
  have hroots : SignedPressureAngular.root (2 * m) = HessianReferencePotential.root (2 * m) := rfl
  rw [hroots] at hgrad
  have hrel := domain_relative_denominator (by omega : 8 ≤ m) (θ x) (v x) σ (ξ x)
    hdom hσ hroot hz0 hsize.2.2.1
  have hr (j : Fin (2 * m)) :
      ‖diameterVector (θ x) j - HessianReferencePotential.root (2 * m) j‖ ≤ phaseError (2 * m) := by
    have hb := (angularError_point (θ x) j).trans (domain_theta_coarse hm (θ x) (v x) hdom j)
    simpa only [angularError, SignedPressureAngular.root,
      HessianReferencePotential.root, phaseError, Nat.cast_mul, Nat.cast_ofNat] using hb
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
    (by change ∀ j, _ ≤ 600 * (logOrder (2 * m) : ℝ) * (1 + Real.log ((2 * m : ℕ) : ℝ))
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgrad)
    (by simpa only [chordError, Nat.cast_mul, Nat.cast_ofNat,
      SignedPressureAngular.root, HessianReferencePotential.root] using hrel)
    (by rw [velocityError_eq] at hvel
        change pairEnergy (by omega) (fun j => I * angularError (θ x) j * (η j : ℂ) +
          (centerVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x) j - h j)) ≤ _ at hvel
        exact hvel)
    (by simpa only [accelerationBound, Nat.cast_mul, Nat.cast_ofNat] using hacc')
  exact absorb_error (pairEnergy_nonneg _ _) (pairEnergy_nonneg _ _) herr.2 hb

end
end StructuralNote.CommonFiberHessian
