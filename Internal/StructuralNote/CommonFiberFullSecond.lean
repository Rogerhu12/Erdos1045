import StructuralNote.CommonFiberSecondEstimate
import StructuralNote.LogDiscriminantHessian

/-! Equation (9.14) for the actual fiber configuration. Both the angular
acceleration and the implicit closure acceleration enter the derivative. -/

namespace StructuralNote.CommonFiberFullSecond

open Erdos1045 Erdos1045.EventualExact Complex Filter LensClosure LensIncrementDerivatives
open CommonFiberGeometry CommonFiberFirstDerivative CommonFiberSecondDerivative
open CommonTangentialParameters LogDiscriminantSecondDerivative LogDiscriminantHessian
open scoped BigOperators Topology
noncomputable section

def fullVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (j : Fin (2 * m)) : ℂ :=
  I * diameterVector θ j * (η j : ℂ) + centerVelocity hm θ v σ ξ η h ξ' j

def fullAcceleration {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' ξ'' : ℂ)
    (j : Fin (2 * m)) : ℂ :=
  -diameterVector θ j * (η j : ℂ) ^ 2 + centerAcceleration hm θ v σ ξ η h ξ' ξ'' j

theorem fullVelocity_hasDerivAt {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ ξ' : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ'' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ (ξ' x) x)
    (hξ' : HasDerivAt ξ' ξ'' x)
    (ht : ∀ j, heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4) (j : Fin (2 * m)) :
    HasDerivAt (fun s => fullVelocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j)
      (fullAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j) x := by
  have hd := ((((unit_path_hasDerivAt (hθ j)).const_mul
    (FourierMultiplier.character (2 * m) 1 j)).const_mul I).mul_const (η j : ℂ)).add
      (centerVelocity_hasDerivAt hm σ hθ hv hξ hξ' ht j)
  change HasDerivAt (fun s => fullVelocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j) _ x at hd
  apply hd.congr_deriv
  unfold fullAcceleration diameterVector
  ring_nf
  simp only [I_sq]
  ring

theorem actual_log_second_derivative {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ ξ' : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ'' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hfirst : ∀ᶠ s in 𝓝 x,
      (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s ∧
      (∀ j, heightParameter (coordinates hm (v s)) (ξ s) j ^ 2 < 4))
    (hξ' : HasDerivAt ξ' ξ'' x)
    (hi : Function.Injective (configuration hm (θ x) (v x) σ (ξ x))) :
    HasDerivAt (deriv (fun s => Real.log (Configuration.discriminant
      (configuration hm (θ s) (v s) σ (ξ s)))))
      (quadratic (configuration hm (θ x) (v x) σ (ξ x))
        (fullVelocity hm (θ x) (v x) σ (ξ x) η h (ξ' x)) +
      accelerationPairing (configuration hm (θ x) (v x) σ (ξ x))
        (fullAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'')) x := by
  have hp := hfirst.self_of_nhds
  have hv := fullVelocity_hasDerivAt hm σ hp.1 hp.2.1 hp.2.2.1 hξ' hp.2.2.2
  have hz : ∀ᶠ s in 𝓝 x, ∀ j,
      HasDerivAt (fun r => configuration hm (θ r) (v r) σ (ξ r) j)
        (fullVelocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j) s := by
    filter_upwards [hfirst] with s hs
    exact configuration_hasDerivAt hm σ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  simpa only [second_eq_quadratic_add_acceleration] using log_second_derivative hz hv hi

end
end StructuralNote.CommonFiberFullSecond
