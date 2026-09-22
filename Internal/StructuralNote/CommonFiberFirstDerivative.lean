import StructuralNote.ClosedSourceIntegration

/-! First derivatives in the actual angle and tangential coordinates, followed
through the closure correction and mean-zero discrete integration. -/

namespace StructuralNote.CommonFiberFirstDerivative

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open LensClosurePathDerivatives CommonClosureEnergy CommonTangentialParameters
open CommonFiberGeometry FiniteFourierLift BoxLensLift ClosedSourceIntegration
open scoped BigOperators Topology
noncomputable section

theorem phase_hasDerivAt {m : ℕ} (hm : 0 < m) {θ : ℝ → Fin (2 * m) → ℝ}
    {η : Fin (2 * m) → ℝ} {x : ℝ}
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x) (j : Fin m) :
    HasDerivAt (fun s => phase hm (θ s) j)
      (angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)) x := by
  exact (((hθ _).add (hθ _)).div_const 2).const_add (LensClosure.midpoint m j)

theorem halfAngle_hasDerivAt {m : ℕ} (hm : 0 < m) {θ : ℝ → Fin (2 * m) → ℝ}
    {η : Fin (2 * m) → ℝ} {x : ℝ}
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x) (j : Fin m) :
    HasDerivAt (fun s => halfAngle hm (θ s) j)
      (angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) / 2) x := by
  exact (((hθ _).sub (hθ _)).div_const 2).const_add (Real.pi / (2 * m))

theorem coordinates_hasDerivAt {m : ℕ} (hm : 0 < m) {v : ℝ → Fin (2 * m) → ℂ}
    {h : Fin (2 * m) → ℂ} {x : ℝ}
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (j : Fin m) :
    HasDerivAt (fun s => coordinates hm (v s) j) (coordinates hm h j) x := by
  have hd := ((hv (successor (by omega) (BoxLensLift.halfIndex j))).sub
    (hv (BoxLensLift.halfIndex j))).const_mul ((starRingEnd ℂ) (unit (LensClosure.midpoint m j)))
  exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hd

theorem length_hasDerivAt {m : ℕ} (hm : 0 < m) {θ : ℝ → Fin (2 * m) → ℝ}
    {η : Fin (2 * m) → ℝ} {x : ℝ}
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x) (j : Fin m) :
    HasDerivAt (fun s => 2 * Real.cos (halfAngle hm (θ s) j))
      (-Real.sin (halfAngle hm (θ x) j) *
        angleDifference (by omega) η (CommonClosureEnergy.halfIndex j)) x := by
  apply (((halfAngle_hasDerivAt hm hθ j).cos).const_mul 2).congr_deriv
  ring

def velocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (j : Fin m) : ℂ :=
  incrementVelocity (phase hm θ j) (2 * Real.cos (halfAngle hm θ j)) (σ j)
    (heightParameter (coordinates hm v) ξ j)
    (angleAverage (by omega) η (CommonClosureEnergy.halfIndex j))
    (-Real.sin (halfAngle hm θ j) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j))
    (heightParameter (coordinates hm h) ξ' j)

def centerVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ) :
    Fin (2 * m) → ℂ :=
  integral (repeatHalf hm (velocity hm θ v σ ξ η h ξ'))

theorem fiberIncrement_hasDerivAt {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ ξ' x)
    (ht : ∀ j, heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4) (j : Fin m) :
    HasDerivAt (fun s => fiberIncrement hm (θ s) (v s) σ (ξ s) j)
      (velocity hm (θ x) (v x) σ (ξ x) η h ξ' j) x :=
  LensIncrementDerivatives.increment_hasDerivAt (σ j) (phase_hasDerivAt hm hθ j)
    (length_hasDerivAt hm hθ j)
    (heightParameter_hasDerivAt (coordinates_hasDerivAt hm hv) hξ j) (ht j)

theorem center_hasDerivAt {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ ξ' x)
    (ht : ∀ j, heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4) (j : Fin (2 * m)) :
    HasDerivAt (fun s => center hm (θ s) (v s) σ (ξ s) j)
      (centerVelocity hm (θ x) (v x) σ (ξ x) η h ξ' j) x :=
  integral_hasDerivAt
    (repeatHalf_hasDerivAt hm (fiberIncrement_hasDerivAt hm σ hθ hv hξ ht)) j

theorem configuration_hasDerivAt {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ ξ' x)
    (ht : ∀ j, heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4) (j : Fin (2 * m)) :
    HasDerivAt (fun s => configuration hm (θ s) (v s) σ (ξ s) j)
      (I * diameterVector (θ x) j * (η j : ℂ) +
        centerVelocity hm (θ x) (v x) σ (ξ x) η h ξ' j) x := by
  have hd := ((unit_path_hasDerivAt (hθ j)).const_mul (FourierMultiplier.character (2 * m) 1 j)).add
    (center_hasDerivAt hm σ hθ hv hξ ht j)
  change HasDerivAt (fun s => configuration hm (θ s) (v s) σ (ξ s) j) _ x at hd
  apply hd.congr_deriv
  unfold diameterVector
  ring

theorem velocity_sum_eq_zero {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ ξ' x)
    (ht : ∀ j, heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ (coordinates hm (v s)) (ξ s) = 0) :
    (∑ j, velocity hm (θ x) (v x) σ (ξ x) η h ξ' j) = 0 := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => fiberIncrement_hasDerivAt hm σ hθ hv hξ ht j)
  have hc : HasDerivAt (fun s => ∑ j, fiberIncrement hm (θ s) (v s) σ (ξ s) j) 0 x :=
    (hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hz
  exact hd.unique hc

end
end StructuralNote.CommonFiberFirstDerivative
