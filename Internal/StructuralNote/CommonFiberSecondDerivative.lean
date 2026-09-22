import StructuralNote.CommonFiberFirstBounds
import StructuralNote.LensClosureAcceleration

/-! Actual second derivatives along straight angle/tangential parameter lines.
The implicit closure acceleration remains present throughout reconstruction. -/

namespace StructuralNote.CommonFiberSecondDerivative

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open LensClosurePathDerivatives CommonClosureEnergy CommonTangentialParameters
open CommonFiberGeometry CommonFiberFirstDerivative FiniteFourierLift BoxLensLift
open ClosedSourceIntegration Filter
open scoped BigOperators Topology
noncomputable section

def acceleration {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    (ξ' ξ'' : ℂ) (j : Fin m) : ℂ :=
  incrementAcceleration (phase hm θ j) (2 * Real.cos (halfAngle hm θ j)) (σ j)
    (heightParameter (coordinates hm v) ξ j)
    (angleAverage (by omega) η (CommonClosureEnergy.halfIndex j))
    (-Real.sin (halfAngle hm θ j) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j))
    (heightParameter (coordinates hm h) ξ' j) 0
    (-Real.cos (halfAngle hm θ j) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2 / 2)
    (harmonicFunctional (LensClosure.midpoint m j) ξ'')

def centerAcceleration {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' ξ'' : ℂ) :
    Fin (2 * m) → ℂ := integral (repeatHalf hm (acceleration hm θ v σ ξ η h ξ' ξ''))

theorem length_velocity_hasDerivAt {m : ℕ} (hm : 0 < m) {θ : ℝ → Fin (2 * m) → ℝ}
    {η : Fin (2 * m) → ℝ} {x : ℝ}
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x) (j : Fin m) :
    HasDerivAt (fun s => -Real.sin (halfAngle hm (θ s) j) *
      angleDifference (by omega) η (CommonClosureEnergy.halfIndex j))
      (-Real.cos (halfAngle hm (θ x) j) *
        angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2 / 2) x := by
  apply (((halfAngle_hasDerivAt hm hθ j).sin.neg).mul_const
    (angleDifference (by omega) η (CommonClosureEnergy.halfIndex j))).congr_deriv
  ring

theorem velocity_hasDerivAt {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ ξ' : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ'' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ (ξ' x) x)
    (hξ' : HasDerivAt ξ' ξ'' x)
    (ht : ∀ j, heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4) (j : Fin m) :
    HasDerivAt (fun s => velocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j)
      (acceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j) x := by
  have hh : HasDerivAt (fun s => heightParameter (coordinates hm h) (ξ' s) j)
      (harmonicFunctional (LensClosure.midpoint m j) ξ'') x :=
    ((harmonicFunctional (LensClosure.midpoint m j)).hasFDerivAt.comp_hasDerivAt x hξ').const_add _
  exact incrementVelocity_hasDerivAt (σ j) (phase_hasDerivAt hm hθ j) (length_hasDerivAt hm hθ j)
    (heightParameter_hasDerivAt (coordinates_hasDerivAt hm hv) hξ j)
    (hasDerivAt_const x _) (length_velocity_hasDerivAt hm hθ j) hh rfl rfl rfl (ht j)

theorem centerVelocity_hasDerivAt {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ ξ' : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ'' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ (ξ' x) x)
    (hξ' : HasDerivAt ξ' ξ'' x)
    (ht : ∀ j, heightParameter (coordinates hm (v x)) (ξ x) j ^ 2 < 4) (j : Fin (2 * m)) :
    HasDerivAt (fun s => centerVelocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j)
      (centerAcceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j) x :=
  integral_hasDerivAt (repeatHalf_hasDerivAt hm (velocity_hasDerivAt hm σ hθ hv hξ hξ' ht)) j

theorem acceleration_split_eq {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ)
    (ξ' ξ'' : ℂ) (j : Fin m) :
    acceleration hm θ v σ ξ η h ξ' ξ'' j =
      corrected (phase hm θ) σ (coordinates hm v) ξ ξ'' (acceleration hm θ v σ ξ η h ξ' 0) j := by
  unfold acceleration corrected
  simp only [map_zero]
  have hh := acceleration_split (phase hm θ j) (2 * Real.cos (halfAngle hm θ j)) (σ j)
    (heightParameter (coordinates hm v) ξ j)
    (angleAverage (by omega) η (CommonClosureEnergy.halfIndex j))
    (-Real.sin (halfAngle hm θ j) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j))
    (heightParameter (coordinates hm h) ξ' j) 0
    (-Real.cos (halfAngle hm θ j) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2 / 2)
    0 (harmonicFunctional (LensClosure.midpoint m j) ξ'')
  simpa only [zero_add] using hh

theorem centerAcceleration_source_bound {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' ξ'' : ℂ) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / 4)
    (hz : (∑ j, acceleration (by omega) θ v σ ξ η h ξ' ξ'' j) = 0) :
    (∑ j, ‖centerAcceleration (by omega) θ v σ ξ η h ξ' ξ'' j‖) ≤
      36 * (2 * m : ℝ) * ∑ j, ‖acceleration (by omega) θ v σ ξ η h ξ' 0 j‖ := by
  have heq : closureDerivative (phase (by omega) θ) σ (coordinates (by omega) v) ξ ξ'' =
      -∑ j, acceleration (by omega) θ v σ ξ η h ξ' 0 j := by
    simp_rw [acceleration_split_eq] at hz
    simp only [corrected, Finset.sum_add_distrib, ← closureDerivative_apply_sum] at hz
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hz)
  have hb := integrateCorrected_l1 hm (phase (by omega) θ) σ (coordinates (by omega) v) ξ ξ''
    (acceleration (by omega) θ v σ ξ η h ξ' 0) hσ hsmall heq
  have hc : centerAcceleration (by omega) θ v σ ξ η h ξ' ξ'' =
      integrateCorrected (by omega) (phase (by omega) θ) σ (coordinates (by omega) v) ξ ξ''
        (acceleration (by omega) θ v σ ξ η h ξ' 0) := by
    unfold centerAcceleration integrateCorrected
    congr 2
    funext j
    exact acceleration_split_eq (by omega) θ v σ ξ η h ξ' ξ'' j
  rw [hc]
  exact hb

/-- Differentiating actual closure twice removes any independent acceleration
balance assumption. The angle and tangential directions are constant. -/
theorem acceleration_sum_eq_zero {m : ℕ} (hm : 0 < m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ ξ' : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ'' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hfirst : ∀ᶠ s in 𝓝 x,
      (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s ∧
      (∀ j, heightParameter (coordinates hm (v s)) (ξ s) j ^ 2 < 4))
    (hξ' : HasDerivAt ξ' ξ'' x)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase hm (θ s))
      (fun j => 2 * Real.cos (halfAngle hm (θ s) j)) σ (coordinates hm (v s)) (ξ s) = 0) :
    (∑ j, acceleration hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j) = 0 := by
  have hp := hfirst.self_of_nhds
  have hvzero : ∀ᶠ s in 𝓝 x, (∑ j, velocity hm (θ s) (v s) σ (ξ s) η h (ξ' s) j) = 0 := by
    filter_upwards [hfirst, hz.eventually_nhds] with s hs hzs
    exact velocity_sum_eq_zero hm σ hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hzs
  have hd := HasDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    velocity_hasDerivAt hm σ hp.1 hp.2.1 hp.2.2.1 hξ' hp.2.2.2 j)
  exact hd.unique ((hasDerivAt_const x (0 : ℂ)).congr_of_eventuallyEq hvzero)

theorem actual_centerAcceleration_source_bound {m : ℕ} (hm : 2 ≤ m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ ξ' : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ'' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hfirst : ∀ᶠ s in 𝓝 x,
      (∀ j, HasDerivAt (fun r => θ r j) (η j) s) ∧
      (∀ j, HasDerivAt (fun r => v r j) (h j) s) ∧ HasDerivAt ξ (ξ' s) s ∧
      (∀ j, heightParameter (coordinates (by omega) (v s)) (ξ s) j ^ 2 < 4))
    (hξ' : HasDerivAt ξ' ξ'' x) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) (θ x) j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) (v x)) (ξ x) j| ≤ 1 / 4)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase (by omega) (θ s))
      (fun j => 2 * Real.cos (halfAngle (by omega) (θ s) j))
      σ (coordinates (by omega) (v s)) (ξ s) = 0) :
    (∀ j, HasDerivAt (fun s => centerVelocity (by omega) (θ s) (v s) σ (ξ s) η h (ξ' s) j)
      (centerAcceleration (by omega) (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j) x) ∧
    (∑ j, ‖centerAcceleration (by omega) (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' j‖) ≤
      36 * (2 * m : ℝ) * ∑ j, ‖acceleration (by omega) (θ x) (v x) σ (ξ x) η h (ξ' x) 0 j‖ := by
  have hp := hfirst.self_of_nhds
  exact ⟨centerVelocity_hasDerivAt (by omega) σ hp.1 hp.2.1 hp.2.2.1 hξ' hp.2.2.2,
    centerAcceleration_source_bound hm (θ x) (v x) σ (ξ x) η h (ξ' x) ξ'' hσ hsmall
      (acceleration_sum_eq_zero (by omega) σ hfirst hξ' hz)⟩

end
end StructuralNote.CommonFiberSecondDerivative
