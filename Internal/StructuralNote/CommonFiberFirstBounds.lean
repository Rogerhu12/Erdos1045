import StructuralNote.CommonFiberFirstDerivative

/-! The actual first center derivative minus its free tangential direction is
the integral of the small residual source and its forced closure correction. -/

namespace StructuralNote.CommonFiberFirstBounds

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open LensClosurePathDerivatives CommonClosureEnergy CommonTangentialParameters
open CommonFiberGeometry FiniteFourierLift BoxLensLift ClosedSourceIntegration
open CommonFiberFirstDerivative FourierMultiplier SchurSpectrum
open scoped BigOperators Topology
noncomputable section

theorem integral_sub {n : ℕ} (d e : Fin n → ℂ) : integral (d - e) = integral d - integral e := by
  funext j
  simp only [integral, synthesis, Pi.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.val = 0
  · simp [integralCoefficients, hp]
  · simp [integralCoefficients, hp, coefficient, Pi.sub_apply, sub_mul,
      Finset.sum_sub_distrib, sub_div]

def residual {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (j : Fin m) : ℂ :=
  velocity hm θ v σ ξ η h 0 j - halfIncrement (coordinates hm h) j

theorem velocity_sub_eq {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (ξ' : ℂ)
    (j : Fin m) :
    velocity hm θ v σ ξ η h ξ' j - halfIncrement (coordinates hm h) j =
      corrected (phase hm θ) σ (coordinates hm v) ξ ξ' (residual hm θ v σ ξ η h) j := by
  simp only [velocity, residual, corrected, heightParameter, map_zero, add_zero, velocity_split]
  ring

theorem centerVelocity_sub_representation {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (hh : ParameterSpace hm h) :
    centerVelocity hm θ v σ ξ η h ξ' - h =
      integrateCorrected hm (phase hm θ) σ (coordinates hm v) ξ ξ'
        (residual hm θ v σ ξ η h) := by
  have hh' : integral (repeatHalf hm (halfIncrement (coordinates hm h))) = h :=
    reconstruct_coordinates hm h hh
  calc
    _ = integral (repeatHalf hm (velocity hm θ v σ ξ η h ξ')) -
        integral (repeatHalf hm (halfIncrement (coordinates hm h))) :=
      congrArg (fun u => centerVelocity hm θ v σ ξ η h ξ' - u) hh'.symm
    _ = integral (repeatHalf hm (velocity hm θ v σ ξ η h ξ') -
        repeatHalf hm (halfIncrement (coordinates hm h))) := (integral_sub _ _).symm
    _ = _ := by
      congr 1
      funext j
      exact velocity_sub_eq hm θ v σ ξ η h ξ' ⟨j.val % m, Nat.mod_lt _ hm⟩

theorem residual_closure_eq {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (hh : ParameterSpace hm h)
    (hz : (∑ j, velocity hm θ v σ ξ η h ξ' j) = 0) :
    closureDerivative (phase hm θ) σ (coordinates hm v) ξ ξ' =
      -∑ j, residual hm θ v σ ξ η h j := by
  have hzero := (closed_iff_increment_sum _).mp (coordinates_closed hm h hh.1 hh.2.2)
  have hs : (∑ j, residual hm θ v σ ξ η h j) +
      closureDerivative (phase hm θ) σ (coordinates hm v) ξ ξ' = 0 := by
    calc
      _ = ∑ j, (velocity hm θ v σ ξ η h ξ' j - halfIncrement (coordinates hm h) j) := by
        simp_rw [velocity_sub_eq]
        simp only [corrected, Finset.sum_add_distrib, ← closureDerivative_apply_sum]
      _ = 0 := by rw [Finset.sum_sub_distrib, hz, hzero, sub_self]
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hs)

theorem centerVelocity_error_energy {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (hh : ParameterSpace (by omega) h)
    (hz : (∑ j, velocity (by omega) θ v σ ξ η h ξ' j) = 0) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) θ j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) v) ξ j| ≤ 1 / 4) :
    pairEnergy (by omega) (centerVelocity (by omega) θ v σ ξ η h ξ' - h) ≤
      65 / 8 * (2 * m : ℝ) ^ 3 * ∑ j, ‖residual (by omega) θ v σ ξ η h j‖ ^ 2 := by
  rw [centerVelocity_sub_representation (by omega) θ v σ ξ η h ξ' hh]
  exact integrateCorrected_energy hm _ _ _ _ _ _ hσ hsmall
    (residual_closure_eq (by omega) θ v σ ξ η h ξ' hh hz)

theorem actual_velocity_error_energy {m : ℕ} (hm : 2 ≤ m)
    {θ : ℝ → Fin (2 * m) → ℝ} {v : ℝ → Fin (2 * m) → ℂ} {ξ : ℝ → ℂ}
    {η : Fin (2 * m) → ℝ} {h : Fin (2 * m) → ℂ} {ξ' : ℂ} {x : ℝ} (σ : Fin m → ℝ)
    (hθ : ∀ j, HasDerivAt (fun s => θ s j) (η j) x)
    (hv : ∀ j, HasDerivAt (fun s => v s j) (h j) x) (hξ : HasDerivAt ξ ξ' x)
    (hh : ParameterSpace (by omega) h) (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |phase (by omega) (θ x) j - LensClosure.midpoint m j| +
      |heightParameter (coordinates (by omega) (v x)) (ξ x) j| ≤ 1 / 4)
    (hz : ∀ᶠ s in 𝓝 x, closure (phase (by omega) (θ s))
      (fun j => 2 * Real.cos (halfAngle (by omega) (θ s) j)) σ
        (coordinates (by omega) (v s)) (ξ s) = 0) :
    pairEnergy (by omega) (centerVelocity (by omega) (θ x) (v x) σ (ξ x) η h ξ' - h) ≤
      65 / 8 * (2 * m : ℝ) ^ 3 * ∑ j, ‖residual (by omega) (θ x) (v x) σ (ξ x) η h j‖ ^ 2 := by
  have ht (j : Fin m) : heightParameter (coordinates (by omega) (v x)) (ξ x) j ^ 2 < 4 := by
    have hhj := hsmall j
    have habs : |heightParameter (coordinates (by omega) (v x)) (ξ x) j| ≤ 1 / 4 := by
      linarith [abs_nonneg (phase (by omega) (θ x) j - LensClosure.midpoint m j)]
    nlinarith [(abs_le.mp habs).1, (abs_le.mp habs).2]
  exact centerVelocity_error_energy hm _ _ _ _ _ _ _ hh
    (velocity_sum_eq_zero (by omega) σ hθ hv hξ ht hz) hσ hsmall

theorem residual_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ) (h : Fin (2 * m) → ℂ) (j : Fin m)
    (hσ : |σ j| ≤ 1) (ht : |heightParameter (coordinates hm v) ξ j| ≤ 1) :
    ‖residual hm θ v σ ξ η h j‖ ≤
      |angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)| *
        ‖body (2 * Real.cos (halfAngle hm θ j)) (σ j) (heightParameter (coordinates hm v) ξ j)‖ +
      |Real.sin (halfAngle hm θ j)| * |angleDifference (by omega) η (CommonClosureEnergy.halfIndex j)| +
      |coordinates hm h j| * (|phase hm θ j - LensClosure.midpoint m j| +
        |heightParameter (coordinates hm v) ξ j|) := by
  have he : residual hm θ v σ ξ η h j =
      incrementVelocity (phase hm θ j) (2 * Real.cos (halfAngle hm θ j)) (σ j)
        (heightParameter (coordinates hm v) ξ j)
        (angleAverage (by omega) η (CommonClosureEnergy.halfIndex j))
        (-Real.sin (halfAngle hm θ j) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j))
        (coordinates hm h j) - (coordinates hm h j : ℂ) * (unit (LensClosure.midpoint m j) * I) := by
    simp only [residual, velocity, heightParameter, map_zero, add_zero, halfIncrement]
    ring
  rw [he]
  simpa only [abs_mul, abs_neg] using velocity_residual_bound
    (α := phase hm θ j) (μ := LensClosure.midpoint m j)
    (L := 2 * Real.cos (halfAngle hm θ j))
    (a := angleAverage (by omega) η (CommonClosureEnergy.halfIndex j))
    (l := -Real.sin (halfAngle hm θ j) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j))
    (u := coordinates hm h j) hσ ht

end
end StructuralNote.CommonFiberFirstBounds
