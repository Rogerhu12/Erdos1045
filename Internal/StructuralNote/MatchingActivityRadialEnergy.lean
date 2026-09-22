import StructuralNote.MatchingActivityRadialSource

/-! A coarse cubic energy bound for the genuine radial center velocity.
Together with the strong budget it gives an o(n) error, which suffices for
radial monotonicity without a sharp logarithmic variation estimate. -/

namespace StructuralNote.MatchingActivityRadialEnergy

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry MatchingActivityRadialClosure MatchingActivityRadialPair
open MatchingActivityRadialBounds MatchingActivityRadialVelocity MatchingActivityRadialFeasible
open MatchingActivityRadialSource LensIncrementDerivatives LensClosurePathDerivatives ClosedSourceIntegration
open scoped BigOperators
noncomputable section

theorem centerVelocity_energy_bound {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (i : Fin m)
    (hchart : IsFeasibleRadialChart (by omega) θ σ ν r a g)
    (hpos : ∀ j, 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ j, |r j| ≤ 1) (hφ : ∀ j, |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hb : ∀ j, ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1) :
    pairEnergy (by omega) (centerVelocity (by omega) θ σ ν r g i) ≤ 130 * (2 * m : ℝ) ^ 3 := by
  have hp (j : Fin m) : 0 < (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re := lt_of_lt_of_le (by norm_num) (hpos j)
  have hν (j : Fin m) : |ν j| ≤ 1 / 4 := by linarith [hsmall j, abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
  have ht (j : Fin m) : ν j ^ 2 < 4 := by nlinarith [(abs_le.mp (hν j)).1, (abs_le.mp (hν j)).2]
  have he := actual_closure_derivative (by omega) θ σ ν r a g i hchart hp ht
  have hs := directSource_sum_bound hm θ σ ν r i hpos hr hφ hchart.1 (fun j => (hν j).trans (by norm_num)) hb
  have hsmall' (j : Fin m) : |radialPhase (by omega) θ r j - midpoint m j| + |heightParameter ν 0 j| ≤ 1 / 4 := by
    simpa only [heightParameter, map_zero, add_zero] using hsmall j
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
    (f := fun j => ‖directSource (by omega) θ σ ν r i j‖) (fun j _ => norm_nonneg _)
  have hsum0 : 0 ≤ ∑ j, ‖directSource (by omega) θ σ ν r i j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hsq' : (∑ j, ‖directSource (by omega) θ σ ν r i j‖ ^ 2) ≤ 16 := by nlinarith
  have hE := integrateCorrected_energy hm _ _ _ _ _ _ hchart.1 hsmall' he
  change pairEnergy (by omega) (centerVelocity (by omega) θ σ ν r g i) ≤ _ at hE
  calc
    _ ≤ 65 / 8 * (2 * m : ℝ) ^ 3 * ∑ j, ‖directSource (by omega) θ σ ν r i j‖ ^ 2 := hE
    _ ≤ 65 / 8 * (2 * m : ℝ) ^ 3 * 16 := mul_le_mul_of_nonneg_left hsq' (by positivity)
    _ = _ := by ring

end
end StructuralNote.MatchingActivityRadialEnergy
