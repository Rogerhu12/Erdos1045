import StructuralNote.MatchingActivityRadialProjection

/-! The direct source of a single radial variation has exactly two possible
nonzero entries, so the closure correction has order 1/m. -/

namespace StructuralNote.MatchingActivityRadialSourceSharp

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry MatchingActivityRadialClosure MatchingActivityRadialPair
open MatchingActivityRadialSource MatchingActivityRadialBounds MatchingActivityRadialVelocity MatchingActivityRadialFeasible
open LensIncrementDerivatives LensClosurePathDerivatives ClosedSourceIntegration
open scoped BigOperators
noncomputable section

theorem directSource_point_sharp {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (i j : Fin m)
    (hpos : 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ k, |r k| ≤ 1) (hφ : |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hσ : |σ j| ≤ 1) (hν : |ν j| ≤ 1)
    (hb : ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1 / 4) :
    ‖directSource (by omega) θ σ ν r i j‖ ≤ (9 / 8) * (radiusVelocity i j + radiusVelocity i (nextIndex (by omega) j)) := by
  have hd := individual_derivative_bounds hpos (hr j) (hr (nextIndex (by omega) j))
  dsimp only [pair] at hd
  have hvel := velocity_residual_bound (α := radialPhase (by omega) θ r j)
    (μ := midpoint m j) (L := radialLength (by omega) θ r j) (a := phaseVelocity (by omega) θ r i j)
    (l := lengthVelocity (by omega) θ r i j) (u := 0) hσ hν
  simp only [ofReal_zero, zero_mul, sub_zero, abs_zero, add_zero] at hvel
  by_cases hj : j = i
  · have hn : nextIndex (by omega) j ≠ i := by simpa only [← hj] using nextIndex_ne hm j
    have hα : |phaseVelocity (by omega) θ r i j| ≤ 1 / 2 := by
      simp only [phaseVelocity, pairVelocity, radiusVelocity, if_pos hj, if_neg hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero]
      linarith [hd.2.2.1]
    have hL : |lengthVelocity (by omega) θ r i j| ≤ 1 := by
      simpa only [lengthVelocity, radialLength, pairVelocity, radiusVelocity, if_pos hj, if_neg hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, add_zero] using hd.1
    change ‖directSource (by omega) θ σ ν r i j‖ ≤ _ at hvel
    simp only [radiusVelocity, if_pos hj, if_neg hn, add_zero, mul_one]
    nlinarith [norm_nonneg (body (radialLength (by omega) θ r j) (σ j) (ν j))]
  · by_cases hn : nextIndex (by omega) j = i
    · have hα : |phaseVelocity (by omega) θ r i j| ≤ 1 / 2 := by
        simp only [phaseVelocity, pairVelocity, radiusVelocity, if_neg hj, if_pos hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, zero_add]
        linarith [hd.2.2.2]
      have hL : |lengthVelocity (by omega) θ r i j| ≤ 1 := by
        simpa only [lengthVelocity, radialLength, pairVelocity, radiusVelocity, if_neg hj, if_pos hn, pair, ofReal_one, one_mul, ofReal_zero, zero_mul, zero_add] using hd.2.1
      change ‖directSource (by omega) θ σ ν r i j‖ ≤ _ at hvel
      simp only [radiusVelocity, if_neg hj, if_pos hn, zero_add, mul_one]
      nlinarith [norm_nonneg (body (radialLength (by omega) θ r j) (σ j) (ν j))]
    · rw [directSource_zero (by omega) θ σ ν r i j hj hn]
      simp only [norm_zero, radiusVelocity, if_neg hj, if_neg hn, add_zero, mul_zero, le_refl]

theorem directSource_sum_sharp {m : ℕ} (hm : 2 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (i : Fin m)
    (hpos : ∀ j, 1 ≤ (pair (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))).re)
    (hr : ∀ k, |r k| ≤ 1) (hφ : ∀ j, |halfAngle (by omega) θ j| ≤ 1 / 4)
    (hσ : ∀ j, |σ j| ≤ 1) (hν : ∀ j, |ν j| ≤ 1)
    (hb : ∀ j, ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1 / 4) :
    (∑ j, ‖directSource (by omega) θ σ ν r i j‖) ≤ 9 / 4 := by
  have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => directSource_point_sharp hm θ σ ν r i j
    (hpos j) hr (hφ j) (hσ j) (hν j) (hb j))
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib, nextIndex_sum hm, radiusVelocity_sum,
    show (9 / 8 : ℝ) * (1 + 1) = 9 / 4 by norm_num] using he


end
end StructuralNote.MatchingActivityRadialSourceSharp
