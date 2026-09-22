import StructuralNote.CommonFiberSecondDerivative
import StructuralNote.LensAccelerationBounds
import StructuralNote.CommonFiberHeightEstimate

/-! Quadratic and mixed terms in the direct acceleration source of the actual
common fiber. The second closure correction is treated by source integration. -/

namespace StructuralNote.CommonFiberAccelerationSource

open Erdos1045.EventualExact Complex LensClosure LensIncrementDerivatives
open CommonClosureEnergy CommonTangentialParameters CommonFiberFirstDerivative
open CommonFiberSecondDerivative LensAccelerationBounds
open scoped BigOperators
noncomputable section

theorem source_point_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) (j : Fin m) {B S : ℝ}
    (hS : 0 ≤ S) (hσ : |σ j| ≤ 1) (ht : |heightParameter (coordinates hm v) ξ j| ≤ 1)
    (hb : ‖body (2 * Real.cos (halfAngle hm θ j)) (σ j)
      (heightParameter (coordinates hm v) ξ j)‖ ≤ B)
    (hs : |Real.sin (halfAngle hm θ j)| ≤ S) :
    ‖acceleration hm θ v σ ξ η h ξ' 0 j‖ ≤
      (B + S) * angleAverage (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2 +
      (S + 1) * angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2 +
      4 * |angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)| *
        |heightParameter (coordinates hm h) ξ' j| +
      4 * heightParameter (coordinates hm h) ξ' j ^ 2 := by
  let a := angleAverage (by omega : 0 < 2 * m) η (CommonClosureEnergy.halfIndex j)
  let d := angleDifference (by omega : 0 < 2 * m) η (CommonClosureEnergy.halfIndex j)
  let u := heightParameter (coordinates hm h) ξ' j
  have hl : |-Real.sin (halfAngle hm θ j) * d| ≤ S * |d| := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right hs (abs_nonneg d)
  have hll : |-Real.cos (halfAngle hm θ j) * d ^ 2 / 2| ≤ d ^ 2 := by
    rw [abs_div, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg d),
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one (halfAngle hm θ j)) (sq_nonneg d)
    nlinarith [sq_nonneg d]
  have hcross : 2 * |a| * (S * |d|) ≤ S * (a ^ 2 + d ^ 2) := by
    have hh := mul_nonneg hS (sq_nonneg (|a| - |d|))
    nlinarith [sq_abs a, sq_abs d]
  have hB := mul_le_mul_of_nonneg_left hb (sq_nonneg a)
  have hL := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * |a| by positivity)
  have hh := increment_source_bound (α := phase hm θ j)
    (L := 2 * Real.cos (halfAngle hm θ j)) (a := a)
    (l := -Real.sin (halfAngle hm θ j) * d) (u := u)
    (ll := -Real.cos (halfAngle hm θ j) * d ^ 2 / 2) hσ ht
  change ‖acceleration hm θ v σ ξ η h ξ' 0 j‖ ≤
    (B + S) * a ^ 2 + (S + 1) * d ^ 2 + 4 * |a| * |u| + 4 * u ^ 2
  have he : acceleration hm θ v σ ξ η h ξ' 0 j =
      incrementAcceleration (phase hm θ j) (2 * Real.cos (halfAngle hm θ j)) (σ j)
        (heightParameter (coordinates hm v) ξ j) a
        (-Real.sin (halfAngle hm θ j) * d) u 0
        (-Real.cos (halfAngle hm θ j) * d ^ 2 / 2) 0 := by
    simp only [acceleration, map_zero, a, d, u]
  rw [he]
  nlinarith only [hh, hB, hL, hll, hcross]

theorem source_sum_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (η : Fin (2 * m) → ℝ)
    (h : Fin (2 * m) → ℂ) (ξ' : ℂ) {B S : ℝ}
    (hS : 0 ≤ S) (hσ : ∀ j, |σ j| ≤ 1)
    (ht : ∀ j, |heightParameter (coordinates hm v) ξ j| ≤ 1)
    (hb : ∀ j, ‖body (2 * Real.cos (halfAngle hm θ j)) (σ j)
      (heightParameter (coordinates hm v) ξ j)‖ ≤ B)
    (hs : ∀ j, |Real.sin (halfAngle hm θ j)| ≤ S) :
    (∑ j, ‖acceleration hm θ v σ ξ η h ξ' 0 j‖) ≤
      (B + S) * (∑ j : Fin m, angleAverage (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2) +
      (S + 1) * (∑ j : Fin m, angleDifference (by omega) η (CommonClosureEnergy.halfIndex j) ^ 2) +
      4 * (∑ j : Fin m, |angleAverage (by omega) η (CommonClosureEnergy.halfIndex j)| *
        |heightParameter (coordinates hm h) ξ' j|) +
      4 * ∑ j, heightParameter (coordinates hm h) ξ' j ^ 2 := by
  have hh := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
    source_point_bound hm θ v σ ξ η h ξ' j hS (hσ j) (ht j) (hb j) (hs j))
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc] using hh

end
end StructuralNote.CommonFiberAccelerationSource
