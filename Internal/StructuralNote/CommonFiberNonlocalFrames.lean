import StructuralNote.CommonFiberNonlocalProjection
import StructuralNote.CommonFiberSmallCoefficients

/-! The mean directions of actual consecutive diameter vectors. Their radial
center increments have the same absolute bound across the half-period seam. -/

namespace StructuralNote.CommonFiberNonlocalFrames

open Erdos1045 Erdos1045.EventualExact Complex LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry CommonFiberNonlocalProjection
open scoped BigOperators
noncomputable section

def meanFrame {n : ℕ} (hn : 0 < n) (θ : Fin n → ℝ) (j : Fin n) : ℂ :=
  frame n j * unit (angleAverage hn θ j)

theorem meanFrame_halfIndex {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) :
    meanFrame (by omega) θ (CommonClosureEnergy.halfIndex j) = unit (phase hm θ j) := by
  rw [meanFrame]
  have hf : frame (2 * m) (CommonClosureEnergy.halfIndex j) = unit (midpoint m j) := BoxLensLift.frame_halfIndex j
  rw [hf, ← unit_add]
  rfl

theorem angleAverage_halfTurn {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    angleAverage (by omega) θ (halfTurn hm j) = angleAverage (by omega) θ j := by
  have hh (j : Fin (2 * m)) : θ (halfTurn hm j) = θ j := Complex.ofReal_injective (hθ j)
  unfold angleAverage
  rw [← halfTurn_successor, hh, hh]

theorem meanFrame_halfTurn {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    meanFrame (by omega) θ (halfTurn hm j) = -meanFrame (by omega) θ j := by
  rw [meanFrame, frame_halfTurn, angleAverage_halfTurn hm θ hθ, neg_mul]
  rfl

theorem radial_increment (β L s t : ℝ) : radial (unit β) (LensClosure.increment β L s t) = s * Lens.width L t := by
  have hu : (starRingEnd ℂ) (unit β) * unit β = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unit]
    norm_num
  simp only [radial, LensClosure.increment, ← mul_assoc, hu, one_mul,
    Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

theorem radial_center_half {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) :
    radial (meanFrame (by omega) θ (CommonClosureEnergy.halfIndex j))
      (difference (by omega) (center hm θ v σ ξ) (CommonClosureEnergy.halfIndex j)) =
      σ j * Lens.width (2 * Real.cos (halfAngle hm θ j)) (heightParameter (coordinates hm v) ξ j) := by
  rw [meanFrame_halfIndex, center_half_difference hm θ v σ ξ hz]
  exact radial_increment _ _ _ _

theorem radial_center_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    {R : ℝ} (hR : ∀ j, |σ j * Lens.width (2 * Real.cos (halfAngle hm θ j))
      (heightParameter (coordinates hm v) ξ j)| ≤ R) (j : Fin (2 * m)) :
    |radial (meanFrame (by omega) θ j) (difference (by omega) (center hm θ v σ ξ) j)| ≤ R := by
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj]
    change |radial (meanFrame (by omega) θ (CommonClosureEnergy.halfIndex k))
      (difference (by omega) (center hm θ v σ ξ) (CommonClosureEnergy.halfIndex k))| ≤ R
    rw [radial_center_half hm θ v σ ξ hz]
    exact hR k
  · rw [hj, meanFrame_halfTurn hm θ hθ,
      difference_halfPeriodic hm _ (center_halfPeriodic hm θ v σ ξ hz)]
    simp only [radial, map_neg, neg_mul, Complex.neg_re, abs_neg]
    change |radial (meanFrame (by omega) θ (CommonClosureEnergy.halfIndex k))
      (difference (by omega) (center hm θ v σ ξ) (CommonClosureEnergy.halfIndex k))| ≤ R
    rw [radial_center_half hm θ v σ ξ hz]
    exact hR k

theorem center_step_bound {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    {B : ℝ} (hB : ∀ j, ‖fiberIncrement hm θ v σ ξ j‖ ≤ B) (j : Fin (2 * m)) :
    ‖difference (by omega) (center hm θ v σ ξ) j‖ ≤ B := by
  rw [center_difference hm θ v σ ξ hz]
  exact hB ⟨j.val % m, Nat.mod_lt _ hm⟩

end
end StructuralNote.CommonFiberNonlocalFrames
