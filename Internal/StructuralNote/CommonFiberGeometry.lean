import StructuralNote.CommonDomainClosure
import StructuralNote.CommonTangentialReconstruction
import StructuralNote.RationalChart

/-! The actual configurations associated with common continuous parameters and
a closure root. Matching distances and the adjacent crossing formulas are exact. -/

namespace StructuralNote.CommonFiberGeometry

open Erdos1045 Erdos1045.EventualExact Complex
open FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum LensClosure
open CommonTangentialParameters CommonClosureEnergy
open scoped BigOperators
noncomputable section

def fiberIncrement {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin m) : ℂ :=
  LensClosure.increment (phase hm θ j) (2 * Real.cos (halfAngle hm θ j)) (σ j)
    (heightParameter (coordinates hm v) ξ j)

def center {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) : Fin (2 * m) → ℂ :=
  integral (BoxLensLift.repeatHalf hm (fiberIncrement hm θ v σ ξ))

def diameterVector {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) : ℂ :=
  character n 1 j * unit (θ j)

def configuration {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) (j : Fin (2 * m)) : ℂ :=
  diameterVector θ j + center hm θ v σ ξ j

theorem center_mean_zero {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ) :
    (∑ j, center hm θ v σ ξ j) = 0 := integral_mean_zero (by omega) _

theorem center_difference {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0) :
    difference (by omega) (center hm θ v σ ξ) = BoxLensLift.repeatHalf hm (fiberIncrement hm θ v σ ξ) := by
  apply difference_integral
  rw [BoxLensLift.repeatHalf_sum]
  change (2 : ℂ) * closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0
  rw [hz, mul_zero]

theorem center_half_difference {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) :
    difference (by omega) (center hm θ v σ ξ) (CommonClosureEnergy.halfIndex j) = fiberIncrement hm θ v σ ξ j := by
  rw [center_difference hm θ v σ ξ hz]
  exact repeatHalf_halfIndex hm _ j

theorem center_halfPeriodic {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0) :
    HalfPeriodic hm (center hm θ v σ ξ) := by
  have he : (fun j => center hm θ v σ ξ (halfTurn hm j)) = center hm θ v σ ξ := by
    apply integral_unique (by omega)
    · have hs := Equiv.sum_comp (Equiv.ofBijective (halfTurn hm) (halfTurn_involutive hm).bijective)
        (center hm θ v σ ξ)
      exact hs.trans (center_mean_zero hm θ v σ ξ)
    · funext k
      change center hm θ v σ ξ (halfTurn hm (successor _ k)) - center hm θ v σ ξ (halfTurn hm k) = _
      rw [halfTurn_successor]
      change difference (by omega) (center hm θ v σ ξ) (halfTurn hm k) = _
      rw [center_difference hm θ v σ ξ hz]
      exact BoxLensLift.repeatHalf_halfTurn hm _ k
  exact fun j => congrFun he j

theorem diameterVector_norm {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) : ‖diameterVector θ j‖ = 1 := by
  simp [diameterVector, character, norm_pow, ClosedFourier.root_norm]

theorem diameterVector_halfTurn {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (j : Fin (2 * m)) :
    diameterVector θ (halfTurn hm j) = -diameterVector θ j := by
  have ht : θ (halfTurn hm j) = θ j := Complex.ofReal_injective (hθ j)
  rw [diameterVector, character_halfTurn hm (by decide : Odd 1), ht, neg_mul]
  rfl

theorem matching_length {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin (2 * m)) : ‖configuration hm θ v σ ξ j - configuration hm θ v σ ξ (halfTurn hm j)‖ = 2 := by
  have he : configuration hm θ v σ ξ j - configuration hm θ v σ ξ (halfTurn hm j) =
      2 * diameterVector θ j := by
    simp only [configuration, diameterVector_halfTurn hm θ hθ, center_halfPeriodic hm θ v σ ξ hz j]
    ring
  rw [he, norm_mul, diameterVector_norm]
  norm_num

theorem unit_add (x y : ℝ) : unit (x + y) = unit x * unit y := by
  unfold unit
  rw [Complex.ofReal_add, add_mul, Complex.exp_add]

theorem unit_pair (a b : ℝ) : unit (a - b) + unit (a + b) = unit a * (2 * Real.cos b : ℝ) := by
  have he : unit (-b) + unit b = ((2 * Real.cos b : ℝ) : ℂ) := by
    apply Complex.ext
    · simpa only [Complex.add_re, unit_re, Complex.ofReal_re, Real.cos_neg] using (two_mul (Real.cos b)).symm
    · simp only [Complex.add_im, unit_im, Complex.ofReal_im, Real.sin_neg, neg_add_cancel]
  rw [sub_eq_add_neg, unit_add, unit_add, ← mul_add, he]

theorem diameterVector_eq_unit {n : ℕ} (θ : Fin n → ℝ) (j : Fin n) :
    diameterVector θ j = unit (2 * Real.pi * j / n + θ j) := by
  rw [diameterVector, unit_add, character_eq_exp]
  simp only [Nat.cast_one, mul_one, unit]

theorem diameter_sum_half {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (j : Fin m) :
    diameterVector θ (CommonClosureEnergy.halfIndex j) +
      diameterVector θ (successor (by omega) (CommonClosureEnergy.halfIndex j)) =
      unit (phase hm θ j) * (2 * Real.cos (halfAngle hm θ j) : ℝ) := by
  have hj : (successor (by omega) (CommonClosureEnergy.halfIndex j)).val = j.val + 1 := by
    dsimp [successor, CommonClosureEnergy.halfIndex]
    exact Nat.mod_eq_of_lt (by omega)
  have h₁ : 2 * Real.pi * (CommonClosureEnergy.halfIndex j).val / (2 * m : ℕ) +
      θ (CommonClosureEnergy.halfIndex j) = phase hm θ j - halfAngle hm θ j := by
    unfold phase halfAngle LensClosure.midpoint angleAverage angleDifference CommonClosureEnergy.halfIndex
    push_cast
    ring
  have h₂ : 2 * Real.pi * (successor (by omega) (CommonClosureEnergy.halfIndex j)).val / (2 * m : ℕ) +
      θ (successor (by omega) (CommonClosureEnergy.halfIndex j)) = phase hm θ j + halfAngle hm θ j := by
    rw [hj]
    unfold phase halfAngle LensClosure.midpoint angleAverage angleDifference
    push_cast
    ring
  rw [diameterVector_eq_unit, diameterVector_eq_unit, h₁, h₂, unit_pair]

theorem crossing_plus_squared {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) :
    ‖configuration hm θ v σ ξ (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
      configuration hm θ v σ ξ (halfTurn hm (CommonClosureEnergy.halfIndex j))‖ ^ 2 =
      (2 * Real.cos (halfAngle hm θ j) + σ j * Lens.width (2 * Real.cos (halfAngle hm θ j))
        (heightParameter (coordinates hm v) ξ j)) ^ 2 + (heightParameter (coordinates hm v) ξ j) ^ 2 := by
  have he : configuration hm θ v σ ξ (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
      configuration hm θ v σ ξ (halfTurn hm (CommonClosureEnergy.halfIndex j)) =
      diameterVector θ (CommonClosureEnergy.halfIndex j) +
        diameterVector θ (successor (by omega) (CommonClosureEnergy.halfIndex j)) +
        difference (by omega) (center hm θ v σ ξ) (CommonClosureEnergy.halfIndex j) := by
    simp only [configuration, diameterVector_halfTurn hm θ hθ,
      center_halfPeriodic hm θ v σ ξ hz (CommonClosureEnergy.halfIndex j), difference]
    ring
  rw [he, diameter_sum_half hm θ j, center_half_difference hm θ v σ ξ hz]
  unfold fiberIncrement LensClosure.increment
  rw [mul_comm (unit (phase hm θ j)) ((2 * Real.cos (halfAngle hm θ j) : ℝ) : ℂ)]
  exact Lens.norm_sq_rotated_plus (norm_unit _) _ _ _

theorem positive_crossing_length {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) (hσ : σ j = 1) (ht : (heightParameter (coordinates hm v) ξ j) ^ 2 ≤ 4) :
    ‖configuration hm θ v σ ξ (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
      configuration hm θ v σ ξ (halfTurn hm (CommonClosureEnergy.halfIndex j))‖ = 2 := by
  have he := crossing_plus_squared hm θ v σ ξ hθ hz j
  rw [hσ, one_mul, Lens.positive_endpoint_eq ht] at he
  nlinarith [norm_nonneg (configuration hm θ v σ ξ (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
    configuration hm θ v σ ξ (halfTurn hm (CommonClosureEnergy.halfIndex j)))]

theorem crossing_minus_squared {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) :
    ‖configuration hm θ v σ ξ (CommonClosureEnergy.halfIndex j) -
      configuration hm θ v σ ξ (halfTurn hm (successor (by omega) (CommonClosureEnergy.halfIndex j)))‖ ^ 2 =
      (2 * Real.cos (halfAngle hm θ j) - σ j * Lens.width (2 * Real.cos (halfAngle hm θ j))
        (heightParameter (coordinates hm v) ξ j)) ^ 2 + (heightParameter (coordinates hm v) ξ j) ^ 2 := by
  have he : configuration hm θ v σ ξ (CommonClosureEnergy.halfIndex j) -
      configuration hm θ v σ ξ (halfTurn hm (successor (by omega) (CommonClosureEnergy.halfIndex j))) =
      diameterVector θ (CommonClosureEnergy.halfIndex j) +
        diameterVector θ (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
        difference (by omega) (center hm θ v σ ξ) (CommonClosureEnergy.halfIndex j) := by
    simp only [configuration, diameterVector_halfTurn hm θ hθ,
      center_halfPeriodic hm θ v σ ξ hz (successor (by omega) (CommonClosureEnergy.halfIndex j)), difference]
    ring
  rw [he, diameter_sum_half hm θ j, center_half_difference hm θ v σ ξ hz]
  unfold fiberIncrement LensClosure.increment
  rw [mul_comm (unit (phase hm θ j)) ((2 * Real.cos (halfAngle hm θ j) : ℝ) : ℂ)]
  exact Lens.norm_sq_rotated_minus (norm_unit _) _ _ _

theorem negative_crossing_length {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (v : Fin (2 * m) → ℂ) (σ : Fin m → ℝ) (ξ : ℂ)
    (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closure (phase hm θ) (fun j => 2 * Real.cos (halfAngle hm θ j)) σ (coordinates hm v) ξ = 0)
    (j : Fin m) (hσ : σ j = -1) (ht : (heightParameter (coordinates hm v) ξ j) ^ 2 ≤ 4) :
    ‖configuration hm θ v σ ξ (CommonClosureEnergy.halfIndex j) -
      configuration hm θ v σ ξ (halfTurn hm (successor (by omega) (CommonClosureEnergy.halfIndex j)))‖ = 2 := by
  have he := crossing_minus_squared hm θ v σ ξ hθ hz j
  rw [hσ, neg_one_mul, sub_neg_eq_add, Lens.positive_endpoint_eq ht] at he
  nlinarith [norm_nonneg (configuration hm θ v σ ξ (CommonClosureEnergy.halfIndex j) -
    configuration hm θ v σ ξ (halfTurn hm (successor (by omega) (CommonClosureEnergy.halfIndex j))))]

end
end StructuralNote.CommonFiberGeometry
