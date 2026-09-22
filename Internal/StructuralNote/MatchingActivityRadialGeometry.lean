import StructuralNote.MatchingActivityRadialClosure
import StructuralNote.MatchingActivityRadialLens

/-! Geometry of the unsaturated radial lens chart. -/

namespace StructuralNote.MatchingActivityRadialGeometry

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters
open MatchingActivityRadialPair MatchingActivityRadialBounds MatchingActivityRadialLens MatchingActivityRadialClosure
open scoped BigOperators
noncomputable section

def radiusFull {m : ℕ} (hm : 0 < m) (r : Fin m → ℝ) (j : Fin (2 * m)) : ℝ :=
  r ⟨j.val % m, Nat.mod_lt _ hm⟩

def vertices {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ)
    (c : Fin (2 * m) → ℂ) (j : Fin (2 * m)) : ℂ :=
  (radiusFull hm r j : ℂ) * diameterVector θ j + c j

theorem radiusFull_halfIndex {m : ℕ} (hm : 0 < m) (r : Fin m → ℝ) (j : Fin m) :
    radiusFull hm r (CommonClosureEnergy.halfIndex j) = r j := by
  simp only [radiusFull, CommonClosureEnergy.halfIndex, Nat.mod_eq_of_lt j.isLt]

theorem radiusFull_next {m : ℕ} (hm : 0 < m) (r : Fin m → ℝ) (j : Fin m) :
    radiusFull hm r (successor (by omega) (CommonClosureEnergy.halfIndex j)) = r (nextIndex hm j) := by
  have he : (successor (by omega) (CommonClosureEnergy.halfIndex j)).val = j.val + 1 := by
    dsimp [successor, CommonClosureEnergy.halfIndex]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [radiusFull, he, nextIndex]

theorem radiusFull_halfTurn {m : ℕ} (hm : 0 < m) (r : Fin m → ℝ) (j : Fin (2 * m)) :
    radiusFull hm r (halfTurn hm j) = radiusFull hm r j := by
  unfold radiusFull
  apply congrArg r
  apply Fin.ext
  change (j.val + m) % (2 * m) % m = j.val % m
  rw [Nat.mod_mod_of_dvd _ (by exact ⟨2, by omega⟩ : m ∣ 2 * m), Nat.add_mod_right]

theorem weighted_diameter_sum {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ) (j : Fin m) :
    (radiusFull hm r (CommonClosureEnergy.halfIndex j) : ℂ) * diameterVector θ (CommonClosureEnergy.halfIndex j) +
      (radiusFull hm r (successor (by omega) (CommonClosureEnergy.halfIndex j)) : ℂ) *
        diameterVector θ (successor (by omega) (CommonClosureEnergy.halfIndex j)) =
      (radialLength hm θ r j : ℂ) * unit (radialPhase hm θ r j) := by
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
  rw [radiusFull_halfIndex, radiusFull_next, diameterVector_eq_unit, diameterVector_eq_unit, h₁, h₂]
  exact (rotated_length_direction _ _ _ _).symm

theorem crossing_constraints {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ)
    (c : Fin (2 * m) → ℂ) (hθ : HalfPeriodic hm (fun j => (θ j : ℂ))) (hc : HalfPeriodic hm c)
    (hz : DiameterAtMost 2 (vertices hm θ r c)) (j : Fin m) :
    ‖(radialLength hm θ r j : ℂ) * unit (radialPhase hm θ r j) +
      difference (by omega) c (CommonClosureEnergy.halfIndex j)‖ ≤ 2 ∧
    ‖(radialLength hm θ r j : ℂ) * unit (radialPhase hm θ r j) -
      difference (by omega) c (CommonClosureEnergy.halfIndex j)‖ ≤ 2 := by
  change ∀ i, c (halfTurn hm i) = c i at hc
  rw [← weighted_diameter_sum]
  constructor
  · have hh := hz (successor (by omega) (CommonClosureEnergy.halfIndex j)) (halfTurn hm (CommonClosureEnergy.halfIndex j))
    simp only [vertices, radiusFull_halfTurn, diameterVector_halfTurn hm θ hθ, hc] at hh
    convert hh using 1
    congr 1
    unfold difference
    ring
  · have hh := hz (CommonClosureEnergy.halfIndex j) (halfTurn hm (successor (by omega) (CommonClosureEnergy.halfIndex j)))
    simp only [vertices, radiusFull_halfTurn, diameterVector_halfTurn hm θ hθ, hc] at hh
    convert hh using 1
    congr 1
    unfold difference
    ring

theorem small_half_angle {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin m) :
    2 / (2 * m : ℝ) ≤ halfAngle (by omega) θ j ∧
    |halfAngle (by omega) θ j| ≤ 1 / 4 ∧
    1 / (2 * m : ℝ) ≤ Real.sin (halfAngle (by omega) θ j) := by
  have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hdiff : |angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j) / 2| ≤
      1 / (1000 * (2 * m : ℝ)) := by
    have hh := abs_sub (θ (successor (by omega) (CommonClosureEnergy.halfIndex j))) (θ (CommonClosureEnergy.halfIndex j))
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    change |θ (successor (by omega) (CommonClosureEnergy.halfIndex j)) - θ (CommonClosureEnergy.halfIndex j)| / 2 ≤ _
    linarith [hθ (CommonClosureEnergy.halfIndex j), hθ (successor (by omega) (CommonClosureEnergy.halfIndex j))]
  have herr := abs_le.mp hdiff
  have hlo : 2 / (2 * m : ℝ) ≤ halfAngle (by omega) θ j := by
    have hp : 2 / (2 * m : ℝ) + 1 / (1000 * (2 * m : ℝ)) ≤ Real.pi / (2 * m : ℝ) := by
      apply (le_of_mul_le_mul_right ?_ hn0)
      field_simp
      linarith [Real.pi_gt_three]
    unfold halfAngle
    linarith
  have hup : halfAngle (by omega) θ j ≤ 4 / (2 * m : ℝ) := by
    have hp : Real.pi / (2 * m : ℝ) + 1 / (1000 * (2 * m : ℝ)) ≤ 4 / (2 * m : ℝ) := by
      apply (le_of_mul_le_mul_right ?_ hn0)
      field_simp
      linarith [Real.pi_lt_d2]
    unfold halfAngle
    linarith
  have ha0 : 0 ≤ halfAngle (by omega) θ j := (by positivity : 0 ≤ 2 / (2 * m : ℝ)).trans hlo
  have ha : halfAngle (by omega) θ j ≤ 1 / 4 := by
    have hh : (4 : ℝ) / (2 * m) ≤ 1 / 4 := (div_le_iff₀ hn0).2 (by linarith)
    exact hup.trans hh
  refine ⟨hlo, by rwa [abs_of_nonneg ha0], ?_⟩
  have hs := Real.mul_le_sin ha0 (show halfAngle (by omega) θ j ≤ Real.pi / 2 by linarith [Real.pi_gt_three])
  have hm := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2 / Real.pi by positivity)
  have hh : 1 / (2 * m : ℝ) ≤ (2 / Real.pi) * (2 / (2 * m : ℝ)) := by
    apply (le_of_mul_le_mul_right ?_ (mul_pos Real.pi_pos hn0))
    field_simp
    linarith [Real.pi_lt_four]
  exact hh.trans (hm.trans hs)

end
end StructuralNote.MatchingActivityRadialGeometry
