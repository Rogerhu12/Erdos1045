import StructuralNote.MatchingActivityRadialIntegration

/-! Matching and adjacent distance constraints for the unsaturated radial chart. -/

namespace StructuralNote.MatchingActivityRadialConstraints

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters BoxLensLift
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialIntegration
open scoped BigOperators Topology ContDiff
noncomputable section

theorem matching_distance {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ a : ℂ) (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closureFamily (parameters hm θ σ ν r) ξ = 0) (j : Fin (2 * m)) :
    ‖radialConfiguration hm θ σ ν r ξ a (halfTurn hm j) - radialConfiguration hm θ σ ν r ξ a j‖ =
      2 * |radiusFull hm r j| := by
  have he : radialConfiguration hm θ σ ν r ξ a (halfTurn hm j) - radialConfiguration hm θ σ ν r ξ a j =
      (-2 : ℂ) * (radiusFull hm r j : ℂ) * diameterVector θ j := by
    simp only [radialConfiguration, vertices, radiusFull_halfTurn, diameterVector_halfTurn hm θ hθ,
      radialCenter_halfPeriodic hm θ σ ν r ξ hz j]
    ring
  rw [he, norm_mul, norm_mul, diameterVector_norm, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem crossing_distances {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ a : ℂ) (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closureFamily (parameters hm θ σ ν r) ξ = 0)
    (hσ : ∀ j, |σ j| ≤ 1)
    (ht : ∀ j, (heightParameter ν ξ j) ^ 2 ≤ 4)
    (hw : ∀ j, 0 < Lens.width (radialLength hm θ r j) (heightParameter ν ξ j)) (j : Fin m) :
    ‖radialConfiguration hm θ σ ν r ξ a (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
      radialConfiguration hm θ σ ν r ξ a (halfTurn hm (CommonClosureEnergy.halfIndex j))‖ ≤ 2 ∧
    ‖radialConfiguration hm θ σ ν r ξ a (CommonClosureEnergy.halfIndex j) -
      radialConfiguration hm θ σ ν r ξ a (halfTurn hm (successor (by omega) (CommonClosureEnergy.halfIndex j)))‖ ≤ 2 := by
  have hL : 0 ≤ radialLength hm θ r j := norm_nonneg _
  have hh := (Lens.rotated_normalized_constraints_iff (norm_unit (radialPhase hm θ r j)) hL (ht j) (hw j)).mpr (hσ j)
  have hd : difference (by omega) (radialCenter hm θ σ ν r ξ) (CommonClosureEnergy.halfIndex j) =
      radialIncrement hm θ σ ν r ξ j := by
    rw [radialCenter_difference hm θ σ ν r ξ hz]
    exact repeatHalf_halfIndex hm _ j
  have hc := radialCenter_halfPeriodic hm θ σ ν r ξ hz
  change ∀ k, radialCenter hm θ σ ν r ξ (halfTurn hm k) = radialCenter hm θ σ ν r ξ k at hc
  have he₁ : radialConfiguration hm θ σ ν r ξ a (successor (by omega) (CommonClosureEnergy.halfIndex j)) -
      radialConfiguration hm θ σ ν r ξ a (halfTurn hm (CommonClosureEnergy.halfIndex j)) =
      (radialLength hm θ r j : ℂ) * unit (radialPhase hm θ r j) + radialIncrement hm θ σ ν r ξ j := by
    rw [← weighted_diameter_sum, ← hd]
    simp only [radialConfiguration, vertices, radiusFull_halfTurn, diameterVector_halfTurn hm θ hθ, hc, difference]
    ring
  have he₂ : radialConfiguration hm θ σ ν r ξ a (CommonClosureEnergy.halfIndex j) -
      radialConfiguration hm θ σ ν r ξ a (halfTurn hm (successor (by omega) (CommonClosureEnergy.halfIndex j))) =
      (radialLength hm θ r j : ℂ) * unit (radialPhase hm θ r j) - radialIncrement hm θ σ ν r ξ j := by
    rw [← weighted_diameter_sum, ← hd]
    simp only [radialConfiguration, vertices, radiusFull_halfTurn, diameterVector_halfTurn hm θ hθ, hc, difference]
    ring
  rw [he₁, he₂]
  exact hh

theorem adjacent_next {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ a : ℂ) (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closureFamily (parameters hm θ σ ν r) ξ = 0)
    (hσ : ∀ j, |σ j| ≤ 1) (ht : ∀ j, (heightParameter ν ξ j) ^ 2 ≤ 4)
    (hw : ∀ j, 0 < Lens.width (radialLength hm θ r j) (heightParameter ν ξ j)) (j : Fin (2 * m)) :
    ‖radialConfiguration hm θ σ ν r ξ a (cyclicAdvance j (m + 1)) - radialConfiguration hm θ σ ν r ξ a j‖ ≤ 2 := by
  have he : cyclicAdvance j (m + 1) = halfTurn hm (successor (by omega) j) := by
    apply Fin.ext
    simp only [cyclicAdvance, halfTurn, successor, Nat.mod_add_mod]
    congr 1
    omega
  rw [he, norm_sub_rev]
  obtain ⟨k, hj | hj⟩ := half_decomposition hm j
  · rw [hj]
    exact (crossing_distances hm θ σ ν r ξ a hθ hz hσ ht hw k).2
  · rw [hj, ← halfTurn_successor, halfTurn_involutive hm, norm_sub_rev]
    exact (crossing_distances hm θ σ ν r ξ a hθ hz hσ ht hw k).1

theorem diameter_of_nonlocal {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (ξ a : ℂ) (hθ : HalfPeriodic hm (fun j => (θ j : ℂ)))
    (hz : closureFamily (parameters hm θ σ ν r) ξ = 0)
    (hσ : ∀ j, |σ j| ≤ 1) (ht : ∀ j, (heightParameter ν ξ j) ^ 2 ≤ 4)
    (hw : ∀ j, 0 < Lens.width (radialLength hm θ r j) (heightParameter ν ξ j))
    (hr : ∀ j, |r j| ≤ 1)
    (hfar : ∀ (j : Fin (2 * m)) (k : Fin (2 * m)), k.val ≠ m - 1 → k.val ≠ m → k.val ≠ m + 1 →
      ‖radialConfiguration hm θ σ ν r ξ a (cyclicAdvance j k.val) - radialConfiguration hm θ σ ν r ξ a j‖ < 2) :
    DiameterAtMost 2 (radialConfiguration hm θ σ ν r ξ a) := by
  have hb (j : Fin (2 * m)) (k : Fin (2 * m)) :
      ‖radialConfiguration hm θ σ ν r ξ a (cyclicAdvance j k.val) - radialConfiguration hm θ σ ν r ξ a j‖ ≤ 2 := by
    by_cases hp : k.val = m - 1
    · rw [hp]
      have hh := adjacent_next hm θ σ ν r ξ a hθ hz hσ ht hw (cyclicAdvance j (m - 1))
      rwa [NonlocalFeasibility.advance_back_forward (by omega : 1 ≤ m), norm_sub_rev] at hh
    by_cases hm' : k.val = m
    · rw [hm']
      change ‖radialConfiguration hm θ σ ν r ξ a (halfTurn hm j) - radialConfiguration hm θ σ ν r ξ a j‖ ≤ 2
      rw [matching_distance hm θ σ ν r ξ a hθ hz]
      have hh := hr ⟨j.val % m, Nat.mod_lt _ hm⟩
      change |radiusFull hm r j| ≤ 1 at hh
      linarith
    by_cases hn : k.val = m + 1
    · rw [hn]
      exact adjacent_next hm θ σ ν r ξ a hθ hz hσ ht hw j
    exact (hfar j k hp hm' hn).le
  intro i j
  let k : Fin (2 * m) := ⟨cyclicForwardDistance j i, Nat.mod_lt _ (by omega)⟩
  have hh := hb j k
  change ‖radialConfiguration hm θ σ ν r ξ a (cyclicAdvance j (cyclicForwardDistance j i)) -
    radialConfiguration hm θ σ ν r ξ a j‖ ≤ 2 at hh
  have he : cyclicAdvance j (cyclicForwardDistance j i) = i := by
    apply Fin.ext
    simp only [cyclicAdvance, cyclicForwardDistance, Nat.add_mod_mod]
    rw [show j.val + (i.val + 2 * m - j.val) = i.val + 2 * m by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  rwa [he] at hh

end
end StructuralNote.MatchingActivityRadialConstraints
