import StructuralNote.MatchingActivityRadialGeometry

/-! Construction of the actual base point for the unsaturated radial lens chart. -/

namespace StructuralNote.MatchingActivityRadialBase

open Erdos1045 Erdos1045.EventualExact Complex Configuration
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters
open MatchingActivityRadialPair MatchingActivityRadialBounds MatchingActivityRadialLens
open MatchingActivityRadialClosure MatchingActivityRadialGeometry
open scoped BigOperators
noncomputable section

theorem exists_base_coordinates {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ) (r : Fin m → ℝ)
    (c : Fin (2 * m) → ℂ) (hhalf : HalfPeriodic (by omega) (fun j => (θ j : ℂ)))
    (hc : HalfPeriodic (by omega) c) (hz : DiameterAtMost 2 (vertices (by omega) θ r c))
    (hr : ∀ j, 3 / 4 ≤ r j ∧ r j ≤ 1)
    (hθ : ∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hstep : ∀ j, ‖difference (by omega) c j‖ ≤ 1 / (1000 * (2 * m : ℝ))) :
    ∃ σ ν : Fin m → ℝ,
      (∀ j, |σ j| ≤ 1) ∧
      (∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
      (∀ j, difference (by omega) c (CommonClosureEnergy.halfIndex j) =
        radialIncrement (by omega) θ σ ν r 0 j) ∧
      (∀ j, 0 < Lens.width (radialLength (by omega) θ r j) (ν j)) ∧
      (∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4) ∧
      closureFamily (parameters (by omega) θ σ ν r) 0 = 0 := by
  let ν : Fin m → ℝ := fun j =>
    (framed (radialPhase (by omega) θ r j) (difference (by omega) c (CommonClosureEnergy.halfIndex j))).im
  have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hν (j : Fin m) : |ν j| ≤ 1 / (1000 * (2 * m : ℝ)) := by
    exact (abs_im_le_norm _).trans ((framed_norm _ _).le.trans (hstep _))
  have hwidth (j : Fin m) : 0 < Lens.width (radialLength (by omega) θ r j) (ν j) := by
    have ha := small_half_angle hm θ hθ j
    apply width_positive_at_scale (r₀ := r j) (r₁ := r (nextIndex (show 0 < m by omega) j)) hn0 ha.2.1 (by linarith [(hr j).1])
      (by linarith [(hr (nextIndex (show 0 < m by omega) j)).1]) (hr j).2 (hr (nextIndex (by omega) j)).2 ha.2.2
    have hh : 1 / (1000 * (2 * m : ℝ)) ≤ 1 / (2 * m : ℝ) := by
      apply one_div_le_one_div_of_le hn0
      nlinarith
    exact (hν j).trans hh
  have hex (j : Fin m) : ∃ s : ℝ, |s| ≤ 1 ∧
      difference (by omega) c (CommonClosureEnergy.halfIndex j) =
        increment (radialPhase (by omega) θ r j) (radialLength (by omega) θ r j) s (ν j) := by
    have hcross := crossing_constraints (by omega) θ r c hhalf hc hz j
    apply exists_lens_control (difference (by omega) c (CommonClosureEnergy.halfIndex j)) (hwidth j)
    · rw [← rotated_length_direction]
      exact hcross.1
    · rw [← rotated_length_direction]
      exact hcross.2
  choose σ hσ he using hex
  have hinc (j : Fin m) : difference (by omega) c (CommonClosureEnergy.halfIndex j) =
      radialIncrement (by omega) θ σ ν r 0 j := by
    simpa only [radialIncrement, heightParameter, map_zero, add_zero] using he j
  refine ⟨σ, ν, hσ, hν, hinc, hwidth, ?_, ?_⟩
  · intro j
    have ha := small_half_angle hm θ hθ j
    have hp := pair_re_ge_one ha.2.1 (hr j).1 (hr (nextIndex (by omega) j)).1
    have hd := direction_bound hp
    have hrd : |r (nextIndex (by omega) j) - r j| ≤ 1 / 4 :=
      abs_le.mpr ⟨by linarith [(hr j).2, (hr (nextIndex (by omega) j)).1],
        by linarith [(hr j).1, (hr (nextIndex (by omega) j)).2]⟩
    have hdir : |direction (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))| ≤ 1 / 8 := by
      have hh := mul_le_mul (mul_le_mul_of_nonneg_left hrd (by norm_num : (0 : ℝ) ≤ 2)) ha.2.1
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * (1 / 4))
      linarith only [hd, hh]
    have hav : |angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)| ≤ 1 / (1000 * (2 * m : ℝ)) := by
      unfold angleAverage
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hh := abs_add_le (θ (CommonClosureEnergy.halfIndex j)) (θ (successor (by omega) (CommonClosureEnergy.halfIndex j)))
      linarith [hθ (CommonClosureEnergy.halfIndex j), hθ (successor (by omega) (CommonClosureEnergy.halfIndex j))]
    have hα : |radialPhase (by omega) θ r j - midpoint m j| ≤
        1 / (1000 * (2 * m : ℝ)) + 1 / 8 := by
      unfold radialPhase phase
      rw [show midpoint m j + angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) +
          direction (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j)) - midpoint m j =
          angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) +
          direction (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j)) by ring]
      exact (abs_add_le _ _).trans (add_le_add hav hdir)
    have hnum : 1 / (1000 * (2 * m : ℝ)) ≤ 1 / 16 := by
      apply (div_le_iff₀ (by positivity : 0 < 1000 * (2 * m : ℝ))).2
      nlinarith
    linarith [hν j]
  · change (∑ j, radialIncrement (by omega) θ σ ν r 0 j) = 0
    simp_rw [← hinc]
    exact half_difference_sum (by omega) c hc

end
end StructuralNote.MatchingActivityRadialBase
