import StructuralNote.MatchingActivityRadialPressure

/-! The small phase and source-body inputs of the pressure estimate follow
from the genuine radial chart and the already proved pointwise geometry. -/

namespace StructuralNote.MatchingActivityRadialSmallness

open Erdos1045 Erdos1045.EventualExact Complex Configuration Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters
open MatchingActivityRadialClosure MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialGeometry MatchingActivityRadialIntegration MatchingActivityRadialFeasible
open LensIncrementDerivatives LensClosurePathDerivatives
open scoped Topology
noncomputable section

theorem halfAngle_scale {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (hθ : ∀ i, |θ i| ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin m) :
    |halfAngle (by omega) θ j| ≤ 4 / (2 * m : ℝ) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have hdiff : |angleDifference (by omega) θ (CommonClosureEnergy.halfIndex j) / 2| ≤
      1 / (1000 * (2 * m : ℝ)) := by
    have hh := abs_sub (θ (successor (by omega) (CommonClosureEnergy.halfIndex j))) (θ (CommonClosureEnergy.halfIndex j))
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    change |θ (successor (by omega) (CommonClosureEnergy.halfIndex j)) - θ (CommonClosureEnergy.halfIndex j)| / 2 ≤ _
    linarith [hθ (CommonClosureEnergy.halfIndex j), hθ (successor (by omega) (CommonClosureEnergy.halfIndex j))]
  have hup : Real.pi / (2 * m : ℝ) + 1 / (1000 * (2 * m : ℝ)) ≤ 4 / (2 * m : ℝ) := by
    apply (le_of_mul_le_mul_right ?_ hn0)
    field_simp
    linarith [Real.pi_lt_d2]
  have hlo := (small_half_angle hm θ hθ j).1
  rw [abs_of_nonneg ((show 0 ≤ 2 / (2 * m : ℝ) by positivity).trans hlo)]
  unfold halfAngle
  linarith [(abs_le.mp hdiff).2]

theorem phaseHeight_scale {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (r ν : Fin m → ℝ) (hr : ∀ j, 3 / 4 ≤ r j ∧ r j ≤ 1)
    (hθ : ∀ j, |θ j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hν : ∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin m) :
    |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 4 / (2 * m : ℝ) := by
  have hn0 : (0 : ℝ) < 2 * m := by positivity
  have ha := small_half_angle hm θ hθ j
  have hp := pair_re_ge_one ha.2.1 (hr j).1 (hr (nextIndex (by omega) j)).1
  have hd := direction_bound hp
  have hrd : |r (nextIndex (by omega) j) - r j| ≤ 1 / 4 :=
    abs_le.mpr ⟨by linarith [(hr j).2, (hr (nextIndex (by omega) j)).1],
      by linarith [(hr j).1, (hr (nextIndex (by omega) j)).2]⟩
  have hdir : |direction (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j))| ≤ 2 / (2 * m : ℝ) := by
    have hh := mul_le_mul (mul_le_mul_of_nonneg_left hrd (by norm_num : (0 : ℝ) ≤ 2)) (halfAngle_scale hm θ hθ j)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2 * (1 / 4))
    exact (hd.trans hh).trans_eq (by ring)
  have hav : |angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j)| ≤ 1 / (1000 * (2 * m : ℝ)) := by
    unfold angleAverage
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hh := abs_add_le (θ (CommonClosureEnergy.halfIndex j)) (θ (successor (by omega) (CommonClosureEnergy.halfIndex j)))
    linarith [hθ (CommonClosureEnergy.halfIndex j), hθ (successor (by omega) (CommonClosureEnergy.halfIndex j))]
  have hα : |radialPhase (by omega) θ r j - midpoint m j| ≤
      1 / (1000 * (2 * m : ℝ)) + 2 / (2 * m : ℝ) := by
    unfold radialPhase phase
    rw [show midpoint m j + angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) +
        direction (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j)) - midpoint m j =
        angleAverage (by omega) θ (CommonClosureEnergy.halfIndex j) +
        direction (halfAngle (by omega) θ j) (r j) (r (nextIndex (by omega) j)) by ring]
    exact (abs_add_le _ _).trans (add_le_add hav hdir)
  have hnum : 2 * (1 / (1000 * (2 * m : ℝ))) + 2 / (2 * m : ℝ) ≤ 4 / (2 * m : ℝ) := by
    apply le_of_mul_le_mul_right _ hn0
    field_simp
    norm_num
  linarith [hν j]

theorem chart_base_increment {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (c : Fin (2 * m) → ℂ)
    (hchart : IsFeasibleRadialChart hm θ σ ν r a g)
    (hbase : radialConfiguration hm θ σ ν r 0 a = vertices hm θ r c) (j : Fin m) :
    difference (by omega) c (CommonClosureEnergy.halfIndex j) = radialIncrement hm θ σ ν r 0 j := by
  have hz : closureFamily (parameters hm θ σ ν r) 0 = 0 := by
    simpa only [hchart.2.1] using hchart.2.2.2.1.self_of_nhds
  have hc (k : Fin (2 * m)) : radialCenter hm θ σ ν r 0 k + a = c k := by
    have hh := congrFun hbase k
    dsimp only [radialConfiguration, vertices] at hh
    linear_combination hh
  have hd := congrFun (radialCenter_difference hm θ σ ν r 0 hz) (CommonClosureEnergy.halfIndex j)
  have hd' := hd.trans (CommonTangentialParameters.repeatHalf_halfIndex hm _ j)
  unfold difference
  clear hd
  rw [← hc (successor _ (CommonClosureEnergy.halfIndex j)), ← hc (CommonClosureEnergy.halfIndex j)]
  change radialCenter hm θ σ ν r 0 (successor _ _) + a - (radialCenter hm θ σ ν r 0 _ + a) = _
  change radialCenter hm θ σ ν r 0 (successor _ _) - radialCenter hm θ σ ν r 0 _ = _ at hd'
  linear_combination hd'

theorem chart_body_small {m : ℕ} (hm : 8 ≤ m) (θ : Fin (2 * m) → ℝ)
    (σ ν r : Fin m → ℝ) (a : ℂ) (g : (Fin m → ℝ) → ℂ) (c : Fin (2 * m) → ℂ)
    (hchart : IsFeasibleRadialChart (by omega) θ σ ν r a g)
    (hbase : radialConfiguration (by omega) θ σ ν r 0 a = vertices (by omega) θ r c)
    (hstep : ∀ j, ‖difference (by omega) c j‖ ≤ 1 / (1000 * (2 * m : ℝ))) (j : Fin m) :
    ‖body (radialLength (by omega) θ r j) (σ j) (ν j)‖ ≤ 1 / 4 := by
  have hi := chart_base_increment (by omega) θ σ ν r a g c hchart hbase j
  have hh := hstep (CommonClosureEnergy.halfIndex j)
  rw [hi] at hh
  simp only [radialIncrement, heightParameter, map_zero, add_zero, LensClosure.increment, norm_mul, norm_unit, one_mul] at hh
  have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
  have he : 1 / (1000 * (2 * m : ℝ)) ≤ 1 / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < 1000 * (2 * m : ℝ))).2
    nlinarith
  exact hh.trans he

end
end StructuralNote.MatchingActivityRadialSmallness
