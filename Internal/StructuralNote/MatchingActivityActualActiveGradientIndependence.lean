import StructuralNote.MatchingActivityActiveGradientIndependence
import StructuralNote.MatchingActivityCrossingVariationSaturation
import StructuralNote.MatchingActivityRadialSmallness

/-! The active constraint differentials are independent at the genuine
normalized extremal configuration.  The selected crossing signs here are
read from physical crossing activity. -/

namespace StructuralNote.MatchingActivityActualActiveGradientIndependence

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters
open MatchingActivityRadialPair MatchingActivityRadialBounds MatchingActivityRadialLens
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityRadialFeasible
open MatchingActivityRadialSmallness
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveGradientIndependence
open MatchingActivityActualChartSelection MatchingActivityCrossingExclusivity
open StrongPointwiseCoordinates StrongPointwiseSmallness MatchingActivityNonlocalPairs
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open scoped BigOperators Topology ContDiff

noncomputable section

theorem model_activeConstraintDifferentialsIndependent {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : DiameterAtMost 2 z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : StrongPointwiseSteps.physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤
      10 - Real.pi ^ 2)
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1)
    (hactive : ∀ i : Fin m,
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2)) :
    ActiveConstraintDifferentialsIndependent (by omega)
      (fun i => activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i)
      (normalizedPoint m β u) := by
  obtain ⟨hθ, hstep, _⟩ := model_nonlocal_smallness hm h hz hbounds hbudget
    hsmallB hsmallC hsmallR
  obtain ⟨s, ν, g, hchart, hbase, hν⟩ := model_feasible_radial_chart hm h hz
    hbounds hbudget hsmallB hsmallC hsmallR (by
      calc
        2 * budgetConstant / (2 * m : ℝ) =
            (1 / 2 : ℝ) * (4 * budgetConstant / (2 * m : ℝ)) := by ring
        _ ≤ (1 / 2 : ℝ) * (1 / 1000000) :=
          mul_le_mul_of_nonneg_left hsmallB (by norm_num)
        _ ≤ 1 / 10 := by norm_num)
  have hhalf : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u h.periodic j)
  have hr (j : Fin m) : 3 / 4 ≤ modelRadii m β u j ∧ modelRadii m β u j ≤ 1 := by
    rw [hsat j]
    norm_num
  have hbaseC : radialConfiguration (by omega) (normalizedAngle m u) s ν
      (modelRadii m β u) 0 (average (actualCenter m β u)) =
      vertices (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) := by
    exact hbase.trans (model_vertices (by omega) β u h.periodic).symm
  have hinc (j : Fin m) : difference (by omega) (actualCenter m β u)
      (CommonClosureEnergy.halfIndex j) =
      radialIncrement (by omega) (normalizedAngle m u) s ν
        (modelRadii m β u) 0 j :=
    chart_base_increment (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
      (average (actualCenter m β u)) g (actualCenter m β u) hchart hbaseC j
  have hwidth (j : Fin m) : 0 < Lens.width
      (radialLength (by omega) (normalizedAngle m u) (modelRadii m β u) j) (ν j) := by
    have ha := small_half_angle hm (normalizedAngle m u) hθ j
    apply width_positive_at_scale (n := (2 * m : ℝ)) (r₀ := modelRadii m β u j)
      (r₁ := modelRadii m β u (nextIndex (by omega) j)) (t := ν j)
      (by positivity) ha.2.1 (by linarith [(hr j).1])
      (by linarith [(hr (nextIndex (by omega) j)).1]) (hr j).2
      (hr (nextIndex (by omega) j)).2 ha.2.2
    exact (hν j).trans (by
      apply one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2 * m)
      nlinarith)
  have hsmall (j : Fin m) :
      |radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) j -
          LensClosure.midpoint m j| +
        |ν j| ≤ 1 / 4 := by
    have hs := phaseHeight_scale hm (normalizedAngle m u) (modelRadii m β u) ν
      hr hθ hν j
    have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
    exact hs.trans (by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
      nlinarith)
  have hpos (j : Fin m) : 0 < (pair
      (halfAngle (by omega) (normalizedAngle m u) j)
      (modelRadii m β u j) (modelRadii m β u (nextIndex (by omega) j))).re := by
    have ha := small_half_angle hm (normalizedAngle m u) hθ j
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (pair_re_ge_one ha.2.1 (hr j).1 (hr (nextIndex (by omega) j)).1)
  have hsactive (i : Fin m) : s i = activeHalfSign (by omega)
      (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u) i := by
    have ht : (ν i) ^ 2 ≤ 4 := by
      have hb := hν i
      have hlt : |ν i| < 2 := hb.trans_lt ((by
        apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m : ℝ))).2
        have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
        nlinarith) : 1 / (1000 * (2 * m : ℝ)) < 2)
      nlinarith [(abs_lt.mp hlt).1, (abs_lt.mp hlt).2]
    have hL : 0 < radialLength (by omega) (normalizedAngle m u)
        (modelRadii m β u) i := by
      unfold radialLength
      apply length_pos
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (pair_re_ge_one (small_half_angle hm (normalizedAngle m u) hθ i).2.1
          (hr i).1 (hr (nextIndex (by omega) i)).1)
    have hp := Lens.rotated_plus_active_iff
      (norm_unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i))
      hL ht (hwidth i) (hchart.1 i)
    have hn := Lens.rotated_minus_active_iff
      (norm_unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i))
      hL ht (hwidth i) (hchart.1 i)
    rcases hactive i with ha | ha
    · have he : ‖((radialLength (by omega) (normalizedAngle m u)
          (modelRadii m β u) i : ℝ) : ℂ) *
          unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i) +
          unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i) *
            ((((s i * Lens.width (radialLength (by omega) (normalizedAngle m u)
              (modelRadii m β u) i) (ν i) : ℝ) : ℂ) + (ν i : ℂ) * I))‖ = 2 := by
        have he := ha.1
        unfold plusCrossingVector at he
        rw [hinc i] at he
        simpa only [radialIncrement, heightParameter, map_zero, add_zero,
          LensClosure.increment] using he
      have hsend : s i = 1 := hp.mp he
      unfold activeHalfSign
      rw [if_pos ha.1, hsend]
    · have he : ‖((radialLength (by omega) (normalizedAngle m u)
          (modelRadii m β u) i : ℝ) : ℂ) *
          unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i) -
          unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i) *
            ((((s i * Lens.width (radialLength (by omega) (normalizedAngle m u)
              (modelRadii m β u) i) (ν i) : ℝ) : ℂ) + (ν i : ℂ) * I))‖ = 2 := by
        have he := ha.2
        unfold minusCrossingVector at he
        rw [hinc i] at he
        simpa only [radialIncrement, heightParameter, map_zero, add_zero,
          LensClosure.increment] using he
      have hsend : s i = -1 := hn.mp he
      unfold activeHalfSign
      rw [if_neg (ne_of_lt ha.1), hsend]
  have hsend (i : Fin m) : s i = 1 ∨ s i = -1 := by
    rw [hsactive i]
    unfold activeHalfSign
    split <;> simp
  have hind := activeConstraintDifferentialsIndependent_of_chart (show 2 ≤ m by omega)
    (normalizedAngle m u) s ν (modelRadii m β u)
    (average (actualCenter m β u)) g hchart hhalf hsend hpos hsmall hwidth
    (fun j => by rw [hsat j]; norm_num)
  have hsfun : s = fun i => activeHalfSign (by omega) (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u) i := funext hsactive
  have hbase' := hbase
  rw [hsfun] at hind hbase'
  rw [hbase'] at hind
  exact hind

end
end StructuralNote.MatchingActivityActualActiveGradientIndependence
