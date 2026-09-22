import StructuralNote.MatchingActivityCrossingEndpointGraph
import StructuralNote.MatchingActivityActualChartSelection

/-! The one-sided endpoint graph through an actual normalized maximizer. -/

namespace StructuralNote.MatchingActivityCrossingEndpointActual

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityNonlocal
open MatchingActivityCrossingEndpointGraph MatchingActivityCrossingVariationGraph
open MatchingActivityCrossingExclusivity
open MatchingActivityActualChartSelection
open StrongPointwiseCoordinates StrongPointwiseSmallness MatchingActivityNonlocalPairs
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open scoped BigOperators Topology ContDiff
noncomputable section

/-- At the physically active crossing, the base lens coordinate is the same
endpoint sign as the actual active word. -/
theorem model_active_crossing_endpoint_variation {m : ℕ} (hm : 8 ≤ m)
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
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤ 10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10)
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1) (i : Fin m)
    (hactive :
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2)) :
    ∃ (s ν : Fin m → ℝ) (ξ : ℝ → ℂ),
      (∀ j, |s j| ≤ 1) ∧
      s i = activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i ∧
      (s i = 1 ∨ s i = -1) ∧
      (∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
      (∀ j, |radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) j -
        LensClosure.midpoint m j| + |ν j| ≤ 1 / 4) ∧
      crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
          (average (actualCenter m β u)) ξ i 0 = normalizedPoint m β u ∧
      ξ 0 = 0 ∧ ContDiffAt ℝ ∞ ξ 0 ∧
      (∀ᶠ t in 𝓝 (0 : ℝ),
        closureFamily (parameters (by omega) (normalizedAngle m u) (sigmaPath s i t) ν
          (modelRadii m β u)) (ξ t) = 0) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), s i * t ≤ 0 →
        DiameterAtMost 2 (crossingPath (by omega) (normalizedAngle m u) s ν
          (modelRadii m β u) (average (actualCenter m β u)) ξ i t)) := by
  obtain ⟨hθ, hstep, _⟩ := model_nonlocal_smallness hm h hz hbounds hbudget
    hsmallB hsmallC hsmallR
  have hhalf : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u h.periodic j)
  have hr (j : Fin m) : 3 / 4 ≤ modelRadii m β u j ∧ modelRadii m β u j ≤ 1 := by
    rw [hsat j]
    norm_num
  have hd : DiameterAtMost 2 (vertices (by omega) (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u)) := by
    rw [model_vertices (by omega) β u h.periodic]
    exact model_diameter h hz
  obtain ⟨s, ν, hs, hν, hinc, hw, hsmall, hz0⟩ := exists_base_coordinates hm
    (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u) hhalf
    (actualCenter_halfPeriodic (by omega) β u h.periodic) hd hr hθ hstep
  have hL (j : Fin m) : 0 < radialLength (by omega) (normalizedAngle m u)
      (modelRadii m β u) j := by
    unfold radialLength
    apply length_pos
    have hφ := (small_half_angle hm (normalizedAngle m u) hθ j).2.1
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (pair_re_ge_one hφ (hr j).1 (hr (nextIndex (by omega) j)).1)
  have ht (j : Fin m) : (ν j) ^ 2 ≤ 4 := by
    have hn : (0 : ℝ) < 1000 * (2 * m : ℝ) := by positivity
    have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
    have hb : |ν j| < 2 := (hν j).trans_lt (by
      apply (div_lt_iff₀ hn).2
      nlinarith)
    nlinarith [(abs_lt.mp hb).1, (abs_lt.mp hb).2]
  have hp := Lens.rotated_plus_active_iff
    (norm_unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i))
    (hL i) (ht i) (hw i) (hs i)
  have hn := Lens.rotated_minus_active_iff
    (norm_unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i))
    (hL i) (ht i) (hw i) (hs i)
  have hsi : s i = activeHalfSign (by omega) (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u) i := by
    rcases hactive with ha | ha
    · have he : ‖((radialLength (by omega) (normalizedAngle m u)
          (modelRadii m β u) i : ℝ) : ℂ) *
          unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i) +
          unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i) *
            ((((s i * Lens.width (radialLength (by omega) (normalizedAngle m u)
              (modelRadii m β u) i) (ν i) : ℝ) : ℂ) + (ν i : ℂ) * Complex.I))‖ = 2 := by
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
              (modelRadii m β u) i) (ν i) : ℝ) : ℂ) + (ν i : ℂ) * Complex.I))‖ = 2 := by
        have he := ha.2
        unfold minusCrossingVector at he
        rw [hinc i] at he
        simpa only [radialIncrement, heightParameter, map_zero, add_zero,
          LensClosure.increment] using he
      have hsend : s i = -1 := hn.mp he
      unfold activeHalfSign
      rw [if_neg (ne_of_lt ha.1), hsend]
  have hi : s i = 1 ∨ s i = -1 := by
    rw [hsi]
    unfold activeHalfSign
    split <;> simp
  have hbase : radialConfiguration (by omega) (normalizedAngle m u) s ν
      (modelRadii m β u) 0 (average (actualCenter m β u)) = normalizedPoint m β u := by
    rw [radialConfiguration_base (by omega) _ _ _ _ _
      (actualCenter_halfPeriodic (by omega) β u h.periodic) hinc,
      model_vertices (by omega) β u h.periodic]
  have hfar (j k : Fin (2 * m)) (hk₁ : k.val ≠ m - 1) (hk₂ : k.val ≠ m)
      (hk₃ : k.val ≠ m + 1) :
      ‖radialConfiguration (by omega) (normalizedAngle m u) s ν (modelRadii m β u) 0
          (average (actualCenter m β u)) (cyclicAdvance j k.val) -
        radialConfiguration (by omega) (normalizedAngle m u) s ν (modelRadii m β u) 0
          (average (actualCenter m β u)) j‖ < 2 := by
    rw [hbase, ← model_normalized_distance h]
    exact model_nonlocal_offset_strict hm k.isLt ⟨hk₁, hk₂, hk₃⟩ h hz hbounds hbudget
      hsmallB hsmallC hsmallR hsmallb j
  obtain ⟨ξ, hξ0, hξ, hp0, hroot, hfeas⟩ :=
    exists_feasible_endpoint_sigma_path (show 2 ≤ m by omega)
      (normalizedAngle m u) s ν (modelRadii m β u) (average (actualCenter m β u)) i
      hhalf hs hi hsat hsmall hz0 hw hfar
  refine ⟨s, ν, ξ, hs, hsi, hi, hν, hsmall, ?_, hξ0, hξ, hroot, ?_⟩
  · exact hp0.trans hbase
  · exact hfeas.mono fun _ ht hdir => (ht hdir).1

end
end StructuralNote.MatchingActivityCrossingEndpointActual
