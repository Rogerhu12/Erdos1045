import StructuralNote.MatchingActivityCrossingVariationGraph
import StructuralNote.MatchingActivityCrossingExclusivity

/-! The two-sided crossing-control graph at an actually inactive pair of
adjacent crossing constraints.  The center in this file is always the
physical `actualCenter`; the corrected `polarCenter` appears only in the
energy budget used to obtain the coordinate bounds. -/

namespace StructuralNote.MatchingActivityCrossingVariationActual

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityNonlocal
open MatchingActivityCrossingExclusivity MatchingActivityCrossingVariationGraph
open StrongPointwiseCoordinates StrongPointwiseSmallness MatchingActivityNonlocalPairs
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open scoped BigOperators Topology ContDiff
noncomputable section

/-- Strict slack in both adjacent crossing inequalities is exactly the
interior condition needed for a two-sided `sigma` variation. -/
theorem sigma_interior_of_strict_crossings {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (r s ν : Fin m → ℝ) (c : Fin (2 * m) → ℂ)
    (hs : ∀ j, |s j| ≤ 1)
    (hinc : ∀ j, difference (by omega) c (halfIndex j) = radialIncrement hm θ s ν r 0 j)
    (hL : ∀ j, 0 < radialLength hm θ r j)
    (ht : ∀ j, (ν j) ^ 2 ≤ 4)
    (hw : ∀ j, 0 < Lens.width (radialLength hm θ r j) (ν j))
    (i : Fin m)
    (hplus : ‖plusCrossingVector hm θ r c i‖ < 2)
    (hminus : ‖minusCrossingVector hm θ r c i‖ < 2) :
    |s i| < 1 := by
  have hp := Lens.rotated_plus_active_iff (norm_unit (radialPhase hm θ r i))
    (hL i) (ht i) (hw i) (hs i)
  have hn := Lens.rotated_minus_active_iff (norm_unit (radialPhase hm θ r i))
    (hL i) (ht i) (hw i) (hs i)
  have hsp : s i ≠ 1 := by
    intro hsi
    have he := hp.mpr hsi
    have he' : ‖plusCrossingVector hm θ r c i‖ = 2 := by
      unfold plusCrossingVector
      rw [hinc i]
      simpa only [radialIncrement, heightParameter, map_zero, add_zero,
        LensClosure.increment] using he
    exact (ne_of_lt hplus) he'
  have hsm : s i ≠ -1 := by
    intro hsi
    have he := hn.mpr hsi
    have he' : ‖minusCrossingVector hm θ r c i‖ = 2 := by
      unfold minusCrossingVector
      rw [hinc i]
      simpa only [radialIncrement, heightParameter, map_zero, add_zero,
        LensClosure.increment] using he
    exact (ne_of_lt hminus) he'
  have hb := abs_le.mp (hs i)
  exact abs_lt.mpr ⟨lt_of_le_of_ne hb.1 (Ne.symm hsm), lt_of_le_of_ne hb.2 hsp⟩

def HasActualInactiveCrossingVariation {m : ℕ} (hm : 0 < m)
    (β : ℂ) (u : ℕ → ℂ) (i : Fin m) : Prop :=
  ∃ (s ν : Fin m → ℝ) (ξ : ℝ → ℂ),
    (∀ j, |s j| ≤ 1) ∧ |s i| < 1 ∧
    (∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ))) ∧
    (∀ j, |radialPhase hm (normalizedAngle m u) (modelRadii m β u) j - LensClosure.midpoint m j| +
      |ν j| ≤ 1 / 4) ∧
    crossingPath hm (normalizedAngle m u) s ν (modelRadii m β u)
        (average (actualCenter m β u)) ξ i 0 = normalizedPoint m β u ∧
    ξ 0 = 0 ∧ ContDiffAt ℝ ∞ ξ 0 ∧
    ContDiffAt ℝ ∞ (crossingPath hm (normalizedAngle m u) s ν
      (modelRadii m β u) (average (actualCenter m β u)) ξ i) 0 ∧
    (∃ v : Points (2 * m), ∀ j, HasDerivAt
      (fun t => crossingPath hm (normalizedAngle m u) s ν (modelRadii m β u)
        (average (actualCenter m β u)) ξ i t j) (v j) 0) ∧
    (∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters hm (normalizedAngle m u) (sigmaPath s i t) ν
        (modelRadii m β u)) (ξ t) = 0 ∧
      DiameterAtMost 2 (crossingPath hm (normalizedAngle m u) s ν (modelRadii m β u)
        (average (actualCenter m β u)) ξ i t) ∧
      ∀ j : Fin (2 * m),
        ‖crossingPath hm (normalizedAngle m u) s ν (modelRadii m β u)
            (average (actualCenter m β u)) ξ i t (halfTurn hm j) -
          crossingPath hm (normalizedAngle m u) s ν (modelRadii m β u)
            (average (actualCenter m β u)) ξ i t j‖ = 2)

/-- At an actual normalized maximizer whose matching radii have already been
proved equal to one, strict slack in both crossings at a site produces a
genuine two-sided feasible local graph through the same configuration. -/
theorem model_inactive_crossing_variation {m : ℕ} (hm : 8 ≤ m)
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
    (hplus : ‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i‖ < 2)
    (hminus : ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i‖ < 2) :
    HasActualInactiveCrossingVariation (by omega) β u i := by
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
  have hi : |s i| < 1 := sigma_interior_of_strict_crossings (by omega)
    (normalizedAngle m u) (modelRadii m β u) s ν (actualCenter m β u)
    hs hinc hL ht hw i hplus hminus
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
  obtain ⟨ξ, hξ0, hξ, hp0, hp, hv, hfeas⟩ := exists_feasible_sigma_path (show 2 ≤ m by omega)
    (normalizedAngle m u) s ν (modelRadii m β u) (average (actualCenter m β u)) i
    hhalf hs hi hsat hsmall hz0 hw hfar
  refine ⟨s, ν, ξ, hs, hi, hν, hsmall, ?_, hξ0, hξ, hp, hv, hfeas⟩
  exact hp0.trans hbase

end
end StructuralNote.MatchingActivityCrossingVariationActual
