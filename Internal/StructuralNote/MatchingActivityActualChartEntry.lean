import StructuralNote.MatchingActivityActualChartSelection

/-! Corollary 9.2: a sufficiently large actual even-order maximizer, in its
mean-angle and mean-center gauge, is the fixed-Schur configuration selected by
its actual active crossing word. -/

namespace StructuralNote.MatchingActivityActualChartEntry

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open CommonDomainClosure CommonDomainRadius
open MatchingActivityRadialIntegration MatchingActivityRadialModelEnergy
open MatchingActivityNonlocalPairs MatchingActivityRadialActual
open MatchingActivityRadialGeometry MatchingActivityCrossingExclusivity
open MatchingActivityCrossingVariationSaturation
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongBudgetConsequences
open StrongObjectiveEstimate StrongPointwiseSteps
open NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate DiscreteEnergy
open ActualCrossingGeometry SolScalarGap
open FixedSchurLinear FixedSchurProjectionDomain FixedSchurEdgeGeometry
open FixedSchurChart FixedSchurLogBoundedRepresentation
open MatchingActivityActualChart MatchingActivityActualChartSelection
open scoped BigOperators Topology
noncomputable section

/-- Matching saturation identifies the mean-center normalized point with the
physical fixed-Schur vertex. -/
theorem normalizedPoint_meanGauge_eq_vertex {m : ℕ} (hm : 0 < m)
    (β : ℂ) (u : ℕ → ℂ) (hu : Function.Periodic u (2 * m))
    (hsat : ∀ i : Fin m, modelRadii m β u i = 1) :
    (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      FixedSchurEdgeGeometry.vertex (normalizedAngle m u)
        (centerZero (actualCenter m β u)) := by
  funext j
  rw [normalizedPoint_decomposition]
  have hr : PolarRepresentation.radius m ‖β‖ u j = 1 := by
    rw [← radiusFull_model hm β u hu]
    unfold radiusFull
    exact hsat _
  rw [hr]
  simp only [Complex.ofReal_one, one_mul, FixedSchurEdgeGeometry.vertex,
    centerZero]
  ring

/-- Entry of an actual maximizer into the chosen fixed-Schur chart.  The
returned word is built from the active crossings of the physical
`actualCenter`; the corrected `polarCenter` occurs only in the retained budget.
-/
theorem eventual_actual_maximizer_fixedSchur_entry :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (hm2 : 2 ≤ m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ) (s : SignPattern hm),
        NormalizedRelativeEdgeModel z π α β u η ∧
        (∀ i : Fin m, modelRadii m β u i = 1) ∧
        (∀ k : Fin (2 * m),
          operator (2 * m) (polarConstraint hm β u) k ≠ 0) ∧
        G hm (polarConstraint hm β u) + radialMass m β u +
            residualEnergy (by omega) (polarCenter m β u) +
            realEnergy (by omega) (normalizedAngle m u) ≤
          budgetConstant / (2 * m : ℝ) ^ 2 ∧
        pairEnergy (by omega) (fun j => (normalizedAngle m u j : ℂ)) +
            pairEnergy (by omega)
              (projection hm2 (centerZero (actualCenter m β u))) ≤
          actualChartEnergyConstant / (2 * m : ℝ) ^ 2 ∧
        (∀ j, ‖crossingVector hm2 (normalizedAngle m u)
          (centerZero (actualCenter m β u)) (patternSign s) j‖ = 2) ∧
        constraint (by omega) (centerZero (actualCenter m β u)) =
            coordinate (by omega) s (normalizedAngle m u)
              (projection hm2 (centerZero (actualCenter m β u))) ∧
        centerZero (actualCenter m β u) =
            center (coordinate (by omega) s (normalizedAngle m u)
              (projection hm2 (centerZero (actualCenter m β u))))
              (projection hm2 (centerZero (actualCenter m β u))) ∧
        (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
          FixedSchurChart.configuration (by omega) s (normalizedAngle m u)
            (projection hm2 (centerZero (actualCenter m β u))) := by
  obtain ⟨m₀, h₀⟩ :=
    MatchingActivityCrossingPressure.eventual_diameter_matching_pressure_margin 0
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 eventual_coefficients_small
  obtain ⟨m₂, h₂⟩ := eventually_atTop.1
    MatchingActivitySaturation.eventual_radial_derivative_scales
  obtain ⟨m₃, h₃⟩ := eventually_atTop.1 eventual_crossing_variation_margin
  obtain ⟨m₄, h₄⟩ := eventually_atTop.1
    (eventually_projection_inDomain actualChartEnergyConstant)
  obtain ⟨m₅, h₅⟩ := eventually_atTop.1
    (eventually_representation_of_selected_crossing_log_bounded
      actualConstraintConstant actualConstraintConstant_nonneg)
  let mstar := max (max (max m₀ m₁) (max m₂ m₃)) (max (max m₄ m₅) 8)
  refine ⟨mstar, ?_⟩
  intro m hm z hz
  have hm₀ : m₀ ≤ m := by dsimp [mstar] at hm; omega
  have hm₁ : m₁ ≤ 2 * m := by dsimp [mstar] at hm; omega
  have hm₂ : m₂ ≤ 2 * m := by dsimp [mstar] at hm; omega
  have hm₃ : m₃ ≤ m := by dsimp [mstar] at hm; omega
  have hm₄ : m₄ ≤ m := by dsimp [mstar] at hm; omega
  have hm₅ : m₅ ≤ m := by dsimp [mstar] at hm; omega
  have hm8 : 8 ≤ m := by dsimp [mstar] at hm; omega
  obtain ⟨hmp, π, α, β, u, η, hmodel, hc, _, hpressure, hcombined,
      hbounds, hsat, hpressureMargin⟩ := h₀ m hm₀ z hz
  have hG0 : 0 ≤ G hmp (polarConstraint hmp β u) := gap_nonneg hmp _
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one hmp hmodel hz.1 j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter m β u) :=
    pairEnergy_nonneg (by omega) _
  have hE : 0 ≤ realEnergy (by omega) (normalizedAngle m u) :=
    pairEnergy_nonneg (by omega) _
  have hbudget : radialMass m β u +
      residualEnergy (by omega) (polarCenter m β u) +
      realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hcombined, hG0]
  have hgap : G hmp (polarConstraint hmp β u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hcombined, hτ, hD, hE]
  have hs := h₁ (2 * m) hm₁
  have hd := h₂ (2 * m) hm₂
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs hd
  have hθ := (model_nonlocal_smallness hm8 hmodel hz.1 hbounds hbudget
    hs.2.1 hs.2.2.1 hs.2.2.2.1).1
  have hactive : ∀ i : Fin m,
      (‖plusCrossingVector hmp (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector hmp (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector hmp (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector hmp (normalizedAngle m u) (modelRadii m β u)
            (actualCenter m β u) i‖ = 2) := by
    intro i
    exact model_exactly_one_crossing_active hm8 hmodel hz hbounds hθ hbudget hgap
      hpressure hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hd.2.1 hsat
      (h₃ m hm₃) i
  have hθhalf : HalfPeriodic hmp
      (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal
      (normalizedAngle_halfPeriodic hmp u hmodel.periodic j)
  have hθmean : (∑ j, (normalizedAngle m u j : ℂ)) = 0 := by
    rw [← Complex.ofReal_sum, normalizedAngle_mean_zero hmp u]
    norm_num
  have hC : HalfPeriodic hmp (actualCenter m β u) :=
    actualCenter_halfPeriodic hmp β u hmodel.periodic
  have hC0 : HalfPeriodic hmp (centerZero (actualCenter m β u)) :=
    centerZero_halfPeriodic hmp _ hC
  have hC0mean : (∑ j, centerZero (actualCenter m β u) j) = 0 :=
    centerZero_sum (by omega) _
  have henergy := model_actual_projection_energy (show 2 ≤ m by omega)
    hmodel.periodic hc hbounds hθ hbudget
  have hdom := h₄ m hm₄ (show 2 ≤ m by omega) (normalizedAngle m u)
    (centerZero (actualCenter m β u)) hθhalf hθmean hC0 hC0mean henergy
  have hqbound := model_actual_constraint_log_bound (show 2 ≤ m by omega) hbounds
  let s : SignPattern hmp := activePattern hmp (normalizedAngle m u)
    (modelRadii m β u) (actualCenter m β u)
  have hcross : ∀ j, ‖crossingVector (show 2 ≤ m by omega)
      (normalizedAngle m u) (centerZero (actualCenter m β u))
      (patternSign s) j‖ = 2 := by
    exact selected_crossing_all (show 2 ≤ m by omega) (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u) hθhalf hC hsat hactive
  have hrep := h₅ m hm₅ (show 2 ≤ m by omega) s (normalizedAngle m u)
    (centerZero (actualCenter m β u)) hC0 hC0mean hdom hqbound hcross
  refine ⟨hmp, (show 2 ≤ m by omega), π, α, β, u, η, s, hmodel, hsat,
    (fun k => (hpressureMargin k).2), hcombined, henergy, hcross,
    hrep.1, hrep.2.1, ?_⟩
  rw [normalizedPoint_meanGauge_eq_vertex hmp β u hmodel.periodic hsat]
  exact hrep.2.2

end
end StructuralNote.MatchingActivityActualChartEntry
