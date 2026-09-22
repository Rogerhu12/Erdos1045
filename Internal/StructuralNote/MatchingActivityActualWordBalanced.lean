import StructuralNote.MatchingActivityActualWordAlignment
import StructuralNote.MatchingActivityActualChartEntry
import StructuralNote.FixedSchurChartSelection

/-! An arbitrary sufficiently large actual maximizer selects a balanced
physical crossing word. -/

namespace StructuralNote.MatchingActivityActualWordBalanced

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open CommonDomainClosure CommonDomainRadius
open MatchingActivityRadialIntegration MatchingActivityRadialModelEnergy
open MatchingActivityNonlocalPairs MatchingActivityRadialActual
open MatchingActivityRadialGeometry MatchingActivityCrossingExclusivity
open MatchingActivityCrossingVariationSaturation MatchingActivitySaturation
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongBudgetConsequences
open StrongObjectiveEstimate StrongPointwiseSteps
open NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate DiscreteEnergy
open ActualCrossingGeometry SolScalarGap FixedDualClassificationFinite
open FiniteWordClassification
open FixedSchurLinear FixedSchurProjectionDomain FixedSchurEdgeGeometry
open FixedSchurChart FixedSchurLogBoundedRepresentation FixedSchurChartSelection
open MatchingActivityActualChart MatchingActivityActualChartSelection
open MatchingActivityActualChartEntry MatchingActivityActualWordAlignment
open scoped BigOperators Topology
noncomputable section

/-- Translation preserves the diameter-extremal problem. -/
theorem diameterExtremal_sub_const {n : ℕ} (x : Points n)
    (hx : ExtremalNormalization.DiameterExtremal x) (a : ℂ) :
    ExtremalNormalization.DiameterExtremal (fun j => x j - a) := by
  have hdiam : DiameterAtMost 2 (fun j => x j - a) := by
    intro i j
    calc
      ‖(x i - a) - (x j - a)‖ = ‖x i - x j‖ := by
        congr 1
        ring
      _ ≤ 2 := hx.1 i j
  have hdisc : discriminant (fun j => x j - a) = discriminant x := by
    have ha := Configuration.discriminant_affine x (-a) 1
    simp only [norm_one, one_pow, one_mul] at ha
    calc
      _ = discriminant (fun j => -a + x j) := by
        congr 1
        funext j
        ring
      _ = _ := ha
  refine ⟨hdiam, ?_⟩
  intro w hw
  rw [hdisc]
  exact hx.2 w hw

/-- Corollary 9.2 with finite-word selection: the word is formed from the
actual physical crossings, the corrected polar center is used only in the
pressure budget, and the selected word is balanced. -/
theorem eventual_actual_maximizer_balanced_entry :
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
            (projection hm2 (centerZero (actualCenter m β u))) ∧
        deficit hm s ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
        BalancedWord hm s := by
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
  let B := actualChartEnergyConstant + 1
  have hB : 0 ≤ B := by dsimp [B]; linarith [actualChartEnergyConstant_nonneg]
  obtain ⟨m₆, h₆⟩ := eventually_atTop.1
    (eventually_extremal_chart_word_balanced B hB budgetConstant)
  let mstar := max (max (max m₀ m₁) (max m₂ m₃)) (max (max m₄ m₅) (max m₆ 8))
  refine ⟨mstar, ?_⟩
  intro m hm z hz
  have hm₀ : m₀ ≤ m := by dsimp [mstar] at hm; omega
  have hm₁ : m₁ ≤ 2 * m := by dsimp [mstar] at hm; omega
  have hm₂ : m₂ ≤ 2 * m := by dsimp [mstar] at hm; omega
  have hm₃ : m₃ ≤ m := by dsimp [mstar] at hm; omega
  have hm₄ : m₄ ≤ m := by dsimp [mstar] at hm; omega
  have hm₅ : m₅ ≤ m := by dsimp [mstar] at hm; omega
  have hm₆ : m₆ ≤ m := by dsimp [mstar] at hm; omega
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
  have hθhalf : HalfPeriodic hmp (fun j => (normalizedAngle m u j : ℂ)) := by
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
  have hdef : deficit hmp s ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    dsimp [s]
    exact model_activePattern_deficit_le_gap hm8 hmodel hz hbounds hθ hbudget hgap
      hpressure hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hd.2.1 hsat
      (h₃ m hm₃) hactive
  have henergy' : pairEnergy (by omega) (fun j => (normalizedAngle m u j : ℂ)) +
      pairEnergy (by omega) (projection (show 2 ≤ m by omega)
        (centerZero (actualCenter m β u))) ≤ B ^ 2 / (2 * m : ℝ) ^ 2 := by
    apply henergy.trans
    have hden : 0 ≤ (2 * m : ℝ) ^ 2 := sq_nonneg _
    apply div_le_div_of_nonneg_right _ hden
    dsimp [B]
    nlinarith [actualChartEnergyConstant_nonneg]
  have hconfig : (fun j => normalizedPoint m β u j - average (actualCenter m β u)) =
      FixedSchurChart.configuration (by omega) s (normalizedAngle m u)
        (projection (show 2 ≤ m by omega) (centerZero (actualCenter m β u))) := by
    rw [normalizedPoint_meanGauge_eq_vertex hmp β u hmodel.periodic hsat]
    exact hrep.2.2
  have hchartExt : ExtremalNormalization.DiameterExtremal
      (FixedSchurChart.configuration (by omega) s (normalizedAngle m u)
        (projection (show 2 ≤ m by omega) (centerZero (actualCenter m β u)))) := by
    rw [← hconfig]
    exact diameterExtremal_sub_const (normalizedPoint m β u)
      (MatchingActivitySaturation.model_normalizedPoint_extremal hmodel hz)
      (average (actualCenter m β u))
  have hbalanced : BalancedWord hmp s :=
    h₆ m hm₆ (show 2 ≤ m by omega) s (normalizedAngle m u)
      (projection (show 2 ≤ m by omega) (centerZero (actualCenter m β u)))
      hdom henergy' hdef hchartExt
  refine ⟨hmp, (show 2 ≤ m by omega), π, α, β, u, η, s, hmodel, hsat,
    (fun k => (hpressureMargin k).2), hcombined, henergy, hcross,
    hrep.1, hrep.2.1, hconfig, hdef, hbalanced⟩

end
end StructuralNote.MatchingActivityActualWordBalanced
