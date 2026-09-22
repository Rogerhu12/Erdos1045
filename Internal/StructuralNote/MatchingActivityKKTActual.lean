import StructuralNote.MatchingActivityKKTAnalytic
import StructuralNote.MatchingActivityActualActiveGradientIndependence
import StructuralNote.MatchingActivityActualChartEntry

/-! Existence and uniqueness of the normalized KKT multipliers at every
sufficiently large actual diameter maximizer.  The active crossing word is
read from the physical center. -/

namespace StructuralNote.MatchingActivityKKTActual

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
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
open ActualCrossingGeometry SolScalarGap
open FixedSchurLinear FixedSchurProjectionDomain FixedSchurEdgeGeometry
open FixedSchurChart FixedSchurChartGeometry FixedSchurLogBoundedRepresentation
open MatchingActivityActualChart MatchingActivityActualChartSelection
open MatchingActivityActualChartEntry
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveGradientIndependence
open MatchingActivityActualActiveGradientIndependence
open MatchingActivityKKTAnalytic
open scoped BigOperators Topology

noncomputable section

def ActualMultipliers {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) :=
  Multipliers hm
    (fun i => activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i)
    (normalizedPoint m β u)

/-- The normalized KKT multiplier is unique whenever it exists. -/
def HasUniqueActualMultipliers {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : Prop :=
  ∃ K : ActualMultipliers hm β u, ∀ L : ActualMultipliers hm β u, L = K

structure ActualKKTConditions {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ) : Prop where
  large : 8 ≤ m
  bounds : PointwiseBounds hm β u
  budget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
    realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2
  gap : G hm (polarConstraint hm β u) ≤ budgetConstant / (2 * m : ℝ) ^ 2
  pressure : ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64
  smallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000
  smallC : physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000
  smallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤
    10 - Real.pi ^ 2
  smallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10
  smallD : MatchingActivityRadialDiameterError.diameterStepConstant /
    (2 * m : ℝ) ≤ 1 / 2
  smallG : MatchingActivityRadialGradient.configurationStepConstant /
    (2 * m : ℝ) ≤ 1 / 2
  gain : 0 < MatchingActivityRadialLowerBound.lowerBound (2 * m)
  saturated : ∀ i : Fin m, modelRadii m β u i = 1
  margin :
    8 * (31 * Real.pi / 64) +
        (9 / 2 : ℝ) * MatchingActivityRadialModelCenterError.centerErrorConstant *
          Real.sqrt (1 + Real.log (2 * m : ℕ)) <
      ((Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 -
        budgetConstant / 2) / 8
  active : ∀ i : Fin m,
    (‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ = 2 ∧
      ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ < 2) ∨
    (‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ < 2 ∧
      ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i‖ = 2)

theorem edgeConstraint_sub_const {n : ℕ} (x : Points n) (a : ℂ) (p q : Fin n) :
    edgeConstraint x p q = edgeConstraint (fun j => x j - a) p q := by
  unfold edgeConstraint
  congr 1
  ring_nf

/-- Every sufficiently large actual extremizer has a unique normalized KKT
multiplier family for all matching and physically selected crossing edges. -/
theorem eventual_actual_maximizer_unique_multipliers :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z π α β u η ∧
        (∀ i : Fin m, modelRadii m β u i = 1) ∧
        ActualKKTConditions hm β u ∧
        HasUniqueActualMultipliers hm β u := by
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
  obtain ⟨m₆, h₆⟩ := eventually_atTop.1 eventual_geometric_properties
  let mstar := max (max (max m₀ m₁) (max m₂ m₃))
    (max (max m₄ m₅) (max m₆ 8))
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
  let v := projection (show 2 ≤ m by omega) (centerZero (actualCenter m β u))
  have hcross : ∀ j, ‖crossingVector (show 2 ≤ m by omega)
      (normalizedAngle m u) (centerZero (actualCenter m β u))
      (patternSign s) j‖ = 2 := by
    exact selected_crossing_all (show 2 ≤ m by omega) (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u) hθhalf hC hsat hactive
  have hrep := h₅ m hm₅ (show 2 ≤ m by omega) s (normalizedAngle m u)
    (centerZero (actualCenter m β u)) hC0 hC0mean hdom hqbound hcross
  let cfg : Points (2 * m) := configuration hmp s (normalizedAngle m u) v
  have hconfig : (fun j => normalizedPoint m β u j -
      average (actualCenter m β u)) = cfg := by
    rw [normalizedPoint_meanGauge_eq_vertex hmp β u hmodel.periodic hsat]
    exact hrep.2.2
  have hgeo := h₆ m hm₆ (show 2 ≤ m by omega) s (normalizedAngle m u) v hdom
  have hcfg (j : Fin (2 * m)) :
      cfg j = normalizedPoint m β u j - average (actualCenter m β u) := by
    exact (congrFun hconfig j).symm
  have hedge (p q : Fin (2 * m)) :
      edgeConstraint (normalizedPoint m β u) p q = edgeConstraint cfg p q := by
    unfold edgeConstraint
    rw [hcfg p, hcfg q]
    congr 1
    ring_nf
  let sHalf : Fin m → ℝ := fun i => activeHalfSign hmp (normalizedAngle m u)
    (modelRadii m β u) (actualCenter m β u) i
  have hsHalf (i : Fin m) :
      sHalf i = patternSign s (CommonClosureEnergy.halfIndex i) := by
    dsimp only [sHalf, s]
    rw [patternSign_activePattern, activeRaw_halfIndex]
  have hmatch (i : Fin m) : matchingConstraint hmp (normalizedPoint m β u) i = 4 := by
    unfold matchingConstraint
    rw [hedge]
    have hn := hgeo.coordinates.matching (CommonClosureEnergy.halfIndex i)
    change ‖cfg (CommonClosureEnergy.halfIndex i) -
      cfg (halfTurn hmp (CommonClosureEnergy.halfIndex i))‖ = 2 at hn
    unfold edgeConstraint matchingFirst matchingSecond
    rw [hn]
    norm_num
  have hselected (i : Fin m) :
      selectedConstraint hmp sHalf (normalizedPoint m β u) i = 4 := by
    unfold selectedConstraint
    rw [hedge]
    have hcsel := hgeo.coordinates.selected (CommonClosureEnergy.halfIndex i)
    have hCchart : HalfPeriodic hmp
        (center (coordinate hmp s (normalizedAngle m u) v) v) :=
      center_halfPeriodic (show 2 ≤ m by omega) _ _
        hgeo.coordinates.antiperiodic hdom.2.2.1.1
    rcases patternSign_is_sign s (CommonClosureEnergy.halfIndex i) with hp | hn
    · have hsi : sHalf i = 1 := (hsHalf i).trans hp
      have hv := crossingVector_eq_vertex_sub_plus (show 2 ≤ m by omega)
        (normalizedAngle m u) (center (coordinate hmp s (normalizedAngle m u) v) v)
        (patternSign s) hθhalf hCchart (CommonClosureEnergy.halfIndex i) hp
      rw [hv] at hcsel
      unfold edgeConstraint selectedFirst selectedSecond
      simp only [hsi, if_pos]
      change ‖cfg (successor (by omega) (CommonClosureEnergy.halfIndex i)) -
        cfg (halfTurn hmp (CommonClosureEnergy.halfIndex i))‖ ^ 2 = 4
      change ‖cfg (successor (by omega) (CommonClosureEnergy.halfIndex i)) -
        cfg (halfTurn hmp (CommonClosureEnergy.halfIndex i))‖ = 2 at hcsel
      nlinarith
    · have hsi : sHalf i = -1 := (hsHalf i).trans hn
      have hv := crossingVector_eq_vertex_sub_minus (show 2 ≤ m by omega)
        (normalizedAngle m u) (center (coordinate hmp s (normalizedAngle m u) v) v)
        (patternSign s) hθhalf hCchart (CommonClosureEnergy.halfIndex i) hn
      rw [hv] at hcsel
      unfold edgeConstraint selectedFirst selectedSecond
      simp only [hsi, if_neg (by norm_num : (-1 : ℝ) ≠ 1)]
      change ‖cfg (CommonClosureEnergy.halfIndex i) -
        cfg (halfTurn hmp (successor (by omega) (CommonClosureEnergy.halfIndex i)))‖ ^ 2 = 4
      change ‖cfg (CommonClosureEnergy.halfIndex i) -
        cfg (halfTurn hmp (successor (by omega) (CommonClosureEnergy.halfIndex i)))‖ = 2 at hcsel
      nlinarith
  have hx := model_normalizedPoint_extremal hmodel hz
  have hxinj : Function.Injective (normalizedPoint m β u) := by
    intro i j hij
    apply hgeo.injective
    change cfg i = cfg j
    rw [hcfg i, hcfg j, hij]
  have hgraph (p q : Fin (2 * m)) :
      ‖normalizedPoint m β u p - normalizedPoint m β u q‖ = 2 ↔
        WordEdge (patternSign s) p q := by
    rw [show normalizedPoint m β u p - normalizedPoint m β u q = cfg p - cfg q by
      rw [hcfg p, hcfg q]; ring_nf]
    exact hgeo.graph p q
  have hdisc : 1 ≤ discriminant (normalizedPoint m β u) := by
    rw [model_discriminant_normalizedPoint hmodel]
    have hn : (1 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * m by omega)
    exact (one_le_pow₀ hn).trans (hz.discriminant_ge (by omega))
  have hind : ActiveConstraintDifferentialsIndependent hmp sHalf
      (normalizedPoint m β u) := by
    simpa only [sHalf] using
      model_activeConstraintDifferentialsIndependent hm8 hmodel hz.1 hbounds hbudget
        hs.2.1 hs.2.2.1 hs.2.2.2.1 hsat hactive
  have hsigma : Antiperiodic hmp (patternSign s) := patternSign_antiperiodic s
  have hhalf (i : Fin m) : sHalf i = patternSign s (halfIndex i) := hsHalf i
  obtain ⟨K⟩ := exists_multipliers (show 2 ≤ m by omega) (patternSign s) hsigma
    sHalf hhalf (normalizedPoint m β u) hx hxinj hdisc hgraph hmatch hselected hind
  have hctx : ActualKKTConditions hmp β u :=
    ⟨hm8, hbounds, hbudget, hgap, hpressure, hs.2.1, hs.2.2.1,
      hs.2.2.2.1, hs.2.2.2.2, hd.2.1, hd.2.2, hd.1, hsat,
      h₃ m hm₃, hactive⟩
  refine ⟨hmp, π, α, β, u, η, hmodel, hsat, hctx, K, ?_⟩
  intro L
  exact multipliers_unique hmp sHalf (normalizedPoint m β u) hind L K

end
end StructuralNote.MatchingActivityKKTActual
