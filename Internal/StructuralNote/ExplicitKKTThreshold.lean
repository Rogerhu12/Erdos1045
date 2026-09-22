import StructuralNote.MatchingActivityKKTFinal
import StructuralNote.ExplicitEvenNumerical

/-! Positive KKT certificates at the same concrete cutoff as the even-order
characterization. Every smallness, chart and pressure estimate is supplied
at this order; no eventual-order witness enters the construction. -/

namespace StructuralNote.ExplicitKKTThreshold

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

open MatchingActivityKKTActual MatchingActivityKKTRigidTransport
open MatchingActivityKKTOriginalCertificate MatchingActivityKKTFinal
open ExplicitPressureNumerical

noncomputable section

/-- The unique normalized multiplier family at the concrete even cutoff. -/
theorem actual_maximizer_unique_multipliers {m : ℕ}
    (hN : concreteThreshold ≤ 2 * m) (z : Points (2 * m))
    (hz : ExtremalNormalization.DiameterExtremal z) :
    ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
      (u : ℕ → ℂ) (η : ℝ),
      NormalizedRelativeEdgeModel z π α β u η ∧
      (∀ i : Fin m, modelRadii m β u i = 1) ∧
      ActualKKTConditions hm β u ∧
      HasUniqueActualMultipliers hm β u := by
  have hcrossing : ExplicitMatchingCoordinates.crossingThreshold ≤ 2 * m :=
    (ExplicitFrontNumerical.crossingThreshold_le_concrete
      ExplicitLocalizationNumerical.localizationThreshold_le_concrete).trans hN
  have hword : ExplicitPressureThreshold.activeWordThreshold ≤ 2 * m :=
    (le_max_right _ _).trans hcrossing
  have hs := ExplicitPressureThreshold.coefficients_small ((le_max_left _ _).trans hword)
  have hm8 : 8 ≤ m := by have := hs.1; omega
  have hmatching : ExplicitMatchingCoordinates.matchingThreshold ≤ 2 * m :=
    (le_max_left _ _).trans hcrossing
  have hsaturation : ExplicitMatchingThreshold.saturationThreshold ≤ 2 * m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hmatching)
  have hd := ExplicitMatchingThreshold.derivative_scales ((le_max_right _ _).trans hsaturation)
  have hmargin := ExplicitPressureThreshold.pressure_margin ((le_max_right _ _).trans hword)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs hd
  have hprojection : ExplicitCanonicalEntry.orderThreshold ≤ 2 * m :=
    ExplicitRationalNumerical.canonicalEntryThreshold_le_concrete.trans hN
  have hrepresentation :
      ExplicitCanonicalEntrySelected.representationThreshold actualConstraintConstant ≤ 2 * m :=
    (le_max_right _ _).trans
      (ExplicitRationalNumerical.representationThreshold_le_concrete.trans hN)
  have hgeometry : ExplicitHessianThreshold.orderThreshold ≤ 2 * m :=
    ExplicitRationalNumerical.hessianThreshold_le_concrete.trans hN
  obtain ⟨hmp, π, α, β, u, η, hmodel, hc, _, _, hpressure, hcombined,
      hbounds, hsat, hactive, _⟩ :=
    ExplicitMatchingCoordinates.diameter_crossings_active hz hcrossing
  obtain ⟨hbudget, hgap⟩ :=
    ExplicitMatchingCoordinates.combined_budget_parts hmp hmodel hz.1 hcombined
  have hθ := (model_nonlocal_smallness hm8 hmodel hz.1 hbounds hbudget
    hs.2.1 hs.2.2.1 hs.2.2.2.1).1
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
  have hdom := ExplicitCanonicalEntry.projection_inDomain hprojection (show 2 ≤ m by omega) (normalizedAngle m u)
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
  have hrep := ExplicitCanonicalEntrySelected.selected_chart_representation
    (show 2 ≤ m by omega) hrepresentation s (normalizedAngle m u)
    (centerZero (actualCenter m β u)) hθhalf hθmean hC0 hC0mean hdom hqbound hcross
  let cfg : Points (2 * m) := configuration hmp s (normalizedAngle m u) v
  have hconfig : (fun j => normalizedPoint m β u j -
      average (actualCenter m β u)) = cfg := by
    rw [normalizedPoint_meanGauge_eq_vertex hmp β u hmodel.periodic hsat]
    exact hrep.2.2
  have hgeo := ExplicitHessianThresholdFixedSchurGeometry.geometric_properties hgeometry (show 2 ≤ m by omega) s (normalizedAngle m u) v hdom
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
      nlinarith only [hcsel]
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
      nlinarith only [hcsel]
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
      hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2, hd.2, hd.1, hsat,
      hmargin, hactive⟩
  refine ⟨hmp, π, α, β, u, η, hmodel, hsat, hctx, K, ?_⟩
  intro L
  exact multipliers_unique hmp sHalf (normalizedPoint m β u) hind L K

/-- Transport the normalized family back to the original points and apply
the pointwise strict-positivity theorem. -/
theorem positive_original_certificate {m : ℕ}
    (hN : concreteThreshold ≤ 2 * m) (z : Points (2 * m))
    (hz : ExtremalNormalization.DiameterExtremal z) :
    ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
      (u : ℕ → ℂ) (η : ℝ),
      Nonempty (PositiveOriginalCertificate z hm π α β u η) := by
  obtain ⟨hmp, π, α, β, u, η, hmodel, _, ctx, K, _⟩ :=
    actual_maximizer_unique_multipliers hN z hz
  have hdisc : 0 < discriminant z := by
    rw [← WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz]
    exact WholeBoxLowerBound.diameterMaximum_pos (by have := ctx.large; omega)
  have hzinj : Function.Injective z := HullGeometry.injective_of_discriminant_pos hdisc
  obtain ⟨L, hmatching, hcrossing⟩ :=
    exists_relabeledMultipliers_of_model hmp hmodel hzinj K
  have hactive := model_actual_active_edges_exact hmp hmodel hz ctx
  have hind := model_relabeled_independent hmp hmodel hz ctx
  have hunique (L' : RelabeledMultipliers hmp
      (fun i => activeHalfSign hmp (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i) π z) : L' = L :=
    relabeled_multipliers_unique hmp _ π z hind L' L
  let C : OriginalCertificate z hmp π α β u η :=
    ⟨hmodel, ctx, K, L, hmatching, hcrossing, hactive, hind, hunique⟩
  exact ⟨hmp, π, α, β, u, η, ⟨OriginalCertificate.withPositive C hz⟩⟩

end
end StructuralNote.ExplicitKKTThreshold
