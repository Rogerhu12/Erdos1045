import StructuralNote.MatchingActivityCrossingEndpointPressure

/-! The physical active crossing word agrees with the sign of the corrected
polar pressure. -/

namespace StructuralNote.MatchingActivityActualWordPressure

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
open CommonClosureEnergy MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityNonlocal
open MatchingActivityNonlocalPairs
open MatchingActivityCrossingVariationGraph MatchingActivityCrossingVariationDerivative
open MatchingActivityCrossingEndpointActual MatchingActivityCrossingEndpointPressure
open MatchingActivityActualChartSelection MatchingActivityCrossingExclusivity
open MatchingActivityRadialSmallness MatchingActivityRadialCenterFirst
open MatchingActivityRadialModelCenterError MatchingActivityRadialDiameterError
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongPointwiseSteps
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open MatchingActivitySaturation MatchingActivityCrossingVariationSaturation SolScalarGap
open scoped BigOperators Topology ContDiff
noncomputable section

/-- The sign of the physically active first-half crossing equals the strict
sign of the midpoint pressure. -/
theorem model_activeHalfSign_pressure_pos {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hgap : G (m := m) (by omega) (polarConstraint (by omega) β u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤
      31 * Real.pi / 64)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : StrongPointwiseRadial.radialErrorConstant / (2 * m : ℝ) ≤
      10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10)
    (hsmallD : diameterStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1)
    (hmargin :
      8 * (31 * Real.pi / 64) +
          (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ)) <
        ((Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 -
          budgetConstant / 2) / 8)
    (i : Fin m)
    (hactive :
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
      (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
        ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2)) :
    0 < activeHalfSign (by omega) (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i *
      operator (2 * m) (polarConstraint (by omega) β u) (halfIndex i) := by
  obtain ⟨s, ν, ξ, hs, hsi, hi, hν, hsmall, hbase, hξ0, hξ, hroot, hfeas⟩ :=
    model_active_crossing_endpoint_variation hm h hz.1 hbounds hbudget hsmallB hsmallC
      hsmallR hsmallb hsat i hactive
  let D := centerFirst (modelDiameter m β u) (actualCenter m β u)
    (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i)
  let g := operator (2 * m) (polarConstraint (by omega) β u) (halfIndex i)
  have hsmallC' : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2 := by
    calc
      _ = 2 * (physicalStepConstant / (2 * m : ℝ)) := by ring
      _ ≤ 2 * (1 / 1000 : ℝ) := mul_le_mul_of_nonneg_left hsmallC (by norm_num)
      _ ≤ _ := by norm_num
  have hpressureSign : 0 < D * g := by
    exact actual_crossing_derivative_pressure_sign hm h.periodic hbounds hθ hbudget hgap
      hpressure hsmallD hsmallC' hsat hmargin s ν ξ i hs hν hsmall hξ0 hξ hroot
  have hinj : Function.Injective (normalizedPoint m β u) := by
    apply HullGeometry.injective_of_discriminant_pos
    rw [MatchingActivitySaturation.model_discriminant_normalizedPoint h]
    exact (pow_pos (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ)) (2 * m)).trans_le
      (hz.discriminant_ge (by omega))
  have hdc : GeometricRelativeRemainder.configuration (modelDiameter m β u)
      (actualCenter m β u) = normalizedPoint m β u := by
    funext j
    simp only [GeometricRelativeRemainder.configuration, normalizedPoint_decomposition,
      modelDiameter]
  have hd := crossingPath_log_derivative (show 2 ≤ m by omega) (normalizedAngle m u)
    s ν (modelRadii m β u) (average (actualCenter m β u)) i ξ hsmall hξ0 hξ hroot
    (modelDiameter m β u) (actualCenter m β u) (hbase.trans hdc.symm) (hdc ▸ hinj)
  have hv (j : Fin (2 * m)) : HasDerivAt
      (fun t => crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
        (average (actualCenter m β u)) ξ i t j)
      (centerVelocity (by omega) (normalizedAngle m u) s ν
        (modelRadii m β u) ξ i j) 0 :=
    crossingPath_hasDerivAt (show 2 ≤ m by omega) (normalizedAngle m u) s ν
      (modelRadii m β u) (average (actualCenter m β u)) i ξ hsmall hξ0 hξ hroot j
  have hinjAdd : ∀ᶠ t in nhds (0 : ℝ), Function.Injective
      (crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
        (average (actualCenter m β u)) ξ i t) :=
    RadialObjectivePrice.eventually_injective_of_hasDerivAt hv (hbase ▸ hinj)
  have hlin : HasDerivAt (fun t : ℝ => -(s i) * t) (-(s i)) 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul (-(s i))
  have htend : Tendsto (fun t : ℝ => -(s i) * t) (nhds 0) (nhds 0) := by
    simpa using hlin.continuousAt.tendsto
  let p : ℝ → Points (2 * m) := fun t =>
    crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
      (average (actualCenter m β u)) ξ i (-(s i) * t)
  have hp0 : p 0 = normalizedPoint m β u := by
    dsimp [p]
    simpa using hbase
  have hsiSq : (s i) ^ 2 = 1 := by
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  have hfeasIn : ∀ᶠ t in nhds (0 : ℝ), 0 ≤ t → DiameterAtMost 2 (p t) := by
    have hpull := htend.eventually hfeas
    filter_upwards [hpull] with t ht ht0
    exact ht (by nlinarith [hsiSq])
  have hinjIn : ∀ᶠ t in nhds (0 : ℝ), Function.Injective (p t) := by
    exact htend.eventually hinjAdd
  have hdIn : HasDerivAt (fun t => Real.log (discriminant (p t)))
      (D * (-(s i))) 0 := by
    have hd0 : HasDerivAt (fun t => Real.log (discriminant
        (crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
          (average (actualCenter m β u)) ξ i t))) D (-(s i) * 0) := by
      simpa only [neg_mul, mul_zero, neg_zero, D] using hd
    dsimp [p, D]
    simpa only [Function.comp_def] using hd0.comp 0 hlin
  have hnonpos : D * (-(s i)) ≤ 0 :=
    oneSided_log_derivative_nonpos
      (MatchingActivitySaturation.model_normalizedPoint_extremal h hz)
      hp0 hfeasIn hinjIn hdIn
  rw [← hsi]
  rcases hi with hi | hi
  · rw [hi] at hnonpos ⊢
    norm_num at hnonpos ⊢
    nlinarith [hpressureSign]
  · rw [hi] at hnonpos ⊢
    norm_num at hnonpos ⊢
    nlinarith [hpressureSign]

end
end StructuralNote.MatchingActivityActualWordPressure
