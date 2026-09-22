import StructuralNote.MatchingActivityKKTRadialResponse
import StructuralNote.MatchingActivityActualWordPressure

/-! Strict positivity of the normalized KKT coefficients at every sufficiently
large actual diameter maximizer. -/

namespace StructuralNote.MatchingActivityKKTPositive

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
open CommonClosureEnergy CommonTangentialParameters CommonFiberGeometry
open MatchingActivityRadialPair MatchingActivityRadialBounds MatchingActivityRadialLens
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityRadialFeasible
open MatchingActivityRadialPath MatchingActivityRadialVelocity MatchingActivityRadialObjectiveFirst
open MatchingActivityRadialSmallness MatchingActivityRadialLowerBound
open MatchingActivityRadialCenterFirst MatchingActivityRadialDiameterError LocalGradient
open MatchingActivityActiveConstraintDifferentials
open MatchingActivityActiveGradientIndependence
open MatchingActivityActiveConstraintCrossingResponse
open MatchingActivityCrossingVariationGraph MatchingActivityCrossingVariationDerivative
open MatchingActivityCrossingEndpointPressure
open MatchingActivityActualWordPressure
open MatchingActivityKKTRadialResponse
open MatchingActivityKKTAnalytic MatchingActivityKKTActual
open MatchingActivityActualChartSelection MatchingActivityCrossingExclusivity
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongPointwiseSteps
open StrongPointwiseRadial MatchingActivityNonlocalPairs
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open scoped BigOperators Topology ContDiff

noncomputable section

theorem crossing_multiplier_pos_of_response {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (x : Points (2 * m))
    (K : Multipliers hm s x) (i : Fin m) (U : Points (2 * m)) (R : ℝ)
    (hM : ∀ j, edgeDifferential x U (matchingFirst j) (matchingSecond hm j) = 0)
    (hX : ∀ j, edgeDifferential x U (selectedFirst hm s j)
      (selectedSecond hm s j) = if j = i then R else 0)
    (hprod : 0 < fderiv ℝ logDiscriminant x U * R) :
    0 < K.crossing i := by
  have hs := K.stationarity U
  simp_rw [hM, mul_zero, Finset.sum_const_zero, zero_add, hX] at hs
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  have hR : R ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hprod
    exact (lt_irrefl 0) hprod
  rw [hs] at hprod
  have hsq : 0 < R ^ 2 := sq_pos_of_ne_zero hR
  nlinarith

theorem matching_multiplier_pos_of_response {m : ℕ} (hm : 0 < m)
    (s : Fin m → ℝ) (x : Points (2 * m))
    (K : Multipliers hm s x) (i : Fin m) (U : Points (2 * m))
    (hM : ∀ j, edgeDifferential x U (matchingFirst j) (matchingSecond hm j) =
      if j = i then 8 else 0)
    (hX : ∀ j, edgeDifferential x U (selectedFirst hm s j)
      (selectedSecond hm s j) = 0)
    (hpos : 0 < fderiv ℝ logDiscriminant x U) :
    0 < K.matching i := by
  have hs := K.stationarity U
  simp_rw [hM, hX, mul_zero, Finset.sum_const_zero, add_zero] at hs
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  linarith

set_option maxHeartbeats 1200000 in
/-- Every normalized KKT coefficient attached to a genuinely active matching
or physically selected crossing is strictly positive. -/
theorem model_actual_multipliers_positive {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (ctx : ActualKKTConditions (show 0 < m by omega) β u)
    (K : ActualMultipliers (show 0 < m by omega) β u) :
    ∀ i : Fin m, 0 < K.matching i ∧ 0 < K.crossing i := by
  obtain ⟨hθ, hstep, _⟩ := model_nonlocal_smallness hm h hz.1 ctx.bounds ctx.budget
    ctx.smallB ctx.smallC ctx.smallR
  obtain ⟨s, ν, g, hchart, hbase, hν⟩ := model_feasible_radial_chart hm h hz.1
    ctx.bounds ctx.budget ctx.smallB ctx.smallC ctx.smallR ctx.smallb
  have hhalf : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u h.periodic j)
  have hr (j : Fin m) : 3 / 4 ≤ modelRadii m β u j ∧ modelRadii m β u j ≤ 1 := by
    rw [ctx.saturated j]
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
          LensClosure.midpoint m j| + |ν j| ≤ 1 / 4 := by
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
  have ht (j : Fin m) : (ν j) ^ 2 < 4 := by
    have hb := hν j
    have hlt : |ν j| < 2 := hb.trans_lt (by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m : ℝ))).2
      have hmR : (8 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith)
    nlinarith [(abs_lt.mp hlt).1, (abs_lt.mp hlt).2]
  have hsactive (i : Fin m) : s i = activeHalfSign (by omega)
      (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u) i := by
    have hL : 0 < radialLength (by omega) (normalizedAngle m u)
        (modelRadii m β u) i := by
      unfold radialLength
      apply length_pos
      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
        (pair_re_ge_one (small_half_angle hm (normalizedAngle m u) hθ i).2.1
          (hr i).1 (hr (nextIndex (by omega) i)).1)
    have hp := Lens.rotated_plus_active_iff
      (norm_unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i))
      hL (ht i).le (hwidth i) (hchart.1 i)
    have hn := Lens.rotated_minus_active_iff
      (norm_unit (radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i))
      hL (ht i).le (hwidth i) (hchart.1 i)
    rcases ctx.active i with ha | ha
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
  let sHalf : Fin m → ℝ := fun i => activeHalfSign (by omega)
    (normalizedAngle m u) (modelRadii m β u) (actualCenter m β u) i
  have hsfun : s = sHalf := funext hsactive
  subst s
  change Multipliers (show 0 < m by omega) sHalf (normalizedPoint m β u) at K
  have hxinj : Function.Injective (normalizedPoint m β u) := by
    apply HullGeometry.injective_of_discriminant_pos
    rw [MatchingActivitySaturation.model_discriminant_normalizedPoint h]
    exact (pow_pos (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ)) (2 * m)).trans_le
      (hz.discriminant_ge (by omega))
  have hdc : GeometricRelativeRemainder.configuration (modelDiameter m β u)
      (actualCenter m β u) = normalizedPoint m β u := by
    funext j
    simp only [GeometricRelativeRemainder.configuration, normalizedPoint_decomposition,
      modelDiameter]
  have hinjDC : Function.Injective (GeometricRelativeRemainder.configuration
      (modelDiameter m β u) (actualCenter m β u)) := by
    rw [hdc]
    exact hxinj
  have hsmallC' : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2 := by
    calc
      _ = 2 * (physicalStepConstant / (2 * m : ℝ)) := by ring
      _ ≤ 2 * (1 / 1000 : ℝ) := mul_le_mul_of_nonneg_left ctx.smallC (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  intro i
  constructor
  · let U : Points (2 * m) := directVelocity (by omega) (normalizedAngle m u) i +
        centerVelocity (by omega) (normalizedAngle m u) sHalf ν
          (modelRadii m β u) g i
    have hM (j : Fin m) : edgeDifferential (normalizedPoint m β u) U
        (matchingFirst j) (matchingSecond (by omega) j) = if j = i then 8 else 0 := by
      have hresp := matching_radial_response (show 2 ≤ m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) g i j hchart hhalf hpos ht
      simpa only [U, outwardPath, radiusPath_zero, hchart.2.1, hbase,
        ctx.saturated, mul_one] using hresp
    have hX (j : Fin m) : edgeDifferential (normalizedPoint m β u) U
        (selectedFirst (by omega) sHalf j) (selectedSecond (by omega) sHalf j) = 0 := by
      have hresp := selected_radial_response_zero (show 2 ≤ m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) g i j hchart hhalf hsend hpos ht
      simpa only [U, outwardPath, radiusPath_zero, hchart.2.1, hbase] using hresp
    let D := (∑ j, inner ℝ (realGradient (normalizedPoint m β u) j)
        (directVelocity (by omega) (normalizedAngle m u) i j)) +
      centerFirst (modelDiameter m β u) (actualCenter m β u)
        (centerVelocity (by omega) (normalizedAngle m u) sHalf ν
          (modelRadii m β u) g i)
    have hp0 : outwardPath (by omega) (normalizedAngle m u) sHalf ν
        (modelRadii m β u) (average (actualCenter m β u)) g i 0 =
        normalizedPoint m β u := by
      simpa only [outwardPath, radiusPath_zero, hchart.2.1] using hbase
    have hd : HasDerivAt (fun t => Real.log (discriminant
        (outwardPath (by omega) (normalizedAngle m u) sHalf ν
          (modelRadii m β u) (average (actualCenter m β u)) g i t))) D 0 := by
      have hd' := outwardPath_log_derivative (show 0 < m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) g i hchart hpos ht
        (modelDiameter m β u) (actualCenter m β u) (hp0.trans hdc.symm) hinjDC
      rw [hdc] at hd'
      simpa only [D] using hd'
    have hv (j : Fin (2 * m)) : HasDerivAt (fun t =>
        outwardPath (by omega) (normalizedAngle m u) sHalf ν
          (modelRadii m β u) (average (actualCenter m β u)) g i t j) (U j) 0 := by
      simpa only [U, Pi.add_apply] using outwardPath_hasDerivAt (show 0 < m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) g i hchart hpos ht j
    have hpderiv : HasDerivAt (outwardPath (by omega) (normalizedAngle m u) sHalf ν
        (modelRadii m β u) (average (actualCenter m β u)) g i) U 0 :=
      hasDerivAt_pi.mpr hv
    have hfd : HasFDerivAt logDiscriminant
        (fderiv ℝ logDiscriminant (normalizedPoint m β u))
        (normalizedPoint m β u) :=
      (logDiscriminant_contDiffAt hxinj).differentiableAt
        (by norm_num : (∞ : WithTop ℕ∞) ≠ 0) |>.hasFDerivAt
    rw [← hp0] at hfd
    have hchain := hfd.comp_hasDerivAt 0 hpderiv
    have hobj : fderiv ℝ logDiscriminant (normalizedPoint m β u) U = D := by
      rw [← hp0]
      exact hchain.unique hd
    have hdlower : lowerBound (2 * m) ≤ D := by
      exact model_radial_derivative_lower hm β u h.periodic ctx.bounds hθ hstep ctx.budget
        ctx.pressure ctx.smallD hsmallC' ctx.smallG sHalf ν g hchart hbase hν hr i
    have hDpos : 0 < D := ctx.gain.trans_le hdlower
    apply matching_multiplier_pos_of_response (show 0 < m by omega) sHalf
      (normalizedPoint m β u) K i U hM hX
    rwa [hobj]
  · have hzero : closureFamily (parameters (by omega) (normalizedAngle m u) sHalf ν
        (modelRadii m β u)) 0 = 0 := by
      simpa only [hchart.2.1] using hchart.2.2.2.1.self_of_nhds
    obtain ⟨ξ, hξ0, hξ, hroot⟩ := exists_smooth_sigma_root (show 2 ≤ m by omega)
      (normalizedAngle m u) sHalf ν (modelRadii m β u) i hchart.1 hsmall hzero
    let U : Points (2 * m) := centerVelocity (by omega) (normalizedAngle m u) sHalf ν
      (modelRadii m β u) ξ i
    let R : ℝ := 2 * sHalf i * Lens.height (ν i) *
      Lens.width (radialLength (by omega) (normalizedAngle m u)
        (modelRadii m β u) i) (ν i)
    have hM (j : Fin m) : edgeDifferential (normalizedPoint m β u) U
        (matchingFirst j) (matchingSecond (by omega) j) = 0 := by
      have hresp := matching_crossing_response_zero (show 2 ≤ m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) i j ξ hhalf hsmall hξ0 hξ hroot
      simpa only [U, crossingPath, sigmaPath_zero, hξ0, hbase] using hresp
    have hX (j : Fin m) : edgeDifferential (normalizedPoint m β u) U
        (selectedFirst (by omega) sHalf j) (selectedSecond (by omega) sHalf j) =
        if j = i then R else 0 := by
      have hresp := selected_crossing_response (show 2 ≤ m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) i j ξ hhalf hsend hsmall hwidth hξ0 hξ hroot
      by_cases hj : j = i
      · subst j
        simpa only [U, R, crossingPath, sigmaPath_zero, hξ0, hbase, if_pos] using hresp
      · simpa only [U, R, crossingPath, sigmaPath_zero, hξ0, hbase, if_neg hj] using hresp
    let D := centerFirst (modelDiameter m β u) (actualCenter m β u) U
    have hp0 : crossingPath (by omega) (normalizedAngle m u) sHalf ν
        (modelRadii m β u) (average (actualCenter m β u)) ξ i 0 =
        normalizedPoint m β u := by
      simpa only [crossingPath, sigmaPath_zero, hξ0] using hbase
    have hd : HasDerivAt (fun t => Real.log (discriminant
        (crossingPath (by omega) (normalizedAngle m u) sHalf ν (modelRadii m β u)
          (average (actualCenter m β u)) ξ i t))) D 0 := by
      have hd' := crossingPath_log_derivative (show 2 ≤ m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) i ξ hsmall hξ0 hξ hroot
        (modelDiameter m β u) (actualCenter m β u) (hp0.trans hdc.symm) hinjDC
      simpa only [D, U] using hd'
    have hv (j : Fin (2 * m)) : HasDerivAt (fun t =>
        crossingPath (by omega) (normalizedAngle m u) sHalf ν (modelRadii m β u)
          (average (actualCenter m β u)) ξ i t j) (U j) 0 := by
      simpa only [U] using crossingPath_hasDerivAt (show 2 ≤ m by omega)
        (normalizedAngle m u) sHalf ν (modelRadii m β u)
        (average (actualCenter m β u)) i ξ hsmall hξ0 hξ hroot j
    have hpderiv : HasDerivAt (crossingPath (by omega) (normalizedAngle m u) sHalf ν
        (modelRadii m β u) (average (actualCenter m β u)) ξ i) U 0 :=
      hasDerivAt_pi.mpr hv
    have hfd : HasFDerivAt logDiscriminant
        (fderiv ℝ logDiscriminant (normalizedPoint m β u))
        (normalizedPoint m β u) :=
      (logDiscriminant_contDiffAt hxinj).differentiableAt
        (by norm_num : (∞ : WithTop ℕ∞) ≠ 0) |>.hasFDerivAt
    rw [← hp0] at hfd
    have hchain := hfd.comp_hasDerivAt 0 hpderiv
    have hobj : fderiv ℝ logDiscriminant (normalizedPoint m β u) U = D := by
      rw [← hp0]
      exact hchain.unique hd
    let p := operator (2 * m) (polarConstraint (by omega) β u)
      (CommonClosureEnergy.halfIndex i)
    have hDpressure : 0 < D * p := by
      exact actual_crossing_derivative_pressure_sign hm h.periodic ctx.bounds hθ ctx.budget
        ctx.gap ctx.pressure ctx.smallD hsmallC' ctx.saturated ctx.margin
        sHalf ν ξ i hchart.1 hν hsmall hξ0 hξ hroot
    have hsPressure : 0 < sHalf i * p := by
      exact model_activeHalfSign_pressure_pos hm h hz ctx.bounds hθ ctx.budget ctx.gap
        ctx.pressure ctx.smallB ctx.smallC ctx.smallR ctx.smallb ctx.smallD
        ctx.saturated ctx.margin i (ctx.active i)
    have hDs : 0 < D * sHalf i := by
      rcases (mul_pos_iff.mp hDpressure) with hpp | hnn
      · rcases (mul_pos_iff.mp hsPressure) with hpp' | hnn'
        · exact mul_pos hpp.1 hpp'.1
        · linarith
      · rcases (mul_pos_iff.mp hsPressure) with hpp' | hnn'
        · linarith
        · exact mul_pos_of_neg_of_neg hnn.1 hnn'.1
    have hDR : 0 < D * R := by
      rw [show D * R = (D * sHalf i) *
          (2 * Lens.height (ν i) * Lens.width (radialLength (by omega)
            (normalizedAngle m u) (modelRadii m β u) i) (ν i)) by
        dsimp [R]
        ring]
      exact mul_pos hDs (mul_pos (mul_pos (by norm_num)
        (LensIncrementDerivatives.height_pos (ht i))) (hwidth i))
    apply crossing_multiplier_pos_of_response (show 0 < m by omega) sHalf
      (normalizedPoint m β u) K i U R hM hX
    rwa [hobj]

/-- The manuscript's plus-crossing coefficient, with the inactive member of
the pair filled by zero. -/
def plusCrossingCoefficient {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (K : ActualMultipliers hm β u) (i : Fin m) : ℝ :=
  if activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i = 1 then K.crossing i else 0

/-- The manuscript's minus-crossing coefficient, with the inactive member of
the pair filled by zero. -/
def minusCrossingCoefficient {m : ℕ} (hm : 0 < m) (β : ℂ) (u : ℕ → ℂ)
    (K : ActualMultipliers hm β u) (i : Fin m) : ℝ :=
  if activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i = -1 then K.crossing i else 0

theorem positive_crossing_coefficient_split {m : ℕ} (hm : 0 < m)
    (β : ℂ) (u : ℕ → ℂ) (K : ActualMultipliers hm β u) (i : Fin m)
    (hpos : 0 < K.crossing i) :
    (0 < plusCrossingCoefficient hm β u K i ∧
        minusCrossingCoefficient hm β u K i = 0) ∨
      (plusCrossingCoefficient hm β u K i = 0 ∧
        0 < minusCrossingCoefficient hm β u K i) := by
  have hs : activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i = 1 ∨
      activeHalfSign hm (normalizedAngle m u) (modelRadii m β u)
        (actualCenter m β u) i = -1 := by
    unfold activeHalfSign
    split <;> simp
  rcases hs with hs | hs
  · refine Or.inl ⟨by simp [plusCrossingCoefficient, hs, hpos], ?_⟩
    unfold minusCrossingCoefficient
    rw [hs]
    norm_num
  · refine Or.inr ⟨?_, by simp [minusCrossingCoefficient, hs, hpos]⟩
    unfold plusCrossingCoefficient
    rw [hs]
    norm_num

theorem crossing_coefficient_complementarity {m : ℕ} (hm : 0 < m)
    (β : ℂ) (u : ℕ → ℂ) (K : ActualMultipliers hm β u) (i : Fin m) :
    plusCrossingCoefficient hm β u K i + minusCrossingCoefficient hm β u K i =
      K.crossing i := by
  unfold plusCrossingCoefficient minusCrossingCoefficient activeHalfSign
  split <;> norm_num

/-- Every sufficiently large genuine even-order diameter maximizer admits one
unique normalized multiplier family, and every matching and physically
selected crossing coefficient in that family is strictly positive. -/
theorem eventual_actual_maximizer_positive_multipliers :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ) (K : ActualMultipliers hm β u),
        NormalizedRelativeEdgeModel z π α β u η ∧
        ActualKKTConditions hm β u ∧
        (∀ L : ActualMultipliers hm β u, L = K) ∧
        ∀ i : Fin m, 0 < K.matching i ∧ 0 < K.crossing i := by
  obtain ⟨m₀, h₀⟩ := eventual_actual_maximizer_unique_multipliers
  refine ⟨max m₀ 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, π, α, β, u, η, hmodel, _, hctx, K, huniq⟩ :=
    h₀ m (by omega) z hz
  refine ⟨hmp, π, α, β, u, η, K, hmodel, hctx, huniq, ?_⟩
  exact model_actual_multipliers_positive (show 8 ≤ m by omega) hmodel hz hctx K

end
end StructuralNote.MatchingActivityKKTPositive
