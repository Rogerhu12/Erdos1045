import StructuralNote.MatchingActivityRadialLowerBound
import StructuralNote.MatchingActivityRadialObjectiveFirst
import StructuralNote.MatchingActivityRadialPath
import StructuralNote.ActualCrossingGeometry
import StructuralNote.StrongPressurePointwiseCoordinates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! One-sided maximality for the genuine radial chart.

The radial chart gives a feasible path only on the outward half-line when a
matching radius is unsaturated.  This file records the corresponding
one-sided first-order obstruction, before attempting to identify the missing
actual-maximizer saturation input.
-/

namespace StructuralNote.MatchingActivitySaturation

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter Set
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter
open MatchingActivityRadialClosure MatchingActivityRadialGeometry
open MatchingActivityRadialFeasible MatchingActivityRadialPath
open MatchingActivityRadialObjectiveFirst MatchingActivityRadialLowerBound
open MatchingActivityRadialGradient MatchingActivityRadialModelCenterError
open MatchingActivityRadialActual MatchingActivityRadialPair MatchingActivityRadialVelocity
open MatchingActivityRadialBounds MatchingActivityRadialIntegration MatchingActivityRadialCenterFirst
open MatchingActivityRadialDiameterError MatchingActivityRadialModelEnergy
open MatchingActivityNonlocalPairs
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongPointwiseSteps StrongPointwiseRadial
open StrongBudgetConsequences StrongObjectiveEstimate SinglePressureEstimate SignedPressureRemainder
open StrongPressurePointwiseCoordinates
open GeometricRelativeRemainder
open LocalGradient
open scoped BigOperators Topology ContDiff
noncomputable section

/-- The normalized polar model is obtained from the labeled extremizer by a
translation, a unit complex factor, and the labeling permutation. -/
theorem model_discriminant_normalizedPoint {m : ℕ} {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η) :
    discriminant (normalizedPoint m β u) = discriminant z := by
  have hrep : z ∘ σ = fun j =>
      (α + (β / (‖β‖ : ℂ)) * physicalTranslation m ‖β‖ u) +
        ((β / (‖β‖ : ℂ)) * PolarCenterEnergy.phase (-meanAngle m u)) * normalizedPoint m β u j := by
    funext j
    have hh := model_normalized_coordinates h j
    rw [← ActualPressureGap.polarCenter_eq_normalizedCenter m β u] at hh
    simpa only [Function.comp_apply, normalizedPoint, PolarCenterEnergy.phase, neg_neg,
      SignedPressureAngular.root, PolarRepresentation.reference, mul_assoc] using hh
  rw [← HullGeometry.discriminant_perm z σ, hrep, discriminant_affine,
    normalizedRotation_norm h.scale_ne_zero, one_pow, one_mul]

/-- The normalized physical coordinates represent the same diameter extremal,
not merely a configuration with the same pairwise distances. -/
theorem model_normalizedPoint_extremal {m : ℕ} {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z) :
    ExtremalNormalization.DiameterExtremal (normalizedPoint m β u) := by
  refine ⟨model_diameter h hz.1, ?_⟩
  intro w hw
  rw [model_discriminant_normalizedPoint h]
  exact hz.2 w hw

/-- The fixed radial derivative lower bound is eventually strictly positive. -/
theorem eventual_lowerBound_pos : ∀ᶠ n : ℕ in atTop, 0 < lowerBound n := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hn
  have hl : Tendsto (fun n : ℕ => Real.log n / (n : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using
      (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hn)
  have hil : Tendsto (fun n : ℕ => (1 + Real.log n) / (n : ℝ)) atTop (𝓝 0) := by
    convert hi.add hl using 1
    · funext n
      ring
    · norm_num
  have hs : Tendsto (fun n : ℕ => Real.sqrt n / (n : ℝ)) atTop (𝓝 0) := by
    have hs' : Tendsto (fun n : ℕ => 1 / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
    apply hs'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0.le
    calc
      1 / Real.sqrt n = Real.sqrt n / Real.sqrt n ^ 2 := by
        field_simp [Real.sqrt_pos.2 hn0]
      _ = Real.sqrt n / (n : ℝ) := by rw [hsq]
  have ht : Tendsto (fun n : ℕ => lowerBound n / (n : ℝ)) atTop (𝓝 (1 / 4 : ℝ)) := by
    have hc : Tendsto (fun _ : ℕ => (1 / 4 : ℝ)) atTop (𝓝 (1 / 4 : ℝ)) := tendsto_const_nhds
    have h53 : Tendsto (fun n : ℕ => 53 * (1 / (n : ℝ))) atTop (𝓝 (53 * 0)) := hi.const_mul 53
    have hlog : Tendsto (fun n : ℕ => 4 * configurationStepConstant *
        ((1 + Real.log n) / (n : ℝ))) atTop (𝓝 (4 * configurationStepConstant * 0)) :=
      hil.const_mul (4 * configurationStepConstant)
    have hsqrt : Tendsto (fun n : ℕ => 12 * centerErrorConstant *
        (Real.sqrt n / (n : ℝ))) atTop (𝓝 (12 * centerErrorConstant * 0)) :=
      hs.const_mul (12 * centerErrorConstant)
    have h := (hc.sub h53).sub hlog |>.sub hsqrt
    have h' : Tendsto (fun n : ℕ => (1 / 4 : ℝ) - 53 * (1 / (n : ℝ)) -
        4 * configurationStepConstant * ((1 + Real.log n) / (n : ℝ)) -
        12 * centerErrorConstant * (Real.sqrt n / (n : ℝ))) atTop (𝓝 (1 / 4 : ℝ)) := by
      simpa only [mul_zero, sub_zero] using h
    apply h'.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    dsimp only [lowerBound]
    field_simp
  filter_upwards [ht.eventually (eventually_gt_nhds (show (0 : ℝ) < 1 / 4 by norm_num)),
    eventually_ge_atTop 1] with n hpos hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm := mul_pos hpos hn0
  simpa [ne_of_gt hn0] using hm

/-- The remaining denominator hypotheses in the radial derivative estimate are
eventual numerical facts, independent of the maximizer. -/
theorem eventual_radial_derivative_scales : ∀ᶠ n : ℕ in atTop,
    0 < lowerBound n ∧ diameterStepConstant / (n : ℝ) ≤ 1 / 2 ∧
      configurationStepConstant / (n : ℝ) ≤ 1 / 2 := by
  filter_upwards [eventual_lowerBound_pos,
    (tendsto_const_div_atTop_nhds_zero_nat diameterStepConstant).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2),
    (tendsto_const_div_atTop_nhds_zero_nat configurationStepConstant).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2)] with n hpos hD hG
  exact ⟨hpos, hD, hG⟩

/-- A one-sided feasible perturbation of a diameter extremizer has
nonpositive logarithmic discriminant derivative. -/
theorem oneSided_log_derivative_nonpos {n : ℕ} {x : Points n}
    (hx : ExtremalNormalization.DiameterExtremal x)
    {p : ℝ → Points n} {d : ℝ}
    (hp0 : p 0 = x)
    (hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t → DiameterAtMost 2 (p t))
    (hinj : ∀ᶠ t in 𝓝 (0 : ℝ), Function.Injective (p t))
    (hd : HasDerivAt (fun t => Real.log (discriminant (p t))) d 0) :
    d ≤ 0 := by
  have hlocal : IsLocalMaxOn (fun t => Real.log (discriminant (p t))) (Ici (0 : ℝ)) 0 := by
    change ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] (0 : ℝ),
      Real.log (discriminant (p t)) ≤ Real.log (discriminant (p 0))
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hfeas, hinj] with t ht hti ht0
    have hdt : DiameterAtMost 2 (p t) := ht ht0
    have hdisc : discriminant (p t) ≤ discriminant x := hx.2 (p t) hdt
    have hpos_t : 0 < discriminant (p t) := discriminant_pos _ (hti)
    rw [← hp0] at hdisc
    exact Real.log_le_log hpos_t hdisc
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    exact (convex_Ici (0 : ℝ)).segment_subset (by simp) (by simp)
  have h := hlocal.hasFDerivWithinAt_nonpos hd.hasDerivWithinAt htangent
  simpa using h

set_option maxHeartbeats 800000 in
/-- At the actual normalized maximizer, every matching semidiameter is one.
The proof uses the genuine feasible outward chart and the positive derivative
bound, rather than imposing matching activity as a chart hypothesis. -/
theorem model_matching_saturated {m : ℕ} (hm : 8 ≤ m) {z : Points (2 * m)}
    {σ : Equiv.Perm (Fin (2 * m))} {α β : ℂ} {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z σ α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤ 31 * Real.pi / 64)
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2)
    (hbounds : PointwiseBounds (m := m) (by omega) β u)
    (hsmallB : 4 * budgetConstant / (2 * m : ℝ) ≤ 1 / 1000000)
    (hsmallC : physicalStepConstant / (2 * m : ℝ) ≤ 1 / 1000)
    (hsmallR : radialErrorConstant / (2 * m : ℝ) ≤ 10 - Real.pi ^ 2)
    (hsmallb : 2 * budgetConstant / (2 * m : ℝ) ≤ 1 / 10)
    (hsmallD : diameterStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmallG : configurationStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hgain : 0 < lowerBound (2 * m)) :
    ∀ i : Fin m, modelRadii m β u i = 1 := by
  obtain ⟨hθ, hstep, _⟩ := model_nonlocal_smallness hm h hz.1 hbounds hbudget
    hsmallB hsmallC hsmallR
  obtain ⟨s, ν, g, hchart, hbase, hν⟩ := model_feasible_radial_chart hm h hz.1 hbounds
    hbudget hsmallB hsmallC hsmallR hsmallb
  have hr := model_radii_bounds hm h hz.1 hbounds hsmallB
  have hhalf : HalfPeriodic (by omega) (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u h.periodic j)
  have hpos (j : Fin m) : 0 < (pair (halfAngle (by omega) (normalizedAngle m u) j)
      (modelRadii m β u j) (modelRadii m β u (nextIndex (by omega) j))).re := by
    have hφ := (small_half_angle hm (normalizedAngle m u) hθ j).2.1
    exact lt_of_lt_of_le (by norm_num) (pair_re_ge_one hφ (hr j).1 (hr _).1)
  have ht (j : Fin m) : ν j ^ 2 < 4 := by
    have hn : (16 : ℝ) ≤ 2 * m := by exact_mod_cast (show 16 ≤ 2 * m by omega)
    have hν' : |ν j| < 2 := (hν j).trans_lt (by
      apply (div_lt_iff₀ (by positivity : 0 < 1000 * (2 * m : ℝ))).2
      nlinarith)
    nlinarith [(abs_lt.mp hν').1, (abs_lt.mp hν').2]
  have hsmallC' : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2 := by
    calc
      _ = 2 * (physicalStepConstant / (2 * m : ℝ)) := by ring
      _ ≤ 2 * (1 / 1000 : ℝ) := mul_le_mul_of_nonneg_left hsmallC (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have hx := model_normalizedPoint_extremal h hz
  have hinj : Function.Injective (normalizedPoint m β u) := by
    apply HullGeometry.injective_of_discriminant_pos
    rw [model_discriminant_normalizedPoint h]
    exact (pow_pos (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ)) (2 * m)).trans_le
      (hz.discriminant_ge (by omega))
  intro i
  apply le_antisymm (hr i).2
  by_contra hri
  have hlt : modelRadii m β u i < 1 := lt_of_not_ge hri
  have hp := outwardPath_properties (show 0 < m by omega) (normalizedAngle m u) s ν
    (modelRadii m β u) (average (actualCenter m β u)) g i hchart hhalf
    (fun j => ⟨(by linarith [(hr j).1]), (hr j).2⟩) hlt
  have hp0 : outwardPath (show 0 < m by omega) (normalizedAngle m u) s ν
      (modelRadii m β u) (average (actualCenter m β u)) g i 0 = normalizedPoint m β u :=
    hp.1.trans hbase
  have hpderiv (j : Fin (2 * m)) : HasDerivAt (fun t =>
      outwardPath (show 0 < m by omega) (normalizedAngle m u) s ν
        (modelRadii m β u) (average (actualCenter m β u)) g i t j)
      (directVelocity (show 0 < m by omega) (normalizedAngle m u) i j +
        centerVelocity (show 0 < m by omega) (normalizedAngle m u) s ν
          (modelRadii m β u) g i j) 0 :=
    outwardPath_hasDerivAt (show 0 < m by omega) (normalizedAngle m u) s ν
      (modelRadii m β u) (average (actualCenter m β u)) g i hchart hpos ht j
  have hpinj : ∀ᶠ t in 𝓝 (0 : ℝ), Function.Injective
      (outwardPath (show 0 < m by omega) (normalizedAngle m u) s ν
        (modelRadii m β u) (average (actualCenter m β u)) g i t) :=
    RadialObjectivePrice.eventually_injective_of_hasDerivAt hpderiv (hp0 ▸ hinj)
  have hdc : GeometricRelativeRemainder.configuration (modelDiameter m β u)
      (actualCenter m β u) = normalizedPoint m β u := by
    funext j
    simp only [GeometricRelativeRemainder.configuration, normalizedPoint_decomposition, modelDiameter]
  have hinjDC : Function.Injective (GeometricRelativeRemainder.configuration
      (modelDiameter m β u) (actualCenter m β u)) := by
    rw [hdc]
    exact hinj
  have hd : HasDerivAt (fun t => Real.log (discriminant
      (outwardPath (show 0 < m by omega) (normalizedAngle m u) s ν
        (modelRadii m β u) (average (actualCenter m β u)) g i t)))
      ((∑ j, inner ℝ (realGradient (normalizedPoint m β u) j)
          (directVelocity (show 0 < m by omega) (normalizedAngle m u) i j)) +
        centerFirst (modelDiameter m β u) (actualCenter m β u)
          (centerVelocity (show 0 < m by omega) (normalizedAngle m u) s ν
            (modelRadii m β u) g i)) 0 := by
    have hd' := outwardPath_log_derivative (show 0 < m by omega) (normalizedAngle m u) s ν
      (modelRadii m β u) (average (actualCenter m β u)) g i hchart hpos ht
      (modelDiameter m β u) (actualCenter m β u) (hp0.trans hdc.symm) hinjDC
    rw [hdc] at hd'
    exact hd'
  have hdlower : lowerBound (2 * m) ≤
      (∑ j, inner ℝ (realGradient (normalizedPoint m β u) j)
        (directVelocity (show 0 < m by omega) (normalizedAngle m u) i j)) +
      centerFirst (modelDiameter m β u) (actualCenter m β u)
        (centerVelocity (show 0 < m by omega) (normalizedAngle m u) s ν
          (modelRadii m β u) g i) :=
    model_radial_derivative_lower hm β u h.periodic hbounds hθ hstep hbudget hpressure
      hsmallD hsmallC' hsmallG s ν g hchart hbase hν hr i
  have hdpos : 0 <
      (∑ j, inner ℝ (realGradient (normalizedPoint m β u) j)
        (directVelocity (show 0 < m by omega) (normalizedAngle m u) i j)) +
      centerFirst (modelDiameter m β u) (actualCenter m β u)
        (centerVelocity (show 0 < m by omega) (normalizedAngle m u) s ν
          (modelRadii m β u) g i) := hgain.trans_le hdlower
  have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), 0 ≤ t → DiameterAtMost 2
      (outwardPath (show 0 < m by omega) (normalizedAngle m u) s ν
        (modelRadii m β u) (average (actualCenter m β u)) g i t) :=
    hp.2.2.mono (fun _ ht hnonneg => (ht hnonneg).1)
  have hdnonpos := oneSided_log_derivative_nonpos hx hp0 hfeas hpinj hd
  linarith

/-- Every sufficiently large genuine even-order diameter maximizer has all
matching semidiameters equal to one in its actual normalized coordinates. -/
theorem eventual_diameter_matching_saturated :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m), ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (σ : Equiv.Perm (Fin (2 * m))) (α β : ℂ) (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z σ α β u η ∧
        ‖operator (2 * m) (polarConstraint hm β u)‖ ≤ 31 * Real.pi / 64 ∧
        radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
          DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 ∧
        PointwiseBounds hm β u ∧
        ∀ i : Fin m, modelRadii m β u i = 1 := by
  obtain ⟨m₀, h₀⟩ := eventual_diameter_pressure_pointwise_coordinates
  obtain ⟨n₁, h₁⟩ := eventually_atTop.1 eventual_coefficients_small
  obtain ⟨n₂, h₂⟩ := eventually_atTop.1 eventual_radial_derivative_scales
  refine ⟨max (max (max m₀ n₁) n₂) 8, ?_⟩
  intro m hm z hz
  obtain ⟨hmp, σ, α, β, u, η, h, hpressure, hbudget, hbounds⟩ :=
    h₀ m (by omega) z hz
  have hs := h₁ (2 * m) (by omega)
  have hd := h₂ (2 * m) (by omega)
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs hd
  have hsat := model_matching_saturated (show 8 ≤ m by omega) h hz hpressure hbudget hbounds
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hd.2.1 hd.2.2 hd.1
  exact ⟨hmp, σ, α, β, u, η, h, hpressure, hbudget, hbounds, hsat⟩

end
end StructuralNote.MatchingActivitySaturation
