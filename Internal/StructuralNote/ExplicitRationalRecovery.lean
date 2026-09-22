import StructuralNote.ExplicitRationalWindow
import StructuralNote.ExplicitComparisonNormal
import StructuralNote.FixedSchurRationalRecoveryBounds
/-! Explicit rational recovery and entry into the single algebraic branch window. -/
namespace StructuralNote.ExplicitRationalRecovery
open Filter Complex Erdos1045.EventualExact FiniteBox SchurSpectrum SchurLiftBounds
open CommonClosureEnergy CommonDomainClosure FixedSchurData FixedSchurChart
open FixedSchurNormalExpansion FixedSchurNormalInnerEnergy FixedSchurInnerAngles
open FixedSchurLinear FixedSchurLiftStability FixedSchurRationalWindowEnergy
open FixedSchurRationalWindowDomain
open AngularObjectiveCurvature
open scoped BigOperators Topology
open Filter Complex Erdos1045 Erdos1045.EventualExact LensClosure SchurSpectrum
open RationalCommonConfiguration FixedSchurRationalWindowEnergy
open FixedSchurRationalWindowDomain FixedSchurRationalReverseEnergy
open FixedSchurReferenceDisplacement CommonDomainClosure CommonDomainRadius
open FixedSchurChart FixedSchurLinear
open Complex Filter Erdos1045 Erdos1045.EventualExact LensClosure
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum CommonClosureEnergy
open CommonFiberGeometry CommonRationalChart RationalCommonConfiguration
open FixedSchurRationalWindowDomain FixedSchurEdgeGeometry FixedSchurLinear
open FixedSchurData FixedSchurChart CommonDomainClosure CommonDomainRadius
open FixedSchurRationalRecovery FixedSchurRationalWindowEnergy
open FixedSchurRationalInnerWindow
open EdgeCoordinates
open FixedSchurReferenceDisplacement FixedSchurRationalRecoveryBounds
open Erdos1045.ExplicitThreshold
noncomputable section

def squareLogThreshold (K : ℝ) : ℕ :=
  growthThreshold (Real.log 2 * (Real.sqrt |K| + 1))

theorem square_log_gt {n : ℕ} {K : ℝ} (hN : squareLogThreshold K ≤ n) :
    K < (CommonDomainRadius.logOrder n : ℝ) ^ 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hg := growth_log_gt hN
  have hc : Real.log n / Real.log 2 ≤ (CommonDomainRadius.logOrder n : ℝ) := Nat.le_ceil _
  have hh : Real.sqrt |K| + 1 < (CommonDomainRadius.logOrder n : ℝ) := by
    apply lt_of_lt_of_le ?_ hc
    exact (lt_div_iff₀ hlog2).mpr (by simpa only [mul_comm] using hg)
  have hs := Real.sq_sqrt (abs_nonneg K)
  have hr := Real.sqrt_nonneg |K|
  have hk := le_abs_self K
  nlinarith only [hh, hs, hr, hk]

def displacementThreshold (B : ℝ) : ℕ :=
  max (ExplicitComparisonNormal.orderThreshold B) (ExplicitComparisonNormal.orderThreshold 0)

def orderThreshold (B : ℝ) : ℕ :=
  max (displacementThreshold B) (squareLogThreshold (8 * innerWindowConstant B))

private theorem division_decay {a n : ℝ} (ha : 0 ≤ a) (hn : 1 ≤ n) :
    a / n ^ 4 ≤ a / n ^ 2 ∧ a / n ^ 3 ≤ a / n ^ 2 := by
  have hpos : 0 < n := by linarith
  constructor <;> apply div_le_div_of_nonneg_left ha (by positivity)
  · nlinarith [sq_nonneg (n ^ 2 - 1), sq_nonneg (n - 1)]
  · nlinarith [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn)]

theorem coordinate_reference_meanSquare (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : displacementThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      meanSquare (coordinate (by omega) s θ v - coordinate (by omega) s 0 0) ≤
        coordinateConstant B / (2 * m : ℝ) ^ 2 := by
  have hinner := ExplicitComparisonNormal.normal_error_meanSquare B hB ((le_max_left _ _).trans hN)
  have hzero := ExplicitComparisonNormal.normal_error_meanSquare 0 (by norm_num) ((le_max_right _ _).trans hN)
  clear hN
  intro hm s θ v hdom henergy
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hn0 : (0 : ℝ) < 2 * m := by linarith
  have hzenergy : pairEnergy (by omega : 0 < 2 * m) (fun _ => ((0 : ℝ) : ℂ)) +
      pairEnergy (by omega : 0 < 2 * m) (0 : Fin (2 * m) → ℂ) ≤
      (0 : ℝ) ^ 2 / (2 * m : ℝ) ^ 2 := by
    simp [pairEnergy_eq_chord_sum]
  have he := hinner hm s θ v hdom henergy
  have he0 := hzero hm s 0 0 (zero_inDomain (by omega)) hzenergy
  let e := normalError (by omega : 0 < 2 * m) θ (coordinate (by omega) s θ v)
    (patternSign s)
  let e0 := normalError (by omega : 0 < 2 * m) 0 (coordinate (by omega) s 0 0)
    (patternSign s)
  let a : Fin (2 * m) → ℝ := fun j => -(2 * m : ℝ) / 2 * patternSign s j *
    angleDifference (by omega) θ j
  have ha : meanSquare a = (2 * m : ℝ) ^ 2 / 4 *
      meanSquare (angleDifference (by omega) θ) := by
    have hp (j : Fin (2 * m)) : a j ^ 2 =
        (2 * m : ℝ) ^ 2 / 4 * angleDifference (by omega) θ j ^ 2 := by
      rcases patternSign_is_sign s j with hj | hj <;> simp only [a, hj] <;> ring
    unfold meanSquare
    simp_rw [hp]
    rw [← Finset.mul_sum]
    ring
  have hq : coordinate (by omega) s θ v - coordinate (by omega) s 0 0 =
      fun j => e j - e0 j - a j := by
    funext j
    simp only [e, e0, a, normalError, angleDifference, Pi.zero_apply, sub_self,
      mul_zero, sub_zero, Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hms := meanSquare_sub_sub_bound e e0 a
  rw [← hq, ha] at hms
  have hangle := angleDifference_meanSquare_le_of_joint_energy (by omega)
    θ v hB hdom henergy
  have hscaled : (2 * m : ℝ) ^ 2 / 4 *
      meanSquare (angleDifference (by omega) θ) ≤
      4 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * m : ℝ) ^ 2 / 4 *
          (16 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 5) := by
        gcongr
      _ = _ := by field_simp; ring
  have he' := (division_decay (sq_nonneg (normalEnergyConstant B)) hn).1
  have he0' := (division_decay (sq_nonneg (normalEnergyConstant 0)) hn).1
  have ha' := (division_decay (show 0 ≤ 4 * Real.pi ^ 2 * B ^ 2 by positivity) hn).2
  change meanSquare e ≤ _ at he
  change meanSquare e0 ≤ _ at he0
  calc
    _ ≤ 3 * meanSquare e + 3 * meanSquare e0 +
        3 * ((2 * m : ℝ) ^ 2 / 4 * meanSquare (angleDifference (by omega) θ)) := hms
    _ ≤ 3 * (normalEnergyConstant B ^ 2 / (2 * m : ℝ) ^ 2) +
        3 * (normalEnergyConstant 0 ^ 2 / (2 * m : ℝ) ^ 2) +
        3 * (4 * Real.pi ^ 2 * B ^ 2 / (2 * m : ℝ) ^ 2) := by
      gcongr
      · exact he.trans he'
      · exact he0.trans he0'
      · exact hscaled.trans ha'
    _ = _ := by unfold coordinateConstant; ring

theorem center_reference_energy (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : displacementThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      pairEnergy (by omega)
        (center (coordinate (by omega) s θ v) v - fixedReferenceCenter (by omega) s) ≤
        referenceConstant B / (2 * m : ℝ) ^ 2 := by
  have hbound := coordinate_reference_meanSquare B hB hN
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties
    ((ExplicitComparisonNormal.thresholds ((le_max_left _ _).trans hN)).1)
  clear hN
  intro hm s θ v hdom henergy
  have hq := (hprops hm s θ v hdom).antiperiodic
  have hq0 := (hprops hm s 0 0 (zero_inDomain (by omega))).antiperiodic
  have hanti : Antiperiodic (by omega)
      (coordinate (by omega) s θ v - coordinate (by omega) s 0 0) := by
    intro j
    simp only [Pi.sub_apply]
    rw [hq j, hq0 j]
    ring
  have hlift := canonicalLift_pairEnergy_le hm _ hanti
  have hms := hbound hm s θ v hdom henergy
  have heq : center (coordinate (by omega) s θ v) v - fixedReferenceCenter (by omega) s =
      fun j => SchurLift.canonicalLift
        (coordinate (by omega) s θ v - coordinate (by omega) s 0 0) j + v j := by
    rw [canonicalLift_sub]
    funext j
    simp only [FixedSchurLinear.center, fixedReferenceCenter, Pi.sub_apply, Pi.add_apply, Pi.zero_apply]
    ring
  rw [heq]
  have hyoung := pairEnergy_add_le_five_four (by omega : 0 < 2 * m)
    (SchurLift.canonicalLift (coordinate (by omega) s θ v - coordinate (by omega) s 0 0)) v
  have hv : pairEnergy (by omega) v ≤ B ^ 2 / (2 * m : ℝ) ^ 2 := by
    linarith [pairEnergy_nonneg (by omega : 0 < 2 * m) (fun j => (θ j : ℂ))]
  unfold referenceConstant
  simp only [add_div, mul_div_assoc]
  nlinarith only [hyoung, hlift, hms, hv]

theorem selectedWindowEnergy_bound (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : displacementThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (X : RationalConfiguration.Variables m → ℝ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      theta (by omega) X = θ →
      normalizedCenter (by omega) (rationalSign s) X =
        center (coordinate (by omega) s θ v) v →
      (∀ j, |extendedAngleParameter (by omega) X j| ≤ 1) →
      selectedWindowEnergy (by omega) s X ≤
        innerWindowConstant B / (2 * m : ℝ) ^ 2 := by
  have hcenter := center_reference_energy B hB hN
  have href := ExplicitRationalWindow.fixedReferenceCenter_data
    ((ExplicitComparisonNormal.thresholds ((le_max_left _ _).trans hN)).1)
  clear hN
  intro hm s θ v X hdom henergy hθ hC hX
  have hangle : pairEnergy (by omega) (fun j => (θ j : ℂ)) ≤
      B ^ 2 / (2 * m : ℝ) ^ 2 := by
    linarith [pairEnergy_nonneg (by omega : 0 < 2 * m) v]
  have ha := parameter_energy_le_four (by omega : 0 < m) X hX
  have hmean := angleMean_sq_le_theta_energy (by omega : 0 < m) X
  rw [hθ] at ha hmean
  have hc := rawCenter_reference_energy_le (by omega : 0 < m) s X
  rw [hC] at hc
  have href := (href hm s).2.2
  have hd := hcenter hm s θ v hdom henergy
  have hmean' : angleMean (by omega) X ^ 2 ≤ 12 * (B ^ 2 / (2 * m : ℝ) ^ 2) := by
    linarith
  have hprod : 5 * angleMean (by omega) X ^ 2 *
      pairEnergy (by omega) (fixedReferenceCenter (by omega) s) ≤
      96120 * (B ^ 2 / (2 * m : ℝ) ^ 2) := by
    calc
      _ ≤ 5 * (12 * (B ^ 2 / (2 * m : ℝ) ^ 2)) * 1602 := by
        gcongr
        exact pairEnergy_nonneg _ _
      _ = _ := by ring
  unfold selectedWindowEnergy innerWindowConstant
  simp only [add_div, mul_div_assoc]
  linarith only [ha, hangle, hc, hd, hprod]

theorem selectedWindow_of_inner_recovery (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
      (X : RationalConfiguration.Variables m → ℝ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      theta (by omega) X = θ →
      normalizedCenter (by omega) (rationalSign s) X =
        center (coordinate (by omega) s θ v) v →
      (∀ j, |extendedAngleParameter (by omega) X j| ≤ 1) →
      selectedWindowEnergy (by omega) s X <
        (CommonDomainRadius.logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
  have hbound := selectedWindowEnergy_bound B hB ((le_max_left _ _).trans hN)
  have hsquare := square_log_gt ((le_max_right _ _).trans hN)
  have hn : (0 : ℝ) < (2 * m : ℕ) := ExplicitHessianThreshold.order_pos
    ((ExplicitComparisonNormal.thresholds ((le_max_left _ _).trans ((le_max_left _ _).trans hN))).1)
  have hrad : 8 * innerWindowConstant B / ((2 * m : ℕ) : ℝ) ^ 2 < energyRadius (2 * m) := by
    exact (div_lt_div_iff_of_pos_right (sq_pos_of_pos hn)).mpr hsquare
  clear hsquare hn
  clear hN
  intro hm s θ v X hdom henergy hθ hC hX
  have hb := hbound hm s θ v X hdom henergy hθ hC hX
  unfold energyRadius at hrad
  have hrad' : innerWindowConstant B / (2 * m : ℝ) ^ 2 <
      (CommonDomainRadius.logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] at hrad
    rw [show (CommonDomainRadius.logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) =
      ((CommonDomainRadius.logOrder (2 * m) : ℝ) ^ 2 / (2 * m : ℝ) ^ 2) / 8 by ring]
    linarith
  exact hb.trans_lt hrad'

private theorem rotated_unit_real_gt_neg_one {a : ℝ} {W : ℂ}
    (ha : |a| < 1) (hW : ‖W‖ = 1) (hpos : 0 < W.re) :
    0 < 1 + (unit (-a) * W).re := by
  have hu : ‖unit (-a) - 1‖ ≤ |a| := by
    simpa only [unit, ofReal_zero, zero_mul, exp_zero, sub_zero, abs_neg] using
      norm_unit_sub_le (-a) 0
  have hd : ‖unit (-a) * W - W‖ < 1 := by
    rw [show unit (-a) * W - W = (unit (-a) - 1) * W by ring, norm_mul, hW, mul_one]
    exact hu.trans_lt ha
  have hr := Complex.abs_re_le_norm (unit (-a) * W - W)
  simp only [sub_re] at hr
  have hb := (abs_lt.mp (hr.trans_lt hd)).1
  linarith

private theorem framed_crossing_positive {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega))
    (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ)
    (hdom : InDomain (by omega) θ v)
    (hp : Properties hm θ v (FiniteBox.patternSign s) (coordinate (by omega) s θ v))
    (j : Fin m) :
    0 < (unit (-midpoint m j) *
      (crossingVector hm θ (center (coordinate (by omega) s θ v) v)
        (FiniteBox.patternSign s) (halfIndex j) / 2)).re := by
  let q := coordinate (by omega : 0 < m) s θ v
  let i := halfIndex j
  have hf : unit (-midpoint m j) = (starRingEnd ℂ) (frame (2 * m) i) := by
    have he : frame (2 * m) i = unit (midpoint m j) := by
      simpa only [i, CommonClosureEnergy.halfIndex, BoxLensLift.halfIndex] using
        BoxLensLift.frame_halfIndex j
    rw [he]
    apply Complex.ext <;> simp [unit_re, unit_im, Real.cos_neg, Real.sin_neg]
  have he := framed_crossing (by omega : 0 < 2 * m) θ q
    (J q + EdgeCoordinates.tangent (by omega) v) (FiniteBox.patternSign s) i
  have hd := center_difference hm q v hdom.2.2.1.2.2
  have hvec : crossingVector hm θ (center q v) (FiniteBox.patternSign s) i =
      diameterVector θ i + diameterVector θ (successor (by omega) i) +
        (FiniteBox.patternSign s i : ℂ) *
          EdgeCoordinates.edgeIncrement q (J q + EdgeCoordinates.tangent (by omega) v) i := by
    unfold crossingVector
    change _ + (FiniteBox.patternSign s i : ℂ) * difference (by omega) (center q v) i = _
    rw [hd]
  rw [← hvec] at he
  change 0 < (unit (-midpoint m j) *
    (crossingVector hm θ (center q v) (FiniteBox.patternSign s) i / 2)).re
  rw [hf, ← mul_div_assoc, he, Complex.div_ofNat_re]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
    zero_mul, sub_zero, mul_zero, add_zero]
  exact div_pos (hp.positive i) (by norm_num)

theorem recovery_data {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      let C := center (coordinate (by omega) s θ v) v
      let X := parameters hm s θ C
      theta (by omega) X = θ ∧
      normalizedCenter (by omega) (rationalSign s) X = C ∧
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 ∧
      ∀ j, |extendedAngleParameter (by omega) X j| ≤ 1 := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hscale := (ExplicitComparisonScalars.small_coefficients hN).2.2.1
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hscale
  clear hN
  intro hm s θ v hdom
  dsimp only
  have hp := hprops hm s θ v hdom
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hθsmall (j : Fin (2 * m)) : |θ j| < 1 / 8 := by
    have hj := CommonFiberSmallCoefficients.domain_theta_bound (by omega) θ v hdom j
    have hden : 1 / (1000 * (2 * m : ℝ)) ≤ (1 / 1000 : ℝ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1000 * (2 * m))).mpr
      linarith only [hn]
    exact (hj.trans hscale).trans_lt (hden.trans_lt (by norm_num))
  have ha1 (j : Fin m) : |relativeAngle (by omega) θ j| < 1 := by
    have hh := abs_sub_le (θ (halfIndex j)) 0 (initialAngle (by omega) θ)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    unfold relativeAngle
    have hz := hθsmall ⟨0, by omega⟩
    change |initialAngle (by omega) θ| < _ at hz
    linarith [hθsmall (halfIndex j)]
  have ha (j : Fin m) : |relativeAngle (by omega) θ j| < Real.pi :=
    (ha1 j).trans (by linarith [Real.pi_gt_three])
  let C := center (coordinate (by omega : 0 < m) s θ v) v
  have hC : HalfPeriodic (by omega) C :=
    center_halfPeriodic hm _ v hp.antiperiodic hdom.2.2.1.1
  have hcross (j : Fin m) :
      ‖crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j)‖ = 2 := hp.selected _
  have hR (j : Fin m) : 0 < 1 + (relativeCrossing hm s θ C j).re := by
    let W := unit (-midpoint m j) *
      (crossingVector hm θ C (FiniteBox.patternSign s) (halfIndex j) / 2)
    have hW : ‖W‖ = 1 := by
      simp only [W, norm_mul, norm_unit, one_mul, norm_div, hcross]
      norm_num
    have hpos : 0 < W.re := framed_crossing_positive hm s θ v hdom hp j
    have hθ0 : |initialAngle (by omega) θ| < 1 :=
      (hθsmall ⟨0, by omega⟩).trans (by norm_num)
    have he : relativeCrossing hm s θ C j = unit (-initialAngle (by omega) θ) * W := by
      unfold relativeCrossing W
      ring
    rw [he]
    exact rotated_unit_real_gt_neg_one hθ0 hW hpos
  refine ⟨recovery_theta hm s θ C hdom.1 hdom.2.1 ha,
    recovery_center hm s θ C hdom.1 hdom.2.1 ha hC hp.mean_zero hcross hR,
    recovery_closure hm s θ C hdom.1 hdom.2.1 ha hC hcross hR, ?_⟩
  intro j
  let k : Fin m := ⟨j.val % m, Nat.mod_lt _ (by omega)⟩
  change |RationalConfiguration.angleParameter (parameters hm s θ C) k| ≤ 1
  rw [FixedSchurRationalRecovery.parameters, RationalParameterRecovery.angleParameter_parameters (by omega) _ _
    (relativeAngle_zero (by omega) θ)]
  rw [← RationalChartInverse.unit_parameter (ha k)]
  apply le_of_lt (RationalChartInverse.parameter_abs_lt_of_close (le_refl (1 : ℝ)) ?_)
  have hu := norm_unit_sub_le (relativeAngle (by omega) θ k) 0
  simp only [unit, ofReal_zero, zero_mul, exp_zero, sub_zero] at hu
  exact hu.trans_lt (ha1 k)

theorem inner_rational_recovery (B : ℝ) (hB : 0 ≤ B) {m : ℕ} (hN : orderThreshold B ≤ 2 * m) :
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      pairEnergy (by omega) (fun j => (θ j : ℂ)) + pairEnergy (by omega) v ≤
        B ^ 2 / (2 * m : ℝ) ^ 2 →
      let C := center (coordinate (by omega) s θ v) v
      let X := parameters hm s θ C
      theta (by omega) X = θ ∧
      normalizedCenter (by omega) (rationalSign s) X = C ∧
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 ∧
      selectedWindowEnergy (by omega) s X <
        (CommonDomainRadius.logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
  have hdata := recovery_data
    ((ExplicitComparisonNormal.thresholds ((le_max_left _ _).trans ((le_max_left _ _).trans hN))).1)
  have hwindow := selectedWindow_of_inner_recovery B hB hN
  clear hN
  intro hm s θ v hdom henergy
  dsimp only
  obtain ⟨hθ, hC, hz, hX⟩ := hdata hm s θ v hdom
  exact ⟨hθ, hC, hz, hwindow hm s θ v _ hdom henergy hθ hC hX⟩

end
end StructuralNote.ExplicitRationalRecovery
