import StructuralNote.FixedSchurRationalRecovery
import StructuralNote.FixedSchurRationalInnerWindow
import StructuralNote.CommonRationalWindowBounds

/-! Every chosen fixed-Schur point admits the literal rational recovery, with
no branch assumption. Inner-scale points satisfy the denominator-eight window. -/

namespace StructuralNote.FixedSchurRationalRecoveryBounds

open Complex Filter Erdos1045 Erdos1045.EventualExact LensClosure
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum CommonClosureEnergy
open CommonFiberGeometry CommonRationalChart RationalCommonConfiguration
open FixedSchurRationalWindowDomain FixedSchurEdgeGeometry FixedSchurLinear
open FixedSchurData FixedSchurChart CommonDomainClosure CommonDomainRadius
open FixedSchurRationalRecovery FixedSchurRationalWindowEnergy
open FixedSchurRationalInnerWindow
open EdgeCoordinates
open scoped BigOperators Topology
noncomputable section

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

theorem eventual_recovery_data :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (θ : Fin (2 * m) → ℝ) (v : Fin (2 * m) → ℂ),
      InDomain (by omega) θ v →
      let C := center (coordinate (by omega) s θ v) v
      let X := parameters hm s θ C
      theta (by omega) X = θ ∧
      normalizedCenter (by omega) (rationalSign s) X = C ∧
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 ∧
      ∀ j, |extendedAngleParameter (by omega) X j| ≤ 1 := by
  obtain ⟨N, hN⟩ := CommonRationalWindowBounds.eventual_domain_chart_bounds
  filter_upwards [eventual_coordinate_properties, eventually_ge_atTop (N + 4096)]
    with m hprops hmN
  intro hm s θ v hdom
  dsimp only
  have hp := hprops hm s θ v hdom
  have hθtiny := (hN m hmN θ v hdom 0 (by simp; positivity)).1
  have hn : (1 : ℝ) ≤ 2 * m := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hθsmall (j : Fin (2 * m)) : |θ j| < 1 / 8 :=
    (hθtiny j).trans_le (by gcongr; linarith)
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

theorem eventual_inner_rational_recovery (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
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
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
  filter_upwards [eventual_recovery_data,
    eventual_selectedWindow_of_inner_recovery B hB] with m hdata hwindow
  intro hm s θ v hdom henergy
  dsimp only
  obtain ⟨hθ, hC, hz, hX⟩ := hdata hm s θ v hdom
  exact ⟨hθ, hC, hz, hwindow hm s θ v _ hdom henergy hθ hC hX⟩

end
end StructuralNote.FixedSchurRationalRecoveryBounds
