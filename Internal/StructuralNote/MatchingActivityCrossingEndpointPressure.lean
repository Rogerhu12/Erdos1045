import StructuralNote.MatchingActivityCrossingEndpointActual
import StructuralNote.MatchingActivityCrossingVariationSaturation

/-! The objective derivative along the endpoint graph has the sign of the
actual midpoint pressure. -/

namespace StructuralNote.MatchingActivityCrossingEndpointPressure

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum FiniteBox
open CommonClosureEnergy MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialActual
open MatchingActivityRadialIntegration MatchingActivityRadialCenterFirst
open MatchingActivityRadialModelCenterError MatchingActivityRadialDiameterError
open MatchingActivityRadialSmallness
open MatchingActivityCrossingVariationGraph
open MatchingActivityCrossingVariationDerivative MatchingActivityCrossingVariationPressure
open MatchingActivityCrossingVariationSaturation MatchingActivityCrossingKernelRate
open StrongPointwiseCoordinates StrongPointwiseSmallness StrongPointwiseSteps
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter
open SignedPressureRemainder SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open SolScalarGap
open scoped BigOperators Topology ContDiff
noncomputable section

/-- Under the quantitative crossing margin, the true objective derivative
has the strict sign of the pressure at the varied matching site. -/
theorem actual_crossing_derivative_pressure_sign {m : ℕ} (hm : 8 ≤ m)
    {β : ℂ} {u : ℕ → ℂ}
    (hu : Function.Periodic u (2 * m))
    (hb : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hgap : G (m := m) (by omega) (polarConstraint (by omega) β u) ≤
      budgetConstant / (2 * m : ℝ) ^ 2)
    (hpressure : ‖operator (2 * m) (polarConstraint (by omega) β u)‖ ≤
      31 * Real.pi / 64)
    (hsmallD : diameterStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmallC : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1)
    (hmargin :
      8 * (31 * Real.pi / 64) +
          (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ)) <
        ((Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 -
          budgetConstant / 2) / 8)
    (s ν : Fin m → ℝ) (ξ : ℝ → ℂ) (i : Fin m)
    (hs : ∀ j, |s j| ≤ 1)
    (hν : ∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hsmall : ∀ j, |radialPhase (by omega) (normalizedAngle m u)
      (modelRadii m β u) j - LensClosure.midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hroot : ∀ᶠ t in nhds (0 : ℝ),
      closureFamily (parameters (by omega) (normalizedAngle m u) (sigmaPath s i t) ν
        (modelRadii m β u)) (ξ t) = 0) :
    0 < centerFirst (modelDiameter m β u) (actualCenter m β u)
        (centerVelocity (by omega) (normalizedAngle m u) s ν
          (modelRadii m β u) ξ i) *
      operator (2 * m) (polarConstraint (by omega) β u)
        (CommonClosureEnergy.halfIndex i) := by
  have hr (j : Fin m) : 3 / 4 ≤ modelRadii m β u j ∧ modelRadii m β u j ≤ 1 := by
    rw [hsat j]
    norm_num
  have hscale (j : Fin m) :
      |radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) j -
        LensClosure.midpoint m j| + |ν j| ≤ 2 / (m : ℝ) := by
    have hh := phaseHeight_scale hm (normalizedAngle m u) (modelRadii m β u) ν hr hθ hν j
    exact hh.trans_eq (by ring)
  have hwpos := model_lens_width_pos hm β u ν hθ hν hsat i
  have hw : 0 ≤ Lens.width
      (radialLength (by omega) (normalizedAngle m u) (modelRadii m β u) i) (ν i) := hwpos.le
  let q : Fin (2 * m) → ℝ := polarConstraint (by omega) β u
  let g := operator (2 * m) q
  let w := Lens.width
    (radialLength (by omega) (normalizedAngle m u) (modelRadii m β u) i) (ν i)
  let δ := radialPhase (by omega) (normalizedAngle m u) (modelRadii m β u) i -
    LensClosure.midpoint m i
  let P := finitePairing g (constraint (by omega)
    (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i)) /
      (2 * m : ℝ)
  let M := g (CommonClosureEnergy.halfIndex i) * w * Real.cos δ /
    Real.sin (Real.pi / (2 * m : ℝ))
  let D := centerFirst (modelDiameter m β u) (actualCenter m β u)
    (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i)
  let L := (Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 -
    budgetConstant / 2
  have hganti : Antiperiodic (by omega) g := operator_antiperiodic (by omega) q
  have hgcoord (j : Fin (2 * m)) : |g j| ≤ 31 * Real.pi / 64 := by
    have hj := norm_le_pi_norm g j
    rw [Real.norm_eq_abs] at hj
    exact hj.trans hpressure
  have hloc : |P - M| ≤ 8 * (31 * Real.pi / 64) * w := by
    exact pressure_work_localization_scale (show 2 ≤ m by omega)
      (normalizedAngle m u) s ν (modelRadii m β u) i ξ hs hsmall hscale hξ0 hξ hroot
      g hganti hgcoord hw
  have hpoint : L ≤ (2 * m : ℝ) * |g (CommonClosureEnergy.halfIndex i)| := by
    exact scaled_potential_log_lower (m := m) (show 2 ≤ m by omega) q
      budgetConstant_nonneg hgap (CommonClosureEnergy.halfIndex i)
  have hmain : L * w / 8 ≤ |M| := by
    exact pressure_main_abs_lower (show 2 ≤ m by omega) hw
      (by linarith [hsmall i, abs_nonneg (ν i)]) hpoint
  have hsqrt := centerVelocity_sqrt_pairEnergy_le (show 2 ≤ m by omega)
    (normalizedAngle m u) s ν (modelRadii m β u) i ξ hs hsmall hξ0 hξ hroot hw
  have herr := model_crossing_objective_main_error (show 2 ≤ m by omega)
    β u s ν (modelRadii m β u) i ξ hu hb hθ hbudget hsmallD hsmallC
    hsmall hξ0 hξ hroot
  have hN : (0 : ℝ) < 2 * m := by positivity
  have herrscale : centerErrorConstant / (2 * m : ℝ) *
      Real.sqrt (pairEnergy (by omega)
        (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i)) ≤
      (9 / 2 : ℝ) * centerErrorConstant * w *
        Real.sqrt (1 + Real.log (2 * m : ℕ)) := by
    have hmultiply := mul_le_mul_of_nonneg_left hsqrt
      (div_nonneg centerErrorConstant_nonneg hN.le)
    calc
      _ ≤ centerErrorConstant / (2 * m : ℝ) *
          ((9 / 2 : ℝ) * (2 * m : ℝ) * w *
            Real.sqrt (1 + Real.log (2 * m : ℕ))) := hmultiply
      _ = _ := by field_simp
  have hDP : |D - P| ≤ (9 / 2 : ℝ) * centerErrorConstant * w *
      Real.sqrt (1 + Real.log (2 * m : ℕ)) := by
    exact herr.trans herrscale
  have hDM : |D - M| ≤
      (8 * (31 * Real.pi / 64) +
        (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ))) * w := by
    calc
      |D - M| = |(D - P) + (P - M)| := by
        congr 1
        ring
      _ ≤ |D - P| + |P - M| := abs_add_le _ _
      _ ≤ (9 / 2 : ℝ) * centerErrorConstant * w *
          Real.sqrt (1 + Real.log (2 * m : ℕ)) +
        8 * (31 * Real.pi / 64) * w := add_le_add hDP hloc
      _ = _ := by ring
  have hmarg := mul_lt_mul_of_pos_right hmargin hwpos
  change (8 * (31 * Real.pi / 64) +
      (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ))) * w <
    L / 8 * w at hmarg
  have hmain' : L / 8 * w ≤ |M| := by
    nlinarith only [hmain]
  have hclose : |D - M| < |M| := hDM.trans_lt (hmarg.trans_le hmain')
  have hL : 0 < L := by
    have hfirst : 0 < 8 * (31 * Real.pi / 64) := by positivity
    have hsecond : 0 ≤
        (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ)) :=
      mul_nonneg (mul_nonneg (by norm_num) centerErrorConstant_nonneg)
        (Real.sqrt_nonneg _)
    have hleft : 0 < 8 * (31 * Real.pi / 64) +
        (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ)) := by
      exact add_pos_of_pos_of_nonneg hfirst hsecond
    have hL8 : 0 < L / 8 := hleft.trans hmargin
    have hmul := mul_pos hL8 (by norm_num : (0 : ℝ) < 8)
    norm_num at hmul
    exact hmul
  have hgabs : 0 < |g (CommonClosureEnergy.halfIndex i)| := by
    nlinarith [hpoint]
  have hsine : 0 < Real.sin (Real.pi / (2 * m : ℝ)) := by
    have ha0 : 0 < Real.pi / (2 * m : ℝ) := by positivity
    have hapi : Real.pi / (2 * m : ℝ) < Real.pi :=
      div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < 2 * m by omega))
    exact Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hcos : 0 < Real.cos δ := by
    have hδ : |δ| ≤ 1 / 4 := by
      dsimp [δ]
      linarith [hsmall i, abs_nonneg (ν i)]
    have hδpow := pow_le_pow_left₀ (abs_nonneg δ) hδ 2
    have hδsq : δ ^ 2 ≤ 1 / 16 := by
      rw [sq_abs] at hδpow
      norm_num at hδpow ⊢
      exact hδpow
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
  rcases lt_or_gt_of_ne (abs_pos.mp hgabs) with hgneg | hgpos
  · have hMneg : M < 0 := by
      dsimp [M]
      exact div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hgneg hwpos) hcos) hsine
    rw [abs_of_neg hMneg] at hclose
    have hDneg : D < 0 := by
      have hh := (abs_lt.mp hclose).2
      linarith
    change 0 < D * g (CommonClosureEnergy.halfIndex i)
    exact mul_pos_of_neg_of_neg hDneg hgneg
  · have hMpos : 0 < M := by
      dsimp [M]
      exact div_pos (mul_pos (mul_pos hgpos hwpos) hcos) hsine
    rw [abs_of_pos hMpos] at hclose
    have hDpos : 0 < D := by
      have hh := (abs_lt.mp hclose).1
      linarith
    change 0 < D * g (CommonClosureEnergy.halfIndex i)
    exact mul_pos hDpos hgpos

end
end StructuralNote.MatchingActivityCrossingEndpointPressure
