import StructuralNote.MatchingActivityCrossingKernelRate
import StructuralNote.MatchingActivityRadialSmallness
import StructuralNote.MatchingActivityCrossingExclusivity

/-! The quantitative first-variation contradiction at a site where both
adjacent crossing constraints are slack. -/

namespace StructuralNote.MatchingActivityCrossingVariationSaturation

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy MatchingActivityRadialPair MatchingActivityRadialBounds
open MatchingActivityRadialClosure MatchingActivityRadialGeometry MatchingActivityRadialBase
open MatchingActivityRadialActual MatchingActivityRadialIntegration MatchingActivityNonlocal
open MatchingActivityCrossingExclusivity MatchingActivityCrossingVariationGraph
open MatchingActivityCrossingVariationActual MatchingActivityCrossingVariationDerivative
open MatchingActivityCrossingVariationPressure MatchingActivityCrossingKernelRate
open MatchingActivityRadialSmallness MatchingActivityRadialLens TotalVariation
open MatchingActivityRadialCenterFirst MatchingActivityRadialModelCenterError
open MatchingActivityRadialDiameterError StrongPointwiseSteps SolScalarGap
open StrongPointwiseCoordinates StrongPointwiseSmallness MatchingActivityNonlocalPairs
open ActualCrossingGeometry NormalizedPolarRepresentation ExtremalPolarCenter SignedPressureRemainder
open SinglePressureEstimate StrongBudgetConsequences StrongObjectiveEstimate
open PolarAngleControl
open scoped BigOperators Topology ContDiff
noncomputable section

/-- Total variation gives the logarithmic energy bound at the exact scale of
the varied lens width. -/
theorem centerVelocity_pairEnergy_le {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (σ ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - LensClosure.midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in nhds (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath σ i t) ν r) (ξ t) = 0)
    (hw : 0 ≤ Lens.width (radialLength (by omega) θ r i) (ν i)) :
    pairEnergy (by omega) (centerVelocity (by omega) θ σ ν r ξ i) ≤
      (2 * m : ℝ) ^ 2 / 16 *
        (18 * Lens.width (radialLength (by omega) θ r i) (ν i)) ^ 2 *
          (1 + Real.log (2 * m : ℕ)) := by
  let U := centerVelocity (by omega) θ σ ν r ξ i
  have he := energyA_le_log (show 0 < 2 * m by omega)
    (periodize (by omega) U) (periodize_periodic (by omega) U)
  have hv := centerVelocity_variation_le_width hm θ σ ν r i ξ hσ hsmall hξ0 hξ hz hw
  have hv0 : 0 ≤ variation (2 * m) (periodize (by omega) U) := variation_nonneg _ _
  have hlog0 : 0 ≤ 1 + Real.log (2 * m : ℕ) := by
    have hn : (1 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 1 ≤ 2 * m by omega)
    linarith [Real.log_nonneg hn]
  change LocalDFT.energyA (2 * m) (periodize (by omega) U) ≤ _
  calc
    _ ≤ (2 * m : ℝ) ^ 2 / 16 *
        variation (2 * m) (periodize (by omega) U) ^ 2 *
          (1 + Real.log (2 * m : ℕ)) := by
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using he
    _ ≤ (2 * m : ℝ) ^ 2 / 16 *
        (18 * Lens.width (radialLength (by omega) θ r i) (ν i)) ^ 2 *
          (1 + Real.log (2 * m : ℕ)) := by
      gcongr

/-- Square-root form of the preceding estimate.  The factor `(2m)` is
cancelled by the normalization in the physical-center error. -/
theorem centerVelocity_sqrt_pairEnergy_le {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (σ ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - LensClosure.midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in nhds (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath σ i t) ν r) (ξ t) = 0)
    (hw : 0 ≤ Lens.width (radialLength (by omega) θ r i) (ν i)) :
    Real.sqrt (pairEnergy (by omega) (centerVelocity (by omega) θ σ ν r ξ i)) ≤
      (9 / 2 : ℝ) * (2 * m : ℝ) *
        Lens.width (radialLength (by omega) θ r i) (ν i) *
          Real.sqrt (1 + Real.log (2 * m : ℕ)) := by
  let U := centerVelocity (by omega) θ σ ν r ξ i
  let w := Lens.width (radialLength (by omega) θ r i) (ν i)
  let L := 1 + Real.log (2 * m : ℕ)
  have hE := centerVelocity_pairEnergy_le hm θ σ ν r i ξ hσ hsmall hξ0 hξ hz hw
  have hE0 : 0 ≤ pairEnergy (by omega) U := pairEnergy_nonneg _ _
  have hL0 : 0 ≤ L := by
    dsimp [L]
    have hn : (1 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 1 ≤ 2 * m by omega)
    linarith [Real.log_nonneg hn]
  have hR0 : 0 ≤ (9 / 2 : ℝ) * (2 * m : ℝ) * w * Real.sqrt L := by
    positivity
  have hsqrtE := Real.sq_sqrt hE0
  have hsqrtL := Real.sq_sqrt hL0
  have hsquare : ((9 / 2 : ℝ) * (2 * m : ℝ) * w * Real.sqrt L) ^ 2 =
      (2 * m : ℝ) ^ 2 / 16 * (18 * w) ^ 2 * L := by
    rw [mul_pow, mul_pow, mul_pow, hsqrtL]
    ring
  change Real.sqrt (pairEnergy (by omega) U) ≤
    (9 / 2 : ℝ) * (2 * m : ℝ) * w * Real.sqrt L
  dsimp [U, w, L] at hE ⊢
  nlinarith

/-- The base lens remains genuinely open when the matching radii are one and
the actual height is at its pointwise scale. -/
theorem model_lens_width_pos {m : ℕ} (hm : 8 ≤ m)
    (β : ℂ) (u : ℕ → ℂ) (ν : Fin m → ℝ)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hν : ∀ j, |ν j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hsat : ∀ j : Fin m, modelRadii m β u j = 1) (i : Fin m) :
    0 < Lens.width
      (radialLength (by omega) (normalizedAngle m u) (modelRadii m β u) i) (ν i) := by
  have hN : (0 : ℝ) < 2 * m := by positivity
  have ha := small_half_angle hm (normalizedAngle m u) hθ i
  apply width_positive_at_scale hN ha.2.1
  · rw [hsat i]
    norm_num
  · rw [hsat (nextIndex (by omega) i)]
    norm_num
  · rw [hsat i]
  · rw [hsat (nextIndex (by omega) i)]
  · exact ha.2.2
  · exact (hν i).trans (by
      apply one_div_le_one_div_of_le hN
      nlinarith)

/-- The localized pressure main term retains one eighth of the scaled
pointwise pressure after the phase and sine factors. -/
theorem pressure_main_abs_lower {m : ℕ} (hm : 2 ≤ m)
    {g w δ L : ℝ} (hw : 0 ≤ w) (hδ : |δ| ≤ 1 / 4)
    (hp : L ≤ (2 * m : ℝ) * |g|) :
    L * w / 8 ≤
      |g * w * Real.cos δ / Real.sin (Real.pi / (2 * m : ℝ))| := by
  have hN : (0 : ℝ) < 2 * m := by positivity
  have ha0 : 0 < Real.pi / (2 * m : ℝ) := by positivity
  have hapi : Real.pi / (2 * m : ℝ) < Real.pi := by
    exact div_lt_self Real.pi_pos (by exact_mod_cast (show 1 < 2 * m by omega))
  have hspos : 0 < Real.sin (Real.pi / (2 * m : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi ha0 hapi
  have hsle : Real.sin (Real.pi / (2 * m : ℝ)) ≤ Real.pi / (2 * m : ℝ) :=
    Real.sin_le ha0.le
  have hδpow := pow_le_pow_left₀ (abs_nonneg δ) hδ 2
  have hδsq : δ ^ 2 ≤ 1 / 16 := by
    rw [sq_abs] at hδpow
    norm_num at hδpow ⊢
    exact hδpow
  have hcos : (1 / 2 : ℝ) ≤ Real.cos δ := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := δ)]
  have hcos0 : 0 ≤ Real.cos δ := by linarith
  have hcoef : (2 * m : ℝ) / 8 * Real.sin (Real.pi / (2 * m : ℝ)) ≤
      Real.cos δ := by
    have hmul := mul_le_mul_of_nonneg_left hsle (by positivity : (0 : ℝ) ≤ (2 * m : ℝ) / 8)
    have he : (2 * m : ℝ) / 8 * (Real.pi / (2 * m : ℝ)) = Real.pi / 8 := by
      field_simp
    rw [he] at hmul
    linarith [Real.pi_lt_four]
  have hscaled : L * w / 8 ≤ (2 * m : ℝ) * |g| * w / 8 := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hw) (by norm_num)
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hw, abs_of_nonneg hcos0,
    abs_of_pos hspos]
  apply hscaled.trans
  apply (le_div_iff₀ hspos).2
  have hmul := mul_le_mul_of_nonneg_left hcoef (mul_nonneg (abs_nonneg g) hw)
  nlinarith

set_option maxHeartbeats 800000 in
/-- Under the explicit eventual numerical margin, a two-sided inactive-site
variation has nonzero genuine objective derivative. -/
theorem actual_inactive_crossing_derivative_ne_zero {m : ℕ} (hm : 8 ≤ m)
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
    centerFirst (modelDiameter m β u) (actualCenter m β u)
      (centerVelocity (by omega) (normalizedAngle m u) s ν
        (modelRadii m β u) ξ i) ≠ 0 := by
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
  have hganti : FiniteBox.Antiperiodic (by omega) g := by
    exact operator_antiperiodic (by omega) q
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
    β u s ν (modelRadii m β u) i ξ hu
    hb hθ hbudget hsmallD hsmallC hsmall hξ0 hξ hroot
  have hN : (0 : ℝ) < 2 * m := by positivity
  have herrscale : centerErrorConstant / (2 * m : ℝ) *
      Real.sqrt (pairEnergy (by omega)
        (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i)) ≤
      (9 / 2 : ℝ) * centerErrorConstant * w * Real.sqrt (1 + Real.log (2 * m : ℕ)) := by
    have hmultiply := mul_le_mul_of_nonneg_left hsqrt
      (div_nonneg centerErrorConstant_nonneg hN.le)
    calc
      _ ≤ centerErrorConstant / (2 * m : ℝ) *
          ((9 / 2 : ℝ) * (2 * m : ℝ) * w *
            Real.sqrt (1 + Real.log (2 * m : ℕ))) := hmultiply
      _ = _ := by field_simp
  intro hD
  change D = 0 at hD
  have hP : |P| ≤ (9 / 2 : ℝ) * centerErrorConstant * w *
      Real.sqrt (1 + Real.log (2 * m : ℕ)) := by
    have hh := herr.trans herrscale
    change |D - P| ≤ _ at hh
    rw [hD, zero_sub, abs_neg] at hh
    exact hh
  have hMupper : |M| ≤
      (8 * (31 * Real.pi / 64) +
        (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ))) * w := by
    calc
      |M| = |(M - P) + P| := by congr 1; ring
      _ ≤ |M - P| + |P| := abs_add_le _ _
      _ = |P - M| + |P| := by rw [abs_sub_comm]
      _ ≤ 8 * (31 * Real.pi / 64) * w +
          (9 / 2 : ℝ) * centerErrorConstant * w *
            Real.sqrt (1 + Real.log (2 * m : ℕ)) := add_le_add hloc hP
      _ = _ := by ring
  have hmarg := mul_lt_mul_of_pos_right hmargin hwpos
  change (8 * (31 * Real.pi / 64) +
      (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ))) * w <
    L / 8 * w at hmarg
  have hcontra : |M| < L * w / 8 := by
    calc
      _ ≤ _ := hMupper
      _ < L / 8 * w := hmarg
      _ = _ := by ring
  exact (not_lt_of_ge hmain) hcontra

/-- The explicit logarithmic pressure margin eventually dominates both the
fixed localization error and the square-root logarithmic center error. -/
theorem eventual_crossing_variation_margin : ∀ᶠ m : ℕ in atTop,
    8 * (31 * Real.pi / 64) +
        (9 / 2 : ℝ) * centerErrorConstant * Real.sqrt (1 + Real.log (2 * m : ℕ)) <
      ((Real.log ((((2 * m) / 4 : ℕ) : ℝ) + 1) - 1) / 16 -
        budgetConstant / 2) / 8 := by
  let A : ℝ := 8 * (31 * Real.pi / 64)
  let B : ℝ := (9 / 2) * centerErrorConstant
  let C : ℝ := (2 + Real.log 4) / 128 + budgetConstant / 16
  let R : ℝ := 128 * (A + B + C + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (by norm_num) centerErrorConstant_nonneg
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hC : 0 ≤ C := by
    dsimp [C]
    have := budgetConstant_nonneg
    positivity
  have hR : 128 ≤ R := by dsimp [R]; nlinarith
  have hN : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    have hd : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
      tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hd
  have hlog : Tendsto (fun m : ℕ => Real.log (2 * m : ℕ)) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] using
      Real.tendsto_log_atTop.comp hN
  have hadd : Tendsto (fun m : ℕ => Real.log (2 * m : ℕ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hlog
  have hsqrt : Tendsto (fun m : ℕ => Real.sqrt (1 + Real.log (2 * m : ℕ)))
      atTop atTop := by
    simpa only [Function.comp_def, add_comm] using Real.tendsto_sqrt_atTop.comp hadd
  filter_upwards [eventually_ge_atTop 8, hsqrt.eventually (eventually_gt_atTop R)]
    with m hm hx
  let x := Real.sqrt (1 + Real.log (2 * m : ℕ))
  let P : ℕ := (2 * m) / 4
  have hNm : (1 : ℝ) ≤ (2 * m : ℕ) := by exact_mod_cast (show 1 ≤ 2 * m by omega)
  have hlogN : 0 ≤ Real.log (2 * m : ℕ) := Real.log_nonneg hNm
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hxsq : x ^ 2 = 1 + Real.log (2 * m : ℕ) := by
    exact Real.sq_sqrt (by linarith)
  have hx1 : 1 ≤ x := by
    dsimp [x, R] at hx ⊢
    nlinarith [hA, hB, hC]
  have hNP : (2 * m : ℝ) ≤ 4 * (((P : ℕ) : ℝ) + 1) := by
    exact_mod_cast (show 2 * m ≤ 4 * (P + 1) by dsimp [P]; omega)
  have hPpos : (0 : ℝ) < ((P : ℕ) : ℝ) + 1 := by positivity
  have hNP' : (((2 * m : ℕ) : ℝ)) ≤ 4 * (((P : ℕ) : ℝ) + 1) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hNP
  have hlogcomp := Real.log_le_log (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ)) hNP'
  have hlogmul : Real.log (4 * (((P : ℕ) : ℝ) + 1)) =
      Real.log 4 + Real.log (((P : ℕ) : ℝ) + 1) := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hPpos.ne']
  rw [hlogmul] at hlogcomp
  have hlogP : x ^ 2 - 1 - Real.log 4 ≤
      Real.log (((P : ℕ) : ℝ) + 1) := by
    rw [hxsq]
    linarith
  have hxR : R < x := by simpa only [x] using hx
  have hquadratic : A + B * x + C < x ^ 2 / 128 := by
    have hcoef : A + B + C + 1 < x / 128 := by
      dsimp [R] at hxR
      nlinarith
    have hlinear : A + B * x + C ≤ (A + B + C) * x := by
      nlinarith [mul_nonneg (add_nonneg hA hC) (sub_nonneg.mpr hx1)]
    have hmul := mul_lt_mul_of_pos_right hcoef (by linarith : 0 < x)
    nlinarith
  dsimp [A, B, C, x, P] at hquadratic hlogP ⊢
  nlinarith

/-- A genuinely two-sided feasible path through a diameter maximizer has zero
logarithmic discriminant derivative. -/
theorem twoSided_log_derivative_eq_zero {n : ℕ} {x : Points n}
    (hx : ExtremalNormalization.DiameterExtremal x)
    {p : ℝ → Points n} {d : ℝ}
    (hp0 : p 0 = x)
    (hfeas : ∀ᶠ t in nhds (0 : ℝ), DiameterAtMost 2 (p t))
    (hinj : ∀ᶠ t in nhds (0 : ℝ), Function.Injective (p t))
    (hd : HasDerivAt (fun t => Real.log (discriminant (p t))) d 0) :
    d = 0 := by
  have hlocal : IsLocalMax (fun t => Real.log (discriminant (p t))) 0 := by
    change ∀ᶠ t in nhds (0 : ℝ),
      Real.log (discriminant (p t)) ≤ Real.log (discriminant (p 0))
    filter_upwards [hfeas, hinj] with t ht hti
    have hdisc : discriminant (p t) ≤ discriminant x := hx.2 (p t) ht
    have hpos : 0 < discriminant (p t) := discriminant_pos _ hti
    rw [← hp0] at hdisc
    exact Real.log_le_log hpos hdisc
  exact hlocal.hasDerivAt_eq_zero hd

set_option maxHeartbeats 800000 in
/-- At an actual normalized maximizer, both adjacent crossings at one site
cannot be simultaneously slack. -/
theorem model_not_both_crossings_strict {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hb : PointwiseBounds (m := m) (by omega) β u)
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
    (i : Fin m) :
    ¬(‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
      ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) := by
  rintro ⟨hplus, hminus⟩
  have hvar := model_inactive_crossing_variation hm h hz.1 hb hbudget
    hsmallB hsmallC hsmallR hsmallb hsat i hplus hminus
  obtain ⟨s, ν, ξ, hs, hi, hν, hsmall, hbase, hξ0, hξ, hpath, hv, hfeas⟩ := hvar
  obtain ⟨v, hv⟩ := hv
  have hroot : ∀ᶠ t in nhds (0 : ℝ),
      closureFamily (parameters (by omega) (normalizedAngle m u) (sigmaPath s i t) ν
        (modelRadii m β u)) (ξ t) = 0 := hfeas.mono (fun _ ht => ht.1)
  have hsmallC' : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2 := by
    calc
      _ = 2 * (physicalStepConstant / (2 * m : ℝ)) := by ring
      _ ≤ 2 * (1 / 1000 : ℝ) := mul_le_mul_of_nonneg_left hsmallC (by norm_num)
      _ ≤ _ := by norm_num
  have hne := actual_inactive_crossing_derivative_ne_zero hm h.periodic hb hθ hbudget
    hgap hpressure hsmallD hsmallC' hsat hmargin s ν ξ i hs hν hsmall hξ0 hξ hroot
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
  have hpinj : ∀ᶠ t in nhds (0 : ℝ), Function.Injective
      (crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
        (average (actualCenter m β u)) ξ i t) :=
    RadialObjectivePrice.eventually_injective_of_hasDerivAt hv (hbase ▸ hinj)
  have hdiam : ∀ᶠ t in nhds (0 : ℝ), DiameterAtMost 2
      (crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
        (average (actualCenter m β u)) ξ i t) := hfeas.mono (fun _ ht => ht.2.1)
  have hzero := twoSided_log_derivative_eq_zero
    (MatchingActivitySaturation.model_normalizedPoint_extremal h hz) hbase hdiam hpinj hd
  exact hne hzero

/-- At an actual normalized maximizer, matching saturation and the quantitative
crossing-variation margin force exactly one of the two adjacent crossing
constraints at a site to be active. -/
theorem model_exactly_one_crossing_active {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hb : PointwiseBounds (m := m) (by omega) β u)
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
    (i : Fin m) :
    (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2 ∧
      ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2) ∨
    (‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ < 2 ∧
      ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
          (actualCenter m β u) i‖ = 2) := by
  have hhalf : HalfPeriodic (by omega)
      (fun j => (normalizedAngle m u j : ℂ)) := by
    intro j
    exact congrArg Complex.ofReal (normalizedAngle_halfPeriodic (by omega) u h.periodic j)
  have hd : DiameterAtMost 2 (vertices (by omega) (normalizedAngle m u)
      (modelRadii m β u) (actualCenter m β u)) := by
    rw [model_vertices (by omega) β u h.periodic]
    exact model_diameter h hz.1
  have hle := crossing_constraints (show 0 < m by omega) (normalizedAngle m u)
    (modelRadii m β u) (actualCenter m β u) hhalf
    (actualCenter_halfPeriodic (by omega) β u h.periodic) hd i
  change ‖plusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i‖ ≤ 2 ∧
    ‖minusCrossingVector (by omega) (normalizedAngle m u) (modelRadii m β u)
      (actualCenter m β u) i‖ ≤ 2 at hle
  have hnotSlack := model_not_both_crossings_strict hm h hz hb hθ hbudget hgap
    hpressure hsmallB hsmallC hsmallR hsmallb hsmallD hsat hmargin i
  have hnotBoth := crossing_exclusive_of_matching hm (normalizedAngle m u)
    (modelRadii m β u) (actualCenter m β u) hsat hθ hb.2.2.2.2.2.2 hsmallC i
  rcases lt_or_eq_of_le hle.1 with hp | hp
  · right
    refine ⟨hp, le_antisymm hle.2 ?_⟩
    exact le_of_not_gt (fun hn => hnotSlack ⟨hp, hn⟩)
  · left
    refine ⟨hp, lt_of_le_of_ne hle.2 ?_⟩
    intro hn
    exact hnotBoth ⟨hp, hn⟩

/-- For every sufficiently large actual even-order maximizer, one and only one
of the two adjacent crossing constraints at each matching site is active, in
the same physical coordinates in which all matching constraints are active. -/
theorem eventual_diameter_exactly_one_crossing_active :
    ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ z : Points (2 * m),
      ExtremalNormalization.DiameterExtremal z →
      ∃ (hm : 0 < m) (π : Equiv.Perm (Fin (2 * m))) (α β : ℂ)
        (u : ℕ → ℂ) (η : ℝ),
        NormalizedRelativeEdgeModel z π α β u η ∧
        (∀ i : Fin m, modelRadii m β u i = 1) ∧
        (∀ k : Fin (2 * m), operator (2 * m) (polarConstraint hm β u) k ≠ 0) ∧
        ∀ i : Fin m,
          (‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
                (actualCenter m β u) i‖ = 2 ∧
            ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
                (actualCenter m β u) i‖ < 2) ∨
          (‖plusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
                (actualCenter m β u) i‖ < 2 ∧
            ‖minusCrossingVector hm (normalizedAngle m u) (modelRadii m β u)
                (actualCenter m β u) i‖ = 2) := by
  obtain ⟨m₀, h₀⟩ :=
    MatchingActivityCrossingPressure.eventual_diameter_matching_pressure_margin 0
  obtain ⟨m₁, h₁⟩ := eventually_atTop.1 eventual_coefficients_small
  obtain ⟨m₂, h₂⟩ := eventually_atTop.1
    MatchingActivitySaturation.eventual_radial_derivative_scales
  obtain ⟨m₃, h₃⟩ := eventually_atTop.1 eventual_crossing_variation_margin
  refine ⟨max (max (max m₀ m₁) m₂) (max m₃ 8), ?_⟩
  intro m hm z hz
  have hm₀ : m₀ ≤ m := by omega
  have hm₁ : m₁ ≤ 2 * m := by omega
  have hm₂ : m₂ ≤ 2 * m := by omega
  have hm₃ : m₃ ≤ m := by omega
  have hm8 : 8 ≤ m := by omega
  obtain ⟨hmp, π, α, β, u, η, hmodel, _, _, hpressure, hcombined,
      hbounds, hsat, hpressureMargin⟩ := h₀ m hm₀ z hz
  have hG0 : 0 ≤ G hmp (polarConstraint hmp β u) := gap_nonneg hmp _
  have hτ : 0 ≤ radialMass m β u := by
    unfold radialMass
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr
      (PolarRepresentation.model_radius_le_one hmp hmodel hz.1 j)
  have hD : 0 ≤ residualEnergy (by omega) (polarCenter m β u) :=
    pairEnergy_nonneg (by omega) _
  have hE : 0 ≤ DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) :=
    pairEnergy_nonneg (by omega) _
  have hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hcombined, hG0]
  have hgap : G hmp (polarConstraint hmp β u) ≤ budgetConstant / (2 * m : ℝ) ^ 2 := by
    linarith only [hcombined, hτ, hD, hE]
  have hs := h₁ (2 * m) hm₁
  have hd := h₂ (2 * m) hm₂
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hs hd
  have hθ := (model_nonlocal_smallness hm8 hmodel hz.1 hbounds hbudget
    hs.2.1 hs.2.2.1 hs.2.2.2.1).1
  refine ⟨hmp, π, α, β, u, η, hmodel, hsat, (fun k => (hpressureMargin k).2), ?_⟩
  intro i
  exact model_exactly_one_crossing_active hm8 hmodel hz hbounds hθ hbudget hgap
    hpressure hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2 hd.2.1 hsat (h₃ m hm₃) i

end
end StructuralNote.MatchingActivityCrossingVariationSaturation
