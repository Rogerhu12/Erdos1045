import StructuralNote.MatchingActivityCrossingVariationDerivative
import StructuralNote.CommonFiberNormalPairing
import StructuralNote.MatchingActivityRadialProjection
import StructuralNote.CommonFiberSparseVariation

/-! Localization of the Schur pressure work for a one-site crossing-control
variation.  The direct source is supported at the varied site; every other
term comes from the two-dimensional closure correction. -/

namespace StructuralNote.MatchingActivityCrossingVariationPressure

open Erdos1045 Erdos1045.EventualExact Complex
open FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum LensClosure
open CommonClosureEnergy CommonTangentialParameters BoxLensLift
open ClosedSourceIntegration MatchingActivityRadialProjection
open LensClosurePathDerivatives
open MatchingActivityCrossingVariationDerivative
open MatchingActivityRadialClosure MatchingActivityCrossingVariationGraph
open CommonFiberNormalPairing CommonFiberNormalAverage Filter
open TotalVariation CommonFiberSparseVariation
open scoped BigOperators Topology ContDiff
noncomputable section

theorem pressure_work_eq_corrected_sum {m : ℕ} (hm : 0 < m)
    (α σ ν : Fin m → ℝ) (v : ℂ) (source : Fin m → ℂ)
    (heq : closureDerivative α σ ν 0 v = -∑ j, source j)
    (g : Fin (2 * m) → ℝ) (hg : FiniteBox.Antiperiodic hm g) :
    finitePairing g
        (constraint (by omega) (integrateCorrected hm α σ ν 0 v source)) /
          (2 * m : ℝ) =
      (∑ j : Fin m, g (CommonClosureEnergy.halfIndex j) *
        MatchingActivityRadialProjection.normal (midpoint m j)
          (corrected α σ ν 0 v source j)) /
        Real.sin (Real.pi / (2 * m : ℝ)) := by
  let U := integrateCorrected hm α σ ν 0 v source
  have hU : HalfPeriodic hm U := by
    apply HessianAcceleration.integral_repeat_halfPeriodic
    exact corrected_sum α σ ν 0 v source heq
  have hc : FiniteBox.Antiperiodic hm (constraint (by omega) U) :=
    constraint_halfTurn hm U hU
  rw [antiperiodic_pairing_average hm g _ hg hc]
  unfold CommonFiberNormalAverage.average
  have hs (j : Fin m) :
      constraint (by omega) U (CommonClosureEnergy.halfIndex j) =
        (m : ℝ) / Real.sin (Real.pi / (2 * m : ℝ)) *
          MatchingActivityRadialProjection.normal (midpoint m j)
            (corrected α σ ν 0 v source j) := by
    rw [constraint]
    have hd := integrateCorrected_difference hm α σ ν 0 v source heq
    rw [hd]
    have hi : CommonClosureEnergy.halfIndex j = BoxLensLift.halfIndex j := rfl
    rw [hi, frame_halfIndex]
    simp only [repeatHalf, BoxLensLift.halfIndex, Fin.val_mk, Nat.mod_eq_of_lt j.isLt,
      Nat.cast_mul, Nat.cast_ofNat]
    unfold MatchingActivityRadialProjection.normal
    ring
  simp_rw [hs]
  rw [show (∑ x : Fin m, g (CommonClosureEnergy.halfIndex x) *
      ((m : ℝ) / Real.sin (Real.pi / (2 * m : ℝ)) *
        MatchingActivityRadialProjection.normal (midpoint m x)
          (corrected α σ ν 0 v source x))) =
      ((m : ℝ) / Real.sin (Real.pi / (2 * m : ℝ))) *
        ∑ x : Fin m, g (CommonClosureEnergy.halfIndex x) *
          MatchingActivityRadialProjection.normal (midpoint m x)
            (corrected α σ ν 0 v source x) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

theorem directSource_sum_norm {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (ν r : Fin m → ℝ) (i : Fin m)
    (hw : 0 ≤ Lens.width (radialLength hm θ r i) (ν i)) :
    (∑ j, ‖directSource hm θ ν r i j‖) =
      Lens.width (radialLength hm θ r i) (ν i) := by
  rw [Finset.sum_eq_single i]
  · exact directSource_self_norm hm θ ν r i hw
  · intro j _ hji
    rw [directSource_eq_zero hm θ ν r i j hji, norm_zero]
  · simp

theorem directSource_normal_self {m : ℕ} (hm : 0 < m)
    (θ : Fin (2 * m) → ℝ) (ν r : Fin m → ℝ) (i : Fin m) :
    MatchingActivityRadialProjection.normal (midpoint m i)
        (directSource hm θ ν r i i) =
      Lens.width (radialLength hm θ r i) (ν i) *
        Real.cos (radialPhase hm θ r i - midpoint m i) := by
  have hu : (starRingEnd ℂ) (unit (midpoint m i)) *
      unit (radialPhase hm θ r i) =
      unit (radialPhase hm θ r i - midpoint m i) := by
    have hone : (starRingEnd ℂ) (unit (midpoint m i)) * unit (midpoint m i) = 1 := by
      rw [mul_comm, Complex.mul_conj, normSq_eq_norm_sq, norm_unit]
      norm_num
    calc
      _ = (starRingEnd ℂ) (unit (midpoint m i)) *
          (unit (midpoint m i) * unit (radialPhase hm θ r i - midpoint m i)) := by
            rw [← CommonFiberGeometry.unit_add]
            congr 2
            ring
      _ = _ := by rw [← mul_assoc, hone, one_mul]
  simp only [directSource, controlSource, sigmaVelocity, if_true, one_mul,
    MatchingActivityRadialProjection.normal, ← mul_assoc, hu]
  rw [show unit (radialPhase hm θ r i - midpoint m i) *
      (Lens.width (radialLength hm θ r i) (ν i) : ℂ) =
    (Lens.width (radialLength hm θ r i) (ν i) : ℂ) *
      unit (radialPhase hm θ r i - midpoint m i) by ring]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, unit_re]

theorem pressure_work_localization {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (σ ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j,
      |radialPhase (by omega) θ r j - midpoint m j| +
        |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath σ i t) ν r) (ξ t) = 0)
    (g : Fin (2 * m) → ℝ) (hg : FiniteBox.Antiperiodic (by omega) g)
    {G ε : ℝ} (hG : ∀ j, |g j| ≤ G)
    (hε : ∀ j,
      |radialPhase (by omega) θ r j - midpoint m j| +
        |ν j| ≤ ε) :
    |finitePairing g (constraint (by omega)
        (centerVelocity (by omega) θ σ ν r ξ i)) / (2 * m : ℝ) -
      g (CommonClosureEnergy.halfIndex i) *
        Lens.width (radialLength (by omega) θ r i) (ν i) *
        Real.cos (radialPhase (by omega) θ r i - midpoint m i) /
          Real.sin (Real.pi / (2 * m : ℝ))| ≤
      G * ((m : ℝ) * ‖crossingRootSpeed ξ‖ * ε) /
        Real.sin (Real.pi / (2 * m : ℝ)) := by
  let α := radialPhase (by omega) θ r
  let source := directSource (by omega) θ ν r i
  let v := crossingRootSpeed ξ
  have heq := actual_closure_derivative hm θ σ ν r i ξ hsmall hξ0 hξ hz
  have hsine : 0 < Real.sin (Real.pi / (2 * m : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
      have hpi := Real.pi_pos
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * m)).2
      nlinarith
  change |finitePairing g (constraint (by omega)
      (integrateCorrected (by omega) α σ ν 0 v source)) / (2 * m : ℝ) - _| ≤ _
  rw [pressure_work_eq_corrected_sum (show 0 < m by omega) α σ ν v source heq g hg]
  have hdecomp :
      (∑ j : Fin m, g (CommonClosureEnergy.halfIndex j) *
        MatchingActivityRadialProjection.normal (midpoint m j)
          (corrected α σ ν 0 v source j)) -
        g (CommonClosureEnergy.halfIndex i) *
          Lens.width (radialLength (by omega) θ r i) (ν i) *
          Real.cos (radialPhase (by omega) θ r i - midpoint m i) =
      ∑ j : Fin m, g (CommonClosureEnergy.halfIndex j) *
        MatchingActivityRadialProjection.normal (midpoint m j)
          ((harmonicFunctional (midpoint m j) v : ℂ) *
            tangent (α j) (σ j) (ν j)) := by
    rw [show (∑ j : Fin m, g (CommonClosureEnergy.halfIndex j) *
        MatchingActivityRadialProjection.normal (midpoint m j)
          (corrected α σ ν 0 v source j)) =
      (∑ j : Fin m, g (CommonClosureEnergy.halfIndex j) *
        MatchingActivityRadialProjection.normal (midpoint m j) (source j)) +
      ∑ j : Fin m, g (CommonClosureEnergy.halfIndex j) *
        MatchingActivityRadialProjection.normal (midpoint m j)
          ((harmonicFunctional (midpoint m j) v : ℂ) *
            tangent (α j) (σ j) (ν j)) by
      simp only [corrected, MatchingActivityRadialProjection.normal, mul_add, add_re,
        heightParameter, map_zero, add_zero, Finset.sum_add_distrib]
      ]
    have hsource : (∑ j : Fin m, g (CommonClosureEnergy.halfIndex j) *
        MatchingActivityRadialProjection.normal (midpoint m j) (source j)) =
      g (CommonClosureEnergy.halfIndex i) *
        Lens.width (radialLength (by omega) θ r i) (ν i) *
        Real.cos (radialPhase (by omega) θ r i - midpoint m i) := by
      rw [Finset.sum_eq_single i]
      · rw [directSource_normal_self]
        ring
      · intro j _ hji
        dsimp only [source]
        rw [directSource_eq_zero (by omega) θ ν r i j hji]
        simp [MatchingActivityRadialProjection.normal]
      · simp
    rw [hsource]
    ring
  rw [div_sub_div_same, abs_div, abs_of_pos hsine]
  rw [hdecomp]
  have hG0 : 0 ≤ G :=
    (abs_nonneg (g (CommonClosureEnergy.halfIndex i))).trans (hG _)
  have hpoint (j : Fin m) :
      |g (CommonClosureEnergy.halfIndex j) * MatchingActivityRadialProjection.normal (midpoint m j)
        ((harmonicFunctional (midpoint m j) v : ℂ) *
          tangent (α j) (σ j) (ν j))| ≤
        G * (‖v‖ * ε) := by
    rw [abs_mul]
    apply mul_le_mul (hG _) ?_ (abs_nonneg _) hG0
    have hn : MatchingActivityRadialProjection.normal (midpoint m j)
        ((harmonicFunctional (midpoint m j) v : ℂ) * tangent (α j) (σ j) (ν j)) =
      harmonicFunctional (midpoint m j) v *
        MatchingActivityRadialProjection.normal (midpoint m j)
          (tangent (α j) (σ j) (ν j)) := by
      unfold MatchingActivityRadialProjection.normal
      rw [show (starRingEnd ℂ) (unit (midpoint m j)) *
          ((harmonicFunctional (midpoint m j) v : ℂ) * tangent (α j) (σ j) (ν j)) =
        (harmonicFunctional (midpoint m j) v : ℂ) *
          ((starRingEnd ℂ) (unit (midpoint m j)) * tangent (α j) (σ j) (ν j)) by ring]
      simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    rw [hn, abs_mul]
    exact mul_le_mul (harmonicFunctional_le_norm _ _)
      ((normal_tangent_bound (hσ j) (by
        linarith [hsmall j,
          abs_nonneg (radialPhase (by omega) θ r j -
            midpoint m j)])).trans (hε j))
      (abs_nonneg _) (norm_nonneg _)
  have hsum := (Finset.abs_sum_le_sum_abs (fun j : Fin m =>
    g (CommonClosureEnergy.halfIndex j) * MatchingActivityRadialProjection.normal (midpoint m j)
      ((harmonicFunctional (midpoint m j) v : ℂ) * tangent (α j) (σ j) (ν j)))
      Finset.univ).trans (Finset.sum_le_sum (fun j _ => hpoint j))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  apply div_le_div_of_nonneg_right _ hsine.le
  exact hsum.trans_eq (by dsimp only [v]; ring)

theorem crossingRootSpeed_le_width {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (σ ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath σ i t) ν r) (ξ t) = 0)
    (hw : 0 ≤ Lens.width (radialLength (by omega) θ r i) (ν i)) :
    ‖crossingRootSpeed ξ‖ ≤ (4 / m : ℝ) *
      Lens.width (radialLength (by omega) θ r i) (ν i) := by
  have hb := crossingRootSpeed_bound hm θ σ ν r i ξ hσ hsmall hξ0 hξ hz
  rw [directSource_sum_norm (show 0 < m by omega) θ ν r i hw] at hb
  exact hb

/-- The derivative has bounded total variation at the scale of the one local
source.  This is the sharper replacement for the cubic worst-case energy
bound when estimating the true objective remainder. -/
theorem centerVelocity_variation_le_width {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (σ ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath σ i t) ν r) (ξ t) = 0)
    (hw : 0 ≤ Lens.width (radialLength (by omega) θ r i) (ν i)) :
    variation (2 * m) (periodize (by omega)
      (centerVelocity (by omega) θ σ ν r ξ i)) ≤
        18 * Lens.width (radialLength (by omega) θ r i) (ν i) := by
  let α := radialPhase (by omega) θ r
  let source := directSource (by omega) θ ν r i
  let v := crossingRootSpeed ξ
  have heq := actual_closure_derivative hm θ σ ν r i ξ hsmall hξ0 hξ hz
  have hsmall' (j : Fin m) :
      |α j - midpoint m j| + |heightParameter ν 0 j| ≤ 1 / 4 := by
    simpa only [α, heightParameter, map_zero, add_zero] using hsmall j
  have hc := corrected_source_l1 hm α σ ν 0 v source hσ hsmall' heq
  change (∑ j, ‖corrected α σ ν 0 v source j‖) ≤
      9 * ∑ j, ‖source j‖ at hc
  rw [directSource_sum_norm (show 0 < m by omega) θ ν r i hw] at hc
  rw [variation_periodize]
  have hd := integrateCorrected_difference (show 0 < m by omega) α σ ν 0 v source heq
  change (∑ j, ‖difference (by omega)
    (integrateCorrected (by omega) α σ ν 0 v source) j‖) ≤ _
  rw [hd, repeatHalf_map_sum]
  linarith

theorem sine_grid_lower {m : ℕ} (hm : 1 ≤ m) :
    1 / (m : ℝ) ≤ Real.sin (Real.pi / (2 * m : ℝ)) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hx0 : 0 ≤ Real.pi / (2 * m : ℝ) := by positivity
  have hxpi : Real.pi / (2 * m : ℝ) ≤ Real.pi / 2 := by
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  have hs := Real.mul_le_sin hx0 hxpi
  calc
    1 / (m : ℝ) = (2 / Real.pi) * (Real.pi / (2 * m : ℝ)) := by
      field_simp [Real.pi_ne_zero, ne_of_gt hm0]
    _ ≤ _ := hs

/-- After inserting the closure inverse estimate, all nonlocal correction
terms cost only a fixed multiple of the local lens width. -/
theorem pressure_work_localization_scale {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (σ ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hσ : ∀ j, |σ j| ≤ 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hscale : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 2 / m)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath σ i t) ν r) (ξ t) = 0)
    (g : Fin (2 * m) → ℝ) (hg : FiniteBox.Antiperiodic (by omega) g)
    {G : ℝ} (hG : ∀ j, |g j| ≤ G)
    (hw : 0 ≤ Lens.width (radialLength (by omega) θ r i) (ν i)) :
    |finitePairing g (constraint (by omega)
        (centerVelocity (by omega) θ σ ν r ξ i)) / (2 * m : ℝ) -
      g (CommonClosureEnergy.halfIndex i) *
        Lens.width (radialLength (by omega) θ r i) (ν i) *
        Real.cos (radialPhase (by omega) θ r i - midpoint m i) /
          Real.sin (Real.pi / (2 * m : ℝ))| ≤
      8 * G * Lens.width (radialLength (by omega) θ r i) (ν i) := by
  have hsine := sine_grid_lower (show 1 ≤ m by omega)
  have hsine0 : 0 < Real.sin (Real.pi / (2 * m : ℝ)) :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / m) hsine
  have hG0 : 0 ≤ G :=
    (abs_nonneg (g (CommonClosureEnergy.halfIndex i))).trans (hG _)
  have hv := crossingRootSpeed_le_width hm θ σ ν r i ξ hσ hsmall hξ0 hξ hz hw
  have hloc := pressure_work_localization hm θ σ ν r i ξ hσ hsmall hξ0 hξ hz
    g hg hG hscale
  apply hloc.trans
  apply (div_le_iff₀ hsine0).2
  have hm0 : (0 : ℝ) < m := by positivity
  have hmul := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ G * (m : ℝ))
  have hscalei := hscale i
  have hscale0 : 0 ≤ 2 / (m : ℝ) := by positivity
  have heps : 0 ≤ 2 / (m : ℝ) := hscale0
  have hprod := mul_le_mul_of_nonneg_left hsine
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hG0) hw)
  calc
    G * ((m : ℝ) * ‖crossingRootSpeed ξ‖ * (2 / m)) ≤
        G * ((m : ℝ) * ((4 / m) *
          Lens.width (radialLength (by omega) θ r i) (ν i)) * (2 / m)) := by
          gcongr
    _ = 8 * G * Lens.width (radialLength (by omega) θ r i) (ν i) * (1 / m) := by
          field_simp
          ring
    _ ≤ 8 * G * Lens.width (radialLength (by omega) θ r i) (ν i) *
        Real.sin (Real.pi / (2 * m : ℝ)) := hprod

end
end StructuralNote.MatchingActivityCrossingVariationPressure
