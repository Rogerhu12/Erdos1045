import StructuralNote.MatchingActivityCrossingVariationActual
import StructuralNote.MatchingActivityRadialModelCenterError
import StructuralNote.RadialObjectivePrice
import StructuralNote.ClosedSourceIntegration
import StructuralNote.HessianAcceleration

/-! Explicit first derivatives of the one-site crossing-control graph. -/

namespace StructuralNote.MatchingActivityCrossingVariationDerivative

open Erdos1045 Erdos1045.EventualExact Complex Configuration CommonLocalization Filter
open LensClosure FiniteFourierLift FourierMultiplier SchurLift SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonTangentialParameters BoxLensLift
open MatchingActivityRadialClosure MatchingActivityRadialGeometry
open MatchingActivityRadialIntegration MatchingActivityRadialActual
open MatchingActivityCrossingVariationGraph
open MatchingActivityCrossingVariationActual
open LensIncrementDerivatives LensClosurePathDerivatives ClosedSourceIntegration
open MatchingActivityRadialCenterFirst MatchingActivityRadialObjectiveFirst
open MatchingActivityRadialModelCenterError MatchingActivityRadialDiameterError
open StrongPointwiseCoordinates StrongPointwiseSteps ExtremalPolarCenter NormalizedPolarRepresentation
open MatchingActivityNonlocalPairs
open SignedPressureRemainder StrongObjectiveEstimate SinglePressureEstimate
open LocalGradient
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 500000

def sigmaVelocity {m : ℕ} (i j : Fin m) : ℝ := if j = i then 1 else 0

theorem sigmaPath_hasDerivAt {m : ℕ} (s : Fin m → ℝ) (i j : Fin m) :
    HasDerivAt (fun t => sigmaPath s i t j) (sigmaVelocity i j) 0 := by
  by_cases hj : j = i
  · subst j
    simp only [sigmaPath, Function.update_self, sigmaVelocity, if_true]
    exact (hasDerivAt_id 0).const_add (s i)
  · simp only [sigmaPath, Function.update_of_ne hj, sigmaVelocity, if_neg hj]
    exact hasDerivAt_const 0 _

def controlSource (alpha L t s' : ℝ) : ℂ :=
  unit alpha * ((s' * Lens.width L t : ℝ) : ℂ)

/-- The derivative of one lens increment when both its control coordinate and
its height vary. -/
theorem increment_sigma_hasDerivAt {s t : ℝ → ℝ} {x s' t' : ℝ}
    (alpha L : ℝ) (hs : HasDerivAt s s' x) (ht : HasDerivAt t t' x)
    (hsmall : t x ^ 2 < 4) :
    HasDerivAt (fun y => increment alpha L (s y) (t y))
      (controlSource alpha L (t x) s' + (t' : ℂ) * tangent alpha (s x) (t x)) x := by
  have hh : HasDerivAt (fun y => Lens.width L (t y))
      (heightSlope (t x) * t') x := by
    have he := (height_hasDerivAt hsmall).comp x ht
    simpa only [Lens.width, heightSlope, Function.comp_apply] using he.sub_const L
  have hb := ((hs.mul hh).ofReal_comp).add (ht.ofReal_comp.mul_const I)
  have hd := hb.const_mul (unit alpha)
  change HasDerivAt (fun y => increment alpha L (s y) (t y)) _ x at hd
  apply hd.congr_deriv
  unfold controlSource tangent heightSlope
  push_cast
  ring

def crossingRootSpeed (ξ : ℝ → ℂ) : ℂ := deriv ξ 0

theorem crossingRootSpeed_hasDerivAt {ξ : ℝ → ℂ}
    (hξ : ContDiffAt ℝ ∞ ξ 0) : HasDerivAt ξ (crossingRootSpeed ξ) 0 := by
  exact (hξ.differentiableAt (by norm_num)).hasDerivAt

def directSource {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (ν r : Fin m → ℝ) (i j : Fin m) : ℂ :=
  controlSource (radialPhase hm θ r j) (radialLength hm θ r j) (ν j)
    (sigmaVelocity i j)

theorem directSource_eq_zero {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (ν r : Fin m → ℝ) (i j : Fin m) (hji : j ≠ i) :
    directSource hm θ ν r i j = 0 := by
  simp [directSource, controlSource, sigmaVelocity, hji]

theorem directSource_self_norm {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (ν r : Fin m → ℝ) (i : Fin m)
    (hw : 0 ≤ Lens.width (radialLength hm θ r i) (ν i)) :
    ‖directSource hm θ ν r i i‖ =
      Lens.width (radialLength hm θ r i) (ν i) := by
  simp only [directSource, controlSource, sigmaVelocity, if_true, one_mul, norm_mul,
    norm_unit, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]

/-- Differentiating the exact closure equation identifies the closure-root
velocity.  The right side is supported at the varied crossing site before the
two-dimensional closure correction is applied. -/
theorem actual_closure_derivative {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0) :
    closureDerivative (radialPhase (by omega) θ r) s ν 0 (crossingRootSpeed ξ) =
      -∑ j, directSource (by omega) θ ν r i j := by
  have hroot := crossingRootSpeed_hasDerivAt hξ
  have ht (j : Fin m) : ν j ^ 2 < 4 := by
    have hb : |ν j| ≤ 1 / 4 := by
      linarith [hsmall j, abs_nonneg (radialPhase (by omega) θ r j - midpoint m j)]
    nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have hd (j : Fin m) : HasDerivAt (fun t =>
      radialIncrement (by omega) θ (sigmaPath s i t) ν r (ξ t) j)
      (directSource (by omega) θ ν r i j +
        (harmonicFunctional (midpoint m j) (crossingRootSpeed ξ) : ℂ) *
          tangent (radialPhase (by omega) θ r j) (s j) (ν j)) 0 := by
    have hh := heightParameter_hasDerivAt
      (ν := fun _ : ℝ => ν) (ξ := ξ) (ν' := fun _ => 0)
      (fun j => hasDerivAt_const 0 (ν j)) hroot j
    have he := increment_sigma_hasDerivAt
      (radialPhase (by omega) θ r j) (radialLength (by omega) θ r j)
      (sigmaPath_hasDerivAt s i j) hh (by simpa only [hξ0, heightParameter,
        map_zero, add_zero] using (ht j))
    simpa only [radialIncrement, sigmaPath_zero, hξ0, heightParameter, map_zero,
      add_zero, zero_add, directSource] using he
  have hder := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hd j)
  have hder' : HasDerivAt (fun t =>
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t))
      ((∑ j, directSource (by omega) θ ν r i j) +
        closureDerivative (radialPhase (by omega) θ r) s ν 0 (crossingRootSpeed ξ)) 0 := by
    change HasDerivAt (fun t => ∑ j,
      radialIncrement (by omega) θ (sigmaPath s i t) ν r (ξ t) j) _ 0
    rw [closureDerivative_apply_sum]
    simpa only [heightParameter, map_zero, add_zero, Finset.sum_add_distrib] using hder
  have hconst : HasDerivAt (fun t =>
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t)) 0 0 :=
    (hasDerivAt_const 0 (0 : ℂ)).congr_of_eventuallyEq hz
  have he := hder'.unique hconst
  exact eq_neg_of_add_eq_zero_right he

def centerVelocity {m : ℕ} (hm : 0 < m) (θ : Fin (2 * m) → ℝ)
    (s ν r : Fin m → ℝ) (ξ : ℝ → ℂ) (i : Fin m) : Points (2 * m) :=
  integrateCorrected hm (radialPhase hm θ r) s ν 0 (crossingRootSpeed ξ)
    (directSource hm θ ν r i)

theorem radialCenter_hasDerivAt {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0)
    (j : Fin (2 * m)) :
    HasDerivAt (fun t => radialCenter (by omega) θ (sigmaPath s i t) ν r (ξ t) j)
      (centerVelocity (by omega) θ s ν r ξ i j) 0 := by
  have heq := actual_closure_derivative hm θ s ν r i ξ hsmall hξ0 hξ hz
  have hroot := crossingRootSpeed_hasDerivAt hξ
  have ht (k : Fin m) : ν k ^ 2 < 4 := by
    have hb : |ν k| ≤ 1 / 4 := by
      linarith [hsmall k, abs_nonneg (radialPhase (by omega) θ r k - midpoint m k)]
    nlinarith [(abs_le.mp hb).1, (abs_le.mp hb).2]
  have hd (k : Fin m) : HasDerivAt (fun t =>
      radialIncrement (by omega) θ (sigmaPath s i t) ν r (ξ t) k)
      (corrected (radialPhase (by omega) θ r) s ν 0 (crossingRootSpeed ξ)
        (directSource (by omega) θ ν r i) k) 0 := by
    have hh := heightParameter_hasDerivAt
      (ν := fun _ : ℝ => ν) (ξ := ξ) (ν' := fun _ => 0)
      (fun k => hasDerivAt_const 0 (ν k)) hroot k
    have he := increment_sigma_hasDerivAt
      (radialPhase (by omega) θ r k) (radialLength (by omega) θ r k)
      (sigmaPath_hasDerivAt s i k) hh (by simpa only [hξ0, heightParameter,
        map_zero, add_zero] using (ht k))
    simpa only [radialIncrement, sigmaPath_zero, hξ0, heightParameter, map_zero,
      add_zero, zero_add, corrected, directSource] using he
  unfold radialCenter centerVelocity integrateCorrected
  exact integral_hasDerivAt (repeatHalf_hasDerivAt (show 0 < m by omega) hd) j

theorem crossingPath_hasDerivAt {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ) (i : Fin m) (ξ : ℝ → ℂ)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0)
    (j : Fin (2 * m)) :
    HasDerivAt (fun t => crossingPath (by omega) θ s ν r a ξ i t j)
      (centerVelocity (by omega) θ s ν r ξ i j) 0 := by
  have hc := radialCenter_hasDerivAt hm θ s ν r i ξ hsmall hξ0 hξ hz j
  unfold crossingPath radialConfiguration vertices
  exact (hc.const_add ((radiusFull (by omega) r j : ℂ) * diameterVector θ j)).add_const a

/-- Exact derivative of the genuine objective along the crossing-control
graph.  Since the radii and angles are fixed, the entire first variation is
the physical-center term. -/
theorem crossingPath_log_derivative {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (a : ℂ) (i : Fin m) (ξ : ℝ → ℂ)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0)
    (D C : Points (2 * m))
    (hbase : crossingPath (by omega) θ s ν r a ξ i 0 =
      GeometricRelativeRemainder.configuration D C)
    (hinj : Function.Injective (GeometricRelativeRemainder.configuration D C)) :
    HasDerivAt (fun t => Real.log (discriminant
      (crossingPath (by omega) θ s ν r a ξ i t)))
      (centerFirst D C (centerVelocity (by omega) θ s ν r ξ i)) 0 := by
  have he := RadialObjectivePrice.hasDerivAt_log_discriminant_path
    (crossingPath_hasDerivAt hm θ s ν r a i ξ hsmall hξ0 hξ hz) (hbase ▸ hinj)
  rw [hbase] at he
  simpa only [centerFirst_eq_pairing] using he

theorem crossingRootSpeed_bound {m : ℕ} (hm : 2 ≤ m)
    (θ : Fin (2 * m) → ℝ) (s ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hs : ∀ j, |s j| ≤ 1)
    (hsmall : ∀ j, |radialPhase (by omega) θ r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) θ (sigmaPath s i t) ν r) (ξ t) = 0) :
    ‖crossingRootSpeed ξ‖ ≤ (4 / m : ℝ) * ∑ j, ‖directSource (by omega) θ ν r i j‖ := by
  have hsmall' (j : Fin m) : |radialPhase (by omega) θ r j - midpoint m j| +
      |heightParameter ν 0 j| ≤ 1 / 4 := by
    simpa only [heightParameter, map_zero, add_zero] using hsmall j
  exact correction_bound hm _ _ _ _ _ _ hs hsmall'
    (actual_closure_derivative hm θ s ν r i ξ hsmall hξ0 hξ hz)

/-- The available objective estimate has an explicit pressure main term and a
physical-center error.  Proving that the main term dominates this error in one
of the two `sigma` directions is the remaining sign estimate. -/
theorem model_crossing_objective_main_error {m : ℕ} (hm : 2 ≤ m)
    (β : ℂ) (u : ℕ → ℂ) (s ν r : Fin m → ℝ) (i : Fin m) (ξ : ℝ → ℂ)
    (hu : Function.Periodic u (2 * m))
    (hb : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallD : diameterStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmallC : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmall : ∀ j, |radialPhase (by omega) (normalizedAngle m u) r j - midpoint m j| + |ν j| ≤ 1 / 4)
    (hξ0 : ξ 0 = 0) (hξ : ContDiffAt ℝ ∞ ξ 0)
    (hz : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) (normalizedAngle m u) (sigmaPath s i t) ν r) (ξ t) = 0) :
    |centerFirst (modelDiameter m β u) (actualCenter m β u)
        (centerVelocity (by omega) (normalizedAngle m u) s ν r ξ i) -
      finitePairing (operator (2 * m) (polarConstraint (by omega) β u))
        (constraint (by omega) (centerVelocity (by omega) (normalizedAngle m u) s ν r ξ i)) /
          (2 * m : ℝ)| ≤
      centerErrorConstant / (2 * m : ℝ) *
        Real.sqrt (pairEnergy (by omega)
          (centerVelocity (by omega) (normalizedAngle m u) s ν r ξ i)) := by
  have heq := actual_closure_derivative hm (normalizedAngle m u) s ν r i ξ hsmall hξ0 hξ hz
  have hU : HalfPeriodic (by omega)
      (centerVelocity (by omega) (normalizedAngle m u) s ν r ξ i) := by
    apply HessianAcceleration.integral_repeat_halfPeriodic
    exact corrected_sum _ _ _ _ _ _ heq
  exact model_centerFirst_error hm β u hu hb hθ hbudget hsmallD hsmallC _ hU

/-- The preceding constructions specialize to the actual normalized
maximizer.  The logarithmic objective derivative exists, equals the genuine
physical-center first variation, and differs from its pressure pairing by the
displayed quantitative error. -/
theorem actual_inactive_crossing_objective_derivative {m : ℕ} (hm : 8 ≤ m)
    {z : Points (2 * m)} {π : Equiv.Perm (Fin (2 * m))} {α β : ℂ}
    {u : ℕ → ℂ} {η : ℝ}
    (h : Erdos1045.EventualExact.CommonLocalization.NormalizedRelativeEdgeModel z π α β u η)
    (hz : ExtremalNormalization.DiameterExtremal z)
    (hb : PointwiseBounds (m := m) (by omega) β u)
    (hθ : ∀ j, |normalizedAngle m u j| ≤ 1 / (1000 * (2 * m : ℝ)))
    (hbudget : radialMass m β u + residualEnergy (by omega) (polarCenter m β u) +
      DiscreteEnergy.realEnergy (by omega) (normalizedAngle m u) ≤
        budgetConstant / (2 * m : ℝ) ^ 2)
    (hsmallD : diameterStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (hsmallC : 2 * physicalStepConstant / (2 * m : ℝ) ≤ 1 / 2)
    (i : Fin m) (hvar : HasActualInactiveCrossingVariation (by omega) β u i) :
    ∃ (s ν : Fin m → ℝ) (ξ : ℝ → ℂ),
      |s i| < 1 ∧
      crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
          (MatchingActivityRadialIntegration.average (actualCenter m β u)) ξ i 0 =
        ActualCrossingGeometry.normalizedPoint m β u ∧
      HasDerivAt (fun t => Real.log (discriminant
        (crossingPath (by omega) (normalizedAngle m u) s ν (modelRadii m β u)
          (MatchingActivityRadialIntegration.average (actualCenter m β u)) ξ i t)))
        (centerFirst (modelDiameter m β u) (actualCenter m β u)
          (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i)) 0 ∧
      |centerFirst (modelDiameter m β u) (actualCenter m β u)
          (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i) -
        finitePairing (operator (2 * m) (polarConstraint (by omega) β u))
          (constraint (by omega) (centerVelocity (by omega) (normalizedAngle m u) s ν
            (modelRadii m β u) ξ i)) / (2 * m : ℝ)| ≤
        centerErrorConstant / (2 * m : ℝ) * Real.sqrt (pairEnergy (by omega)
          (centerVelocity (by omega) (normalizedAngle m u) s ν (modelRadii m β u) ξ i)) := by
  obtain ⟨s, ν, ξ, hs, hi, _, hsmall, hbase, hξ0, hξ, _, _, hfeas⟩ := hvar
  have hroot : ∀ᶠ t in 𝓝 (0 : ℝ),
      closureFamily (parameters (by omega) (normalizedAngle m u) (sigmaPath s i t) ν
        (modelRadii m β u)) (ξ t) = 0 := hfeas.mono (fun _ ht => ht.1)
  have hinj : Function.Injective (ActualCrossingGeometry.normalizedPoint m β u) := by
    apply HullGeometry.injective_of_discriminant_pos
    rw [MatchingActivitySaturation.model_discriminant_normalizedPoint h]
    exact (pow_pos (by positivity : (0 : ℝ) < ((2 * m : ℕ) : ℝ)) (2 * m)).trans_le
      (hz.discriminant_ge (by omega))
  have hdc : GeometricRelativeRemainder.configuration (modelDiameter m β u)
      (actualCenter m β u) = ActualCrossingGeometry.normalizedPoint m β u := by
    funext j
    simp only [GeometricRelativeRemainder.configuration, normalizedPoint_decomposition,
      modelDiameter]
  have hd := crossingPath_log_derivative (show 2 ≤ m by omega) (normalizedAngle m u)
    s ν (modelRadii m β u) (MatchingActivityRadialIntegration.average (actualCenter m β u))
    i ξ hsmall hξ0 hξ hroot (modelDiameter m β u) (actualCenter m β u)
    (hbase.trans hdc.symm) (hdc ▸ hinj)
  have herr := model_crossing_objective_main_error (show 2 ≤ m by omega) β u s ν
    (modelRadii m β u) i ξ h.periodic hb hθ hbudget hsmallD hsmallC hsmall hξ0 hξ hroot
  exact ⟨s, ν, ξ, hi, hbase, hd, herr⟩

end
end StructuralNote.MatchingActivityCrossingVariationDerivative
