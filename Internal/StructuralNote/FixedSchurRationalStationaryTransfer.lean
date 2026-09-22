import StructuralNote.FixedSchurRationalLagrangian
import StructuralNote.FixedSchurRationalWindowObjectiveTransfer
import StructuralNote.FixedSchurRationalRecoveryBounds
import StructuralNote.FixedSchurStrictCurvature
import StructuralNote.FixedSchurStationaryUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Second-order transfer from the literal rational closure manifold to the
fixed-Schur chart. -/

namespace StructuralNote.FixedSchurRationalStationaryTransfer

open Filter Matrix Complex Erdos1045 Erdos1045.EventualExact
open LensClosure FiniteFourierLift FourierMultiplier SchurSpectrum
open CommonClosureEnergy CommonFiberGeometry CommonRationalChart
open RationalCommonConfiguration RationalAngleBranch RationalChart
open RationalStationarySystem FixedSchurRationalClosureMatrix
open FixedSchurRationalLagrangian
open FixedSchurRationalClosurePaths FixedSchurRationalWindowClosureDerivative
open FixedSchurRationalRecovery FixedSchurRationalWindowObjectiveTransfer
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain FixedSchurEdgeGeometry
open FixedSchurRationalWindowRepresentation FixedSchurRationalRecoveryBounds
open FixedSchurChart FixedSchurChartSmooth FixedSchurLinear CommonDomainClosure
open CommonDomainRadius
open scoped Topology ContDiff BigOperators

noncomputable section

/-- At a critical point, the second derivative along a smooth path depends
only on its velocity.  This is the precise chain-rule statement that removes
the acceleration of a nonlinear coordinate change. -/
theorem second_deriv_comp_eq_affine_of_critical
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x u : E) (Z : ℝ → E)
    (hf : ContDiffAt ℝ 2 f x) (hZ : ContDiffAt ℝ 2 Z 0)
    (hZ0 : Z 0 = x) (hZu : deriv Z 0 = u)
    (hcritical : fderiv ℝ f x = 0) :
    deriv (deriv (fun t : ℝ ↦ f (Z t))) 0 =
      deriv (deriv (fun t : ℝ ↦ f (x + t • u))) 0 := by
  let L : ℝ → E := fun t ↦ x + t • u
  have hL : ContDiffAt ℝ 2 L 0 := by
    dsimp only [L]
    fun_prop
  have hL0 : L 0 = x := by simp [L]
  have hLu : deriv L 0 = u := by
    have h := ((hasDerivAt_id' (0 : ℝ)).smul_const u).const_add x
    change deriv (fun t : ℝ ↦ x + t • u) 0 = u
    simpa only [one_smul] using h.deriv
  have hfnear : ∀ᶠ y in nhds x, ContDiffAt ℝ 1 f y :=
    (hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have hZnear : ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ 1 Z t :=
    (hZ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have hLnear : ∀ᶠ t in nhds (0 : ℝ), ContDiffAt ℝ 1 L t :=
    (hL.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).eventually (by norm_num)
  have hZto : Tendsto Z (nhds 0) (nhds x) := by
    rw [← hZ0]
    exact hZ.continuousAt
  have hLto : Tendsto L (nhds 0) (nhds x) := by
    rw [← hL0]
    exact hL.continuousAt
  have hfirstZ : deriv (fun t ↦ f (Z t)) =ᶠ[nhds 0]
      fun t ↦ (fderiv ℝ f (Z t)) (deriv Z t) := by
    filter_upwards [hZto.eventually hfnear, hZnear] with t hft hZt
    rw [show (fun r ↦ f (Z r)) = f ∘ Z by rfl]
    exact fderiv_comp_deriv t (hft.differentiableAt (by norm_num))
      (hZt.differentiableAt (by norm_num))
  have hfirstL : deriv (fun t ↦ f (L t)) =ᶠ[nhds 0]
      fun t ↦ (fderiv ℝ f (L t)) (deriv L t) := by
    filter_upwards [hLto.eventually hfnear, hLnear] with t hft hLt
    rw [show (fun r ↦ f (L r)) = f ∘ L by rfl]
    exact fderiv_comp_deriv t (hft.differentiableAt (by norm_num))
      (hLt.differentiableAt (by norm_num))
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)).differentiableAt (by norm_num)
  have hcZ : HasDerivAt (fun t ↦ fderiv ℝ f (Z t))
      (fderiv ℝ (fderiv ℝ f) x u) 0 := by
    have houter : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (Z 0) := by
      simpa only [hZ0] using hDf.hasFDerivAt
    have hcomp := houter.comp_hasDerivAt 0
      (hZ.differentiableAt (by simp)).hasDerivAt
    simpa only [Function.comp_def, hZu] using hcomp
  have hcL : HasDerivAt (fun t ↦ fderiv ℝ f (L t))
      (fderiv ℝ (fderiv ℝ f) x u) 0 := by
    have houter : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (L 0) := by
      simpa only [hL0] using hDf.hasFDerivAt
    have hcomp := houter.comp_hasDerivAt 0
      (hL.differentiableAt (by simp)).hasDerivAt
    simpa only [Function.comp_def, hLu] using hcomp
  have hvZ : DifferentiableAt ℝ (deriv Z) 0 :=
    (hZ.derivWithin (m := (1 : ℕ∞ω)) (by norm_num)).differentiableAt (by norm_num)
  have hvL : DifferentiableAt ℝ (deriv L) 0 :=
    (hL.derivWithin (m := (1 : ℕ∞ω)) (by norm_num)).differentiableAt (by norm_num)
  have hsecondZ : deriv (fun t ↦ (fderiv ℝ f (Z t)) (deriv Z t)) 0 =
      (fderiv ℝ (fderiv ℝ f) x u) u := by
    have h := hcZ.clm_apply hvZ.hasDerivAt
    rw [h.deriv, hZ0, hZu, hcritical]
    simp only [_root_.zero_apply, add_zero]
  have hsecondL : deriv (fun t ↦ (fderiv ℝ f (L t)) (deriv L t)) 0 =
      (fderiv ℝ (fderiv ℝ f) x u) u := by
    have h := hcL.clm_apply hvL.hasDerivAt
    rw [h.deriv, hL0, hLu, hcritical]
    simp only [_root_.zero_apply, add_zero]
  change deriv (deriv (fun t : ℝ ↦ f (Z t))) 0 =
    deriv (deriv (fun t : ℝ ↦ f (L t))) 0
  rw [hfirstZ.deriv_eq, hfirstL.deriv_eq, hsecondZ, hsecondL]

/-- The physical selected-crossing coordinate used by the reverse map is
exactly the original rational stereographic unit after the normalization by
mean angle and base edge. -/
theorem relativeCrossing_normalized_eq_rotation {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega))
    (X : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0)
    (j : Fin m) :
    relativeCrossing hm s (theta (by omega) X)
        (normalizedCenter (by omega) (rationalSign s) X) j =
      RationalChart.rotation (RationalConfiguration.crossingParameter X j) := by
  have hdiff := normalizedCenter_half_difference (by omega : 0 < m)
    (rationalSign s) X hclosure j
  have hsign : rationalSign s j = 1 ∨ rationalSign s j = -1 :=
    FiniteBox.patternSign_is_sign s _
  have hcore :
      RationalConfiguration.diameter (by omega) X j +
          RationalConfiguration.diameter (by omega) X (j.val + 1) +
        ((rationalSign s j : ℝ) : ℂ) *
          RationalConfiguration.increment (by omega) (rationalSign s) X j =
        2 * RationalConfiguration.crossingUnit X j := by
    unfold RationalConfiguration.increment RationalChart.crossingIncrement
    rcases hsign with hs | hs <;> rw [hs] <;> norm_num
  have hvec :
      crossingVector hm (theta (by omega) X)
          (normalizedCenter (by omega) (rationalSign s) X)
          (FiniteBox.patternSign s) (halfIndex j) =
        unit (-angleMean (by omega) X) *
          (2 * RationalConfiguration.crossingUnit X j) := by
    unfold crossingVector
    rw [normalized_diameter, normalized_diameter,
      successor_half_val (by omega : 0 < m) j]
    change unit (-angleMean (by omega) X) *
          RationalConfiguration.diameter (by omega) X j +
        unit (-angleMean (by omega) X) *
          RationalConfiguration.diameter (by omega) X (j.val + 1) +
        ((rationalSign s j : ℝ) : ℂ) * difference (by omega)
          (normalizedCenter (by omega) (rationalSign s) X) (halfIndex j) = _
    rw [hdiff]
    calc
      _ = unit (-angleMean (by omega) X) *
          (RationalConfiguration.diameter (by omega) X j +
            RationalConfiguration.diameter (by omega) X (j.val + 1) +
            ((rationalSign s j : ℝ) : ℂ) *
              RationalConfiguration.increment (by omega) (rationalSign s) X j) := by ring
      _ = _ := by rw [hcore]
  unfold relativeCrossing
  rw [hvec, RationalSelectorRoundTrip.initialAngle_theta]
  unfold RationalConfiguration.crossingUnit
  let a := unit (-midpoint m j)
  let b := unit (- -angleMean (by omega) X)
  let c := unit (-angleMean (by omega) X)
  let d := unit (midpoint m j)
  let r := RationalChart.rotation (RationalConfiguration.crossingParameter X j)
  change a * b * (c * (2 * (d * r)) / 2) = r
  have hu : a * b * c * d = 1 := by
    dsimp only [a, b, c, d]
    rw [← unit_add, ← unit_add, ← unit_add]
    have he : -midpoint m j + - -angleMean (by omega) X +
        -angleMean (by omega) X + midpoint m j = 0 := by ring
    rw [he]
    simp [unit]
  calc
    a * b * (c * (2 * (d * r)) / 2) = (a * b * c * d) * r := by ring
    _ = r := by rw [hu, one_mul]

/-- On a closed point in the literal small rational window, the physical
fixed-Schur recovery returns every original rational coordinate. -/
theorem physical_recovery_parameters_eq {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega))
    (X : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0) :
    parameters hm s (theta (by omega) X)
      (normalizedCenter (by omega) (rationalSign s) X) = X := by
  funext i
  cases i with
  | inl k =>
      change Real.tan (relativeAngle (by omega) (theta (by omega) X)
        ⟨k.val + 1, by omega⟩ / 2) = X (.inl k)
      rw [RationalSelectorRoundTrip.relativeAngle_theta]
      unfold RationalAngleBranch.angle
      simp only [Nat.mod_eq_of_lt (show k.val + 1 < m by omega)]
      have he : 2 * Real.arctan
          (RationalConfiguration.angleParameter X ⟨k.val + 1, by omega⟩) / 2 =
          Real.arctan (RationalConfiguration.angleParameter X ⟨k.val + 1, by omega⟩) := by
        ring
      rw [he, Real.tan_arctan]
      simp only [RationalConfiguration.angleParameter, Nat.add_eq_zero_iff,
        Nat.one_ne_zero, and_false, dite_false]
      rfl
  | inr j =>
      change RationalChartInverse.parameter
        (relativeCrossing hm s (theta (by omega) X)
          (normalizedCenter (by omega) (rationalSign s) X) j) = X (.inr j)
      rw [relativeCrossing_normalized_eq_rotation hm s X hclosure,
        RationalChartInverse.parameter_rotation]
      rfl

private theorem canonicalLift_contDiff {n : ℕ} :
    ContDiff ℝ ∞ (SchurLift.canonicalLift : (Fin n → ℝ) → Fin n → ℂ) := by
  have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  have hre : ContDiff ℝ ∞ Complex.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ Complex.im := Complex.imCLM.contDiff
  have hcoefficient (p : Fin n) : ContDiff ℝ ∞
      (fun q : Fin n → ℝ => FiniteFourierLift.integralCoefficients
        (SchurLift.increment q) p) := by
    unfold FiniteFourierLift.integralCoefficients
    split
    · fun_prop
    · unfold FourierMultiplier.coefficient SchurLift.increment
        SchurLift.firstCoefficient
      fun_prop
  unfold SchurLift.canonicalLift FiniteFourierLift.integral
    FourierMultiplier.synthesis
  apply contDiff_pi.mpr
  intro j
  have hsum (S : Finset (Fin n)) : ContDiff ℝ ∞
      (fun q : Fin n → ℝ => ∑ p ∈ S,
        FiniteFourierLift.integralCoefficients (SchurLift.increment q) p *
          FourierMultiplier.character n p j) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; fun_prop
    | @insert a S ha ih =>
        simp only [Finset.sum_insert ha]
        exact ((hcoefficient a).mul contDiff_const).add ih
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum (Finset.univ : Finset (Fin n))

/-- The ambient center supplied by a smooth local model of the chosen
fixed-Schur root. -/
def modelCenter {m : ℕ}
    (g : FixedSchurEquationSmooth.SchurParameters m →
      FixedSchurEquationSmooth.SchurState m)
    (y : FixedSchurEquationSmooth.SchurParameters m) : Fin (2 * m) → ℂ :=
  FixedSchurLinear.center (g y) y.2

/-- The physical rational recovery, with the chosen root replaced locally by
its ambient smooth model. -/
def modelRecovery {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega))
    (g : FixedSchurEquationSmooth.SchurParameters m →
      FixedSchurEquationSmooth.SchurState m)
    (y : FixedSchurEquationSmooth.SchurParameters m) :
    RationalConfiguration.Variables m → ℝ :=
  parameters hm s y.1 (modelCenter g y)

theorem modelCenter_contDiffAt {m : ℕ}
    (g : FixedSchurEquationSmooth.SchurParameters m →
      FixedSchurEquationSmooth.SchurState m)
    (x : FixedSchurEquationSmooth.SchurParameters m)
    (hg : ContDiffAt ℝ ∞ g x) : ContDiffAt ℝ ∞ (modelCenter g) x := by
  unfold modelCenter FixedSchurLinear.center
  exact (canonicalLift_contDiff.contDiffAt.comp x hg).add contDiffAt_snd

/-- The ambient reverse chart is smooth at every point where its tangent and
stereographic denominators are nonzero. -/
theorem modelRecovery_contDiffAt {m : ℕ} (hm : 2 ≤ m)
    (s : FiniteBox.SignPattern (m := m) (by omega))
    (g : FixedSchurEquationSmooth.SchurParameters m →
      FixedSchurEquationSmooth.SchurState m)
    (x : FixedSchurEquationSmooth.SchurParameters m)
    (hg : ContDiffAt ℝ ∞ g x)
    (hangle : ∀ j : Fin m, Real.cos (relativeAngle (by omega) x.1 j / 2) ≠ 0)
    (hden : ∀ j, 1 + (relativeCrossing hm s x.1 (modelCenter g x) j).re ≠ 0) :
    ContDiffAt ℝ ∞ (modelRecovery hm s g) x := by
  have hcenter := modelCenter_contDiffAt g x hg
  have hrelative (j : Fin m) : ContDiffAt ℝ ∞
      (fun y : FixedSchurEquationSmooth.SchurParameters m =>
        relativeCrossing hm s y.1 (modelCenter g y) j) x := by
    have hcast : ContDiff ℝ ∞ (Complex.ofReal : ℝ → ℂ) := Complex.ofRealCLM.contDiff
    have hinit : ContDiffAt ℝ ∞
        (fun y : FixedSchurEquationSmooth.SchurParameters m =>
          initialAngle (by omega) y.1) x := by
      unfold initialAngle
      fun_prop
    unfold relativeCrossing crossingVector CommonFiberGeometry.diameterVector
      LensClosure.unit FiniteFourierLift.successor initialAngle
    fun_prop
  unfold modelRecovery FixedSchurRationalRecovery.parameters
    RationalParameterRecovery.parameters
  apply contDiffAt_pi.mpr
  intro i
  cases i with
  | inl k =>
      change ContDiffAt ℝ ∞ (fun y : FixedSchurEquationSmooth.SchurParameters m =>
        Real.tan (relativeAngle (by omega) y.1 ⟨k.val + 1, by omega⟩ / 2)) x
      let a := fun y : FixedSchurEquationSmooth.SchurParameters m =>
        relativeAngle (by omega) y.1 ⟨k.val + 1, by omega⟩ / 2
      have ha : ContDiffAt ℝ ∞ a x := by
        dsimp only [a]
        unfold relativeAngle initialAngle
        fun_prop
      have ht : ContDiffAt ℝ ∞ Real.tan (a x) := by
        apply Real.contDiffAt_tan.2
        simpa only [a] using hangle ⟨k.val + 1, by omega⟩
      have hc := ht.comp x ha
      simpa only [Function.comp_def, a] using hc
  | inr j =>
      change ContDiffAt ℝ ∞ (fun y : FixedSchurEquationSmooth.SchurParameters m =>
        RationalChartInverse.parameter (relativeCrossing hm s y.1 (modelCenter g y) j)) x
      unfold RationalChartInverse.parameter
      have him := Complex.imCLM.contDiff.contDiffAt.comp x (hrelative j)
      have hre := Complex.reCLM.contDiff.contDiffAt.comp x (hrelative j)
      have hd := him.div (contDiffAt_const.add hre) (hden j)
      convert hd using 1 <;> rfl

/-- At every closed strict single-window point, the chosen fixed-Schur chart
has an actual smooth rational inverse.  It maps nearby points of the chosen
domain to exact rational closure, and it is a left inverse on nearby closed
single-window rational points. -/
theorem eventual_exists_smooth_local_recovery : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (X : RationalConfiguration.Variables m → ℝ),
      selectedWindowEnergy (by omega) s X <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
      let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
      ∃ g : FixedSchurEquationSmooth.SchurParameters m →
          FixedSchurEquationSmooth.SchurState m,
        ContDiffAt ℝ ∞ g x ∧ modelRecovery (show 2 ≤ m by omega) s g x = X ∧
        ContDiffAt ℝ ∞ (modelRecovery (show 2 ≤ m by omega) s g) x ∧
        (∀ᶠ y in nhds x, y ∈ FixedSchurChartSmooth.domain (by omega) →
          RationalConfiguration.closure (by omega) (rationalSign s)
              (modelRecovery (show 2 ≤ m by omega) s g y) = 0 ∧
            fixedSchurCoordinates (show 2 ≤ m by omega) s
              (modelRecovery (show 2 ≤ m by omega) s g y) = y) ∧
        (∀ᶠ Y in nhds X,
          selectedWindowEnergy (by omega) s Y <
              (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
          RationalConfiguration.closure (by omega) (rationalSign s) Y = 0 →
          modelRecovery (show 2 ≤ m by omega) s g
            (fixedSchurCoordinates (show 2 ≤ m by omega) s Y) = Y) := by
  filter_upwards [FixedSchurChartSmooth.eventual_local_model,
    eventual_selectedWindow_representation,
    eventual_fixedSchurCoordinates_inDomain,
    eventual_recovery_data,
    eventual_coordinate_properties] with m hmodel hrep hdomain hdata hprops
  intro hm s X hwindow hclosure
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    hdomain hm s X hwindow
  obtain ⟨g, hgx, hg, hglocal⟩ := hmodel (by omega) s x hx
  have hrepresentation := hrep (show 2 ≤ m by omega) s X hwindow hclosure
  have hCx : modelCenter g x =
      normalizedCenter (by omega) (rationalSign s) X := by
    change center (g x) x.2 = _
    rw [hgx]
    exact hrepresentation.2.1.symm
  have hangle (j : Fin m) :
      Real.cos (relativeAngle (by omega) x.1 j / 2) ≠ 0 := by
    have he : relativeAngle (by omega) x.1 j = RationalAngleBranch.angle (by omega) X j := by
      dsimp only [x, fixedSchurCoordinates]
      exact RationalSelectorRoundTrip.relativeAngle_theta (by omega) X j
    rw [he]
    unfold RationalAngleBranch.angle
    simp only [Nat.mod_eq_of_lt j.isLt]
    have he' : 2 * Real.arctan (RationalConfiguration.angleParameter X j) / 2 =
        Real.arctan (RationalConfiguration.angleParameter X j) := by ring
    rw [he', Real.cos_arctan]
    positivity
  have hden (j : Fin m) :
      1 + (relativeCrossing (show 2 ≤ m by omega) s x.1 (modelCenter g x) j).re ≠ 0 := by
    rw [hCx]
    dsimp only [x, fixedSchurCoordinates]
    rw [relativeCrossing_normalized_eq_rotation (show 2 ≤ m by omega) s X hclosure]
    exact (RationalChart.one_add_rotation_re_pos _).ne'
  have hrecover : modelRecovery (show 2 ≤ m by omega) s g x = X := by
    unfold modelRecovery
    rw [hCx]
    dsimp only [x, fixedSchurCoordinates]
    exact physical_recovery_parameters_eq (show 2 ≤ m by omega) s X hclosure
  have hsmooth := modelRecovery_contDiffAt (show 2 ≤ m by omega) s g x hg hangle hden
  have hforward : ∀ᶠ y in nhds x,
      y ∈ FixedSchurChartSmooth.domain (by omega) →
      RationalConfiguration.closure (by omega) (rationalSign s)
          (modelRecovery (show 2 ≤ m by omega) s g y) = 0 ∧
        fixedSchurCoordinates (show 2 ≤ m by omega) s
          (modelRecovery (show 2 ≤ m by omega) s g y) = y := by
    filter_upwards [hglocal] with y hgy hy
    have hgeq : g y = coordinate (by omega) s y.1 y.2 := hgy.2.2 hy
    have hReq : modelRecovery (show 2 ≤ m by omega) s g y =
        parameters (show 2 ≤ m by omega) s y.1
          (center (coordinate (by omega) s y.1 y.2) y.2) := by
      simp only [modelRecovery, modelCenter, hgeq]
    have hd := hdata (show 2 ≤ m by omega) s y.1 y.2 hy
    dsimp only at hd
    rw [hReq]
    refine ⟨hd.2.2.1, ?_⟩
    apply Prod.ext
    · exact hd.1
    · dsimp only [fixedSchurCoordinates]
      rw [hd.2.1]
      exact (hprops (show 2 ≤ m by omega) s y.1 y.2 hy).free_projection
  have hcoordContinuous : ContinuousAt
      (fixedSchurCoordinates (show 2 ≤ m by omega) s) X :=
    (fixedSchurCoordinates_differentiable (show 2 ≤ m by omega) s X).continuousAt
  have hback : ∀ᶠ Y in nhds X,
      selectedWindowEnergy (by omega) s Y <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalConfiguration.closure (by omega) (rationalSign s) Y = 0 →
      modelRecovery (show 2 ≤ m by omega) s g
        (fixedSchurCoordinates (show 2 ≤ m by omega) s Y) = Y := by
    have hnear := hcoordContinuous.tendsto.eventually hglocal
    filter_upwards [hnear] with Y hY hYwindow hYclosure
    let y := fixedSchurCoordinates (show 2 ≤ m by omega) s Y
    have hy : y ∈ FixedSchurChartSmooth.domain (by omega) :=
      hdomain hm s Y hYwindow
    have hgeq : g y = coordinate (by omega) s y.1 y.2 := hY.2.2 hy
    have hYrep := hrep (show 2 ≤ m by omega) s Y hYwindow hYclosure
    have hcenter : modelCenter g y =
        normalizedCenter (by omega) (rationalSign s) Y := by
      change center (g y) y.2 = _
      rw [hgeq]
      exact hYrep.2.1.symm
    unfold modelRecovery
    rw [hcenter]
    dsimp only [y, fixedSchurCoordinates]
    exact physical_recovery_parameters_eq (show 2 ≤ m by omega) s Y hYclosure
  exact ⟨g, hg, hrecover, hsmooth, hforward, hback⟩

private theorem constraint_differentiable {n : ℕ} (hn : 0 < n) :
    Differentiable ℝ (SchurLift.constraint hn : (Fin n → ℂ) → Fin n → ℝ) := by
  unfold SchurLift.constraint FiniteFourierLift.difference
  fun_prop

private theorem constraint_fderiv_apply {n : ℕ} (hn : 2 ≤ n)
    (C h : Fin n → ℂ) :
    fderiv ℝ (SchurLift.constraint (by omega)) C h =
      SchurLift.constraint (by omega) h := by
  have hout := (constraint_differentiable (show 0 < n by omega) C).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => C + t • h) h 0 := by
    simpa only [one_smul] using ((hasDerivAt_id' (0 : ℝ)).smul_const h).const_add C
  have houter : HasFDerivAt (SchurLift.constraint (by omega))
      (fderiv ℝ (SchurLift.constraint (by omega)) C) (C + (0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using hout
  have hc := houter.comp_hasDerivAt 0 hline
  have he : (fun t : ℝ => SchurLift.constraint (by omega) (C + t • h)) =
      fun t => SchurLift.constraint (by omega) C + t • SchurLift.constraint (by omega) h := by
    funext t
    rw [show C + t • h = fun j => ((1 : ℝ) : ℂ) * C j + ((t : ℝ) : ℂ) * h j by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, Complex.real_smul,
        Complex.ofReal_one, one_mul]]
    rw [CommonDomainConvexity.constraint_linear (show 0 < n by omega)]
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, one_mul, smul_eq_mul]
  have hr : HasDerivAt
      (fun t : ℝ => SchurLift.constraint (by omega) C +
        t • SchurLift.constraint (by omega) h)
      (SchurLift.constraint (by omega) h) 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id' (0 : ℝ)).smul_const
        (SchurLift.constraint (by omega) h)).const_add
          (SchurLift.constraint (by omega) C)
  have hc' : HasDerivAt (fun t : ℝ =>
      SchurLift.constraint (by omega) (C + t • h))
      (fderiv ℝ (SchurLift.constraint (by omega)) C h) 0 := by
    simpa only [Function.comp_def] using hc
  have hr' : HasDerivAt (fun t : ℝ =>
      SchurLift.constraint (by omega) (C + t • h))
      (SchurLift.constraint (by omega) h) 0 := by
    rw [he]
    exact hr
  have hd := hc'.unique hr'
  exact hd

/-- The derivative of a path that locally remains in the linear fixed-Schur
gauge is an admissible fixed-Schur direction. -/
theorem admissible_deriv_of_eventually {m : ℕ} (hm : 0 < m)
    (P : ℝ → FixedSchurEquationSmooth.SchurParameters m)
    (hP : DifferentiableAt ℝ P 0)
    (hmem : ∀ᶠ t in nhds (0 : ℝ),
      CommonFiberCanonicalDirections.Admissible hm (P t)) :
    CommonFiberCanonicalDirections.Admissible hm (deriv P 0) := by
  let d := deriv P 0
  have hPd : HasDerivAt P d 0 := hP.hasDerivAt
  have hfst : HasDerivAt (fun t => (P t).1) d.1 0 := by
    have h := hPd.hasFDerivAt.fst.hasDerivAt
    simpa using h
  have hsnd : HasDerivAt (fun t => (P t).2) d.2 0 := by
    have h := hPd.hasFDerivAt.snd.hasDerivAt
    simpa using h
  have hfstj (j : Fin (2 * m)) : HasDerivAt (fun t => (P t).1 j) (d.1 j) 0 :=
    hasDerivAt_pi.mp hfst j
  have hsndj (j : Fin (2 * m)) : HasDerivAt (fun t => (P t).2 j) (d.2 j) 0 :=
    hasDerivAt_pi.mp hsnd j
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have he : (fun t => (P t).1 (halfTurn hm j)) =ᶠ[nhds 0]
        fun t => (P t).1 j := by
      filter_upwards [hmem] with t ht
      exact Complex.ofReal_injective (ht.1 j)
    have hdj := he.deriv_eq
    rw [(hfstj (halfTurn hm j)).deriv, (hfstj j).deriv] at hdj
    exact congrArg Complex.ofReal hdj
  · have hcast (j : Fin (2 * m)) : HasDerivAt
        (fun t => ((P t).1 j : ℂ)) ((d.1 j : ℝ) : ℂ) 0 :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hfstj j)
    have hsum := HasDerivAt.fun_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 * m)))) => hcast j)
    have he : (fun t => ∑ j, ((P t).1 j : ℂ)) =ᶠ[nhds 0]
        fun _ : ℝ => 0 := by
      filter_upwards [hmem] with t ht
      exact ht.2.1
    have hz := he.deriv_eq
    rw [hsum.deriv, deriv_const] at hz
    exact hz
  · refine ⟨?_, ?_, ?_⟩
    · intro j
      have he : (fun t => (P t).2 (halfTurn hm j)) =ᶠ[nhds 0]
          fun t => (P t).2 j := by
        filter_upwards [hmem] with t ht
        exact ht.2.2.1 j
      have hdj := he.deriv_eq
      rw [(hsndj (halfTurn hm j)).deriv, (hsndj j).deriv] at hdj
      exact hdj
    · have hsum := HasDerivAt.fun_sum
        (fun j (_ : j ∈ (Finset.univ : Finset (Fin (2 * m)))) => hsndj j)
      have he : (fun t => ∑ j, (P t).2 j) =ᶠ[nhds 0]
          fun _ : ℝ => 0 := by
        filter_upwards [hmem] with t ht
        exact ht.2.2.2.1
      have hz := he.deriv_eq
      rw [hsum.deriv, deriv_const] at hz
      exact hz
    · have hout := (constraint_differentiable (show 0 < 2 * m by omega)
          (P 0).2).hasFDerivAt
      have hc := hout.comp_hasDerivAt 0 hsnd
      have he : (fun t => SchurLift.constraint (by omega) ((P t).2)) =ᶠ[nhds 0]
          fun _ : ℝ => 0 := by
        filter_upwards [hmem] with t ht
        exact ht.2.2.2.2
      have hz := he.deriv_eq
      rw [show (fun t => SchurLift.constraint (by omega) ((P t).2)) =
          (SchurLift.constraint (by omega)) ∘ (fun t => (P t).2) by rfl,
        hc.deriv, constraint_fderiv_apply (show 2 ≤ 2 * m by omega), deriv_const] at hz
      exact hz

/-- A vector killed by the two-row closure matrix is killed by the full
complex-valued Fréchet derivative of closure. -/
theorem closureFDeriv_eq_zero_of_matrix_mulVec_eq_zero {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (X u : RationalConfiguration.Variables m → ℝ)
    (hu : closureMatrix hm σ X *ᵥ u = 0) :
    FixedSchurRationalWindowClosureDerivative.closureFDeriv hm
      (RationalConfigurationPolynomials.sign σ) X u = 0 := by
  apply Complex.ext
  · have h := congrFun hu (0 : Fin 2)
    rw [closureMatrix_mulVec] at h
    norm_num [component] at h ⊢
    exact h
  · have h := congrFun hu (1 : Fin 2)
    rw [closureMatrix_mulVec] at h
    norm_num [component] at h ⊢
    exact h

/-- On the literal closure manifold, the actual Lagrangian equals the
rational logarithmic objective. -/
theorem lagrangianValue_eq_objective_of_closure {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ)
    (X : RationalConfiguration.Variables m → ℝ)
    (hclosure : RationalConfiguration.closure hm
      (RationalConfigurationPolynomials.sign σ) X = 0) :
    lagrangianValue hm σ μ X = RationalStationarySystem.objective hm σ X := by
  have hce : ∀ k, (closureCoordinate hm σ k).eval X = 0 :=
    (closure_equations_iff hm σ X).2 hclosure
  unfold lagrangianValue
  simp only [hce, mul_zero, Finset.sum_const_zero, sub_zero]

/-- An actual stationary solution of the literal rational system in the
strict single window is stationary in the chosen fixed-Schur chart. -/
theorem eventual_rational_stationary_fixed : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (Y : RationalStationarySystem.Variables m → ℝ),
      selectedWindowEnergy (by omega) s (RationalStationarySystem.coordinates Y) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalStationarySystem.Stationary (by omega) (halfWord s) Y →
      FixedSchurStationaryUniqueness.Stationary (by omega) s
        (fixedSchurCoordinates (show 2 ≤ m by omega) s
          (RationalStationarySystem.coordinates Y)) := by
  filter_upwards [eventual_exists_smooth_local_recovery,
    eventual_objective_path_deriv_eq,
    eventual_selectedWindow_collisionFree,
    eventual_fixedSchurCoordinates_inDomain] with m hrecovery hobjective hcollision hdomain
  intro hm s Y hwindow hstationary
  let X := RationalStationarySystem.coordinates Y
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  obtain ⟨g, hg, hrecover, hsmooth, hforward, _⟩ :=
    hrecovery hm s X hwindow hclosure
  intro d hd
  let A : ℝ → FixedSchurEquationSmooth.SchurParameters m :=
    fun t => CommonFiberCanonicalPaths.affinePath x d t
  let Z : ℝ → (RationalConfiguration.Variables m → ℝ) :=
    fun t => modelRecovery (show 2 ≤ m by omega) s g (A t)
  have hA : ContDiffAt ℝ ∞ A 0 := by
    dsimp only [A]
    exact CommonFiberCanonicalPaths.affinePath_contDiff x d |>.contDiffAt
  have hA0 : A 0 = x := by
    simp only [A, CommonFiberCanonicalPaths.affinePath, zero_smul, add_zero]
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) := by
    exact hdomain hm s X hwindow
  have hAdom : ∀ᶠ t in nhds (0 : ℝ), A t ∈
      FixedSchurChartSmooth.domain (by omega) := by
    simpa only [A, CommonFiberCanonical.domain, FixedSchurChartSmooth.domain] using
      CommonFiberCanonicalDirections.affine_domain_near_zero (by omega) x d hx hd
  have hAto : Tendsto A (nhds 0) (nhds x) := by
    rw [← hA0]
    exact hA.continuousAt
  have hforwardA := hAto.eventually hforward
  have hclosed : ∀ᶠ t in nhds (0 : ℝ),
      RationalConfiguration.closure (by omega) (rationalSign s) (Z t) = 0 := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).1
  have hcoords : ∀ᶠ t in nhds (0 : ℝ),
      fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t) = A t := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).2
  have hZ : ContDiffAt ℝ ∞ Z 0 := by
    have hsmooth' : ContDiffAt ℝ ∞
        (modelRecovery (show 2 ≤ m by omega) s g) (A 0) := by
      simpa only [hA0] using hsmooth
    exact hsmooth'.comp 0 hA
  have hZ0 : Z 0 = X := by
    dsimp only [Z]
    rw [hA0]
    exact hrecover
  have hfree : CollisionFree (by omega) (halfWord s) X :=
    hcollision hm s X hwindow hclosure
  have hcrit := stationary_lagrangian_fderiv_zero (by omega) (halfWord s) Y hfree hstationary
  have hlagSmooth := lagrangianValue_contDiffAt (by omega) (halfWord s)
    (multiplier Y) X hfree
  have hlagDeriv : deriv (fun t => lagrangianValue (by omega) (halfWord s)
      (multiplier Y) (Z t)) 0 = 0 := by
    have houter : DifferentiableAt ℝ
        (lagrangianValue (by omega) (halfWord s) (multiplier Y)) (Z 0) := by
      simpa only [hZ0] using hlagSmooth.differentiableAt (by simp)
    rw [show (fun t => lagrangianValue (by omega) (halfWord s)
        (multiplier Y) (Z t)) =
      lagrangianValue (by omega) (halfWord s) (multiplier Y) ∘ Z by rfl,
      fderiv_comp_deriv 0 houter (hZ.differentiableAt (by simp)), hZ0, hcrit]
    exact _root_.zero_apply _
  have hlagObj : (fun t => lagrangianValue (by omega) (halfWord s)
      (multiplier Y) (Z t)) =ᶠ[nhds 0]
      fun t => RationalStationarySystem.objective (by omega) (halfWord s) (Z t) := by
    filter_upwards [hclosed] with t ht
    have hce : ∀ k, (closureCoordinate (by omega) (halfWord s) k).eval (Z t) = 0 := by
      apply (closure_equations_iff (by omega) (halfWord s) (Z t)).2
      rwa [sign_halfWord]
    unfold lagrangianValue
    simp only [hce, mul_zero, Finset.sum_const_zero, sub_zero]
  have hratZero : deriv (fun t => RationalStationarySystem.objective
      (by omega) (halfWord s) (Z t)) 0 = 0 := by
    rw [← hlagObj.deriv_eq]
    exact hlagDeriv
  have htransfer := hobjective hm s Z 0 hZ.continuousAt
    (by simpa only [hZ0] using hwindow) hclosed
  have hfixedAffine : (fun t => FixedSchurObjectivePaths.objective (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t))) =ᶠ[nhds 0]
      fun t => FixedSchurObjectivePaths.objective (by omega) s (A t) := by
    filter_upwards [hcoords] with t ht
    rw [ht]
  calc
    deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s
        (CommonFiberCanonicalPaths.affinePath x d t)) 0 =
        deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s (A t)) 0 := by rfl
    _ = deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s
        (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t))) 0 :=
      hfixedAffine.deriv_eq.symm
    _ = deriv (fun t => RationalStationarySystem.objective
        (by omega) (halfWord s) (Z t)) 0 := htransfer.symm
    _ = 0 := hratZero

/-- At an actual rational stationary point in the selected window, the
literal Lagrangian Hessian is strictly negative on every nonzero tangent
direction to the literal closure equations. -/
theorem eventual_rational_lagrangianHessian_negative : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (Y : RationalStationarySystem.Variables m → ℝ),
      selectedWindowEnergy (by omega) s (RationalStationarySystem.coordinates Y) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      RationalStationarySystem.Stationary (by omega) (halfWord s) Y →
      ∀ u : RationalConfiguration.Variables m → ℝ,
        closureMatrix (by omega) (halfWord s)
            (RationalStationarySystem.coordinates Y) *ᵥ u = 0 →
        u ≠ 0 →
        u ⬝ᵥ (RationalBorderedJacobian.lagrangianHessian (by omega) (halfWord s)
            (RationalStationarySystem.coordinates Y)
            (RationalStationarySystem.multiplier Y) *ᵥ u) < 0 := by
  filter_upwards [eventual_selectedWindow_closure_hasFDerivAt_surjective,
    eventual_exists_smooth_local_recovery,
    eventual_objective_path_second_deriv_eq,
    FixedSchurStrictCurvature.eventual_affine_strict_curvature,
    eventual_selectedWindow_collisionFree,
    eventual_fixedSchurCoordinates_inDomain] with m hfull hrecovery hobjective hcurvature
      hcollision hdomain
  intro hm s Y hwindow hstationary u hukernel hune
  let X := RationalStationarySystem.coordinates Y
  let x := fixedSchurCoordinates (show 2 ≤ m by omega) s X
  have hclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  have honto : Function.Surjective
      (closureFDeriv (by omega) (rationalSign s) X) :=
    (hfull hm s X hwindow hclosure).2
  have huclosure : closureFDeriv (by omega) (rationalSign s) X u = 0 := by
    rw [← sign_halfWord]
    exact closureFDeriv_eq_zero_of_matrix_mulVec_eq_zero
      (by omega) (halfWord s) X u hukernel
  obtain ⟨Z, hZ0, hZsmooth, hZclosed, hZderiv⟩ :=
    exists_smooth_closed_path (by omega) (rationalSign s) X u hclosure honto huclosure
  obtain ⟨g, hg, hrecover, hsmooth, hforward, hback⟩ :=
    hrecovery hm s X hwindow hclosure
  let P : ℝ → FixedSchurEquationSmooth.SchurParameters m :=
    fun t => fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t)
  have hP0 : P 0 = x := by
    dsimp only [P, x]
    rw [hZ0]
  have hPdiff : DifferentiableAt ℝ P 0 := by
    have hout : DifferentiableAt ℝ
        (fixedSchurCoordinates (show 2 ≤ m by omega) s) (Z 0) :=
      fixedSchurCoordinates_differentiable (show 2 ≤ m by omega) s (Z 0)
    exact hout.comp 0 (hZsmooth.differentiableAt (by simp))
  have henergy : ContinuousAt
      (fun t => selectedWindowEnergy (by omega) s (Z t)) 0 :=
    (selectedWindowEnergy_differentiable (by omega) s).continuous.continuousAt.comp
      hZsmooth.continuousAt
  have hwindowNear : ∀ᶠ t in nhds (0 : ℝ),
      selectedWindowEnergy (by omega) s (Z t) <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    have hwindow0 : selectedWindowEnergy (by omega) s (Z 0) <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
      simpa only [hZ0] using hwindow
    exact henergy.tendsto.eventually (eventually_lt_nhds hwindow0)
  have hPadmissible : ∀ᶠ t in nhds (0 : ℝ),
      CommonFiberCanonicalDirections.Admissible (by omega) (P t) := by
    filter_upwards [hwindowNear] with t ht
    have hPt := hdomain hm s (Z t) ht
    exact ⟨hPt.1, hPt.2.1, hPt.2.2.1⟩
  let d := deriv P 0
  have hd : CommonFiberCanonicalDirections.Admissible (by omega) d :=
    admissible_deriv_of_eventually (by omega) P hPdiff hPadmissible
  let R : FixedSchurEquationSmooth.SchurParameters m →
      (RationalConfiguration.Variables m → ℝ) :=
    modelRecovery (show 2 ≤ m by omega) s g
  have hRdiff : DifferentiableAt ℝ R x := by
    simpa only [R, x] using hsmooth.differentiableAt (by simp)
  have hZto : Tendsto Z (nhds 0) (nhds X) := by
    rw [← hZ0]
    exact hZsmooth.continuousAt
  have hbackZ := hZto.eventually hback
  have hRP_eq_Z : (fun t => R (P t)) =ᶠ[nhds 0] Z := by
    filter_upwards [hbackZ, hwindowNear, hZclosed] with t hb hw hc
    exact hb hw hc
  have hR_d_eq_u : fderiv ℝ R x d = u := by
    calc
      fderiv ℝ R x d = deriv (fun t => R (P t)) 0 := by
        rw [show (fun t => R (P t)) = R ∘ P by rfl,
          fderiv_comp_deriv 0 (by simpa only [hP0] using hRdiff) hPdiff]
        simp only [hP0, d]
      _ = deriv Z 0 := hRP_eq_Z.deriv_eq
      _ = u := hZderiv
  have hdne : d ≠ 0 := by
    intro hdzero
    have hu0 : u = 0 := by
      rw [hdzero, map_zero] at hR_d_eq_u
      exact hR_d_eq_u.symm
    exact hune hu0
  let A : ℝ → FixedSchurEquationSmooth.SchurParameters m :=
    fun t => CommonFiberCanonicalPaths.affinePath x d t
  let W : ℝ → (RationalConfiguration.Variables m → ℝ) := fun t => R (A t)
  have hA : ContDiffAt ℝ ∞ A 0 := by
    dsimp only [A]
    exact CommonFiberCanonicalPaths.affinePath_contDiff x d |>.contDiffAt
  have hA0 : A 0 = x := by
    simp only [A, CommonFiberCanonicalPaths.affinePath, zero_smul, add_zero]
  have hx : x ∈ FixedSchurChartSmooth.domain (by omega) :=
    hdomain hm s X hwindow
  have hAdom : ∀ᶠ t in nhds (0 : ℝ),
      A t ∈ FixedSchurChartSmooth.domain (by omega) := by
    simpa only [A, CommonFiberCanonical.domain, FixedSchurChartSmooth.domain] using
      CommonFiberCanonicalDirections.affine_domain_near_zero (by omega) x d hx hd
  have hAto : Tendsto A (nhds 0) (nhds x) := by
    rw [← hA0]
    exact hA.continuousAt
  have hforwardA := hAto.eventually hforward
  have hWclosed : ∀ᶠ t in nhds (0 : ℝ),
      RationalConfiguration.closure (by omega) (rationalSign s) (W t) = 0 := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).1
  have hWcoords : ∀ᶠ t in nhds (0 : ℝ),
      fixedSchurCoordinates (show 2 ≤ m by omega) s (W t) = A t := by
    filter_upwards [hforwardA, hAdom] with t ht htdom
    exact (ht htdom).2
  have hWsmooth : ContDiffAt ℝ ∞ W 0 := by
    have hsmooth' : ContDiffAt ℝ ∞ R (A 0) := by
      simpa only [hA0] using hsmooth
    exact hsmooth'.comp 0 hA
  have hW0 : W 0 = X := by
    dsimp only [W, R]
    rw [hA0]
    exact hrecover
  have hAderiv : deriv A 0 = d := by
    dsimp only [A, CommonFiberCanonicalPaths.affinePath]
    simpa only [one_smul] using
      (((hasDerivAt_id' (0 : ℝ)).smul_const d).const_add x).deriv
  have hWderiv : deriv W 0 = u := by
    rw [show W = R ∘ A by rfl,
      fderiv_comp_deriv 0 (by simpa only [hA0] using hRdiff)
        (hA.differentiableAt (by simp)), hA0, hAderiv]
    exact hR_d_eq_u
  have hfree : CollisionFree (by omega) (halfWord s) X :=
    hcollision hm s X hwindow hclosure
  have hcritical := stationary_lagrangian_fderiv_zero
    (by omega) (halfWord s) Y hfree hstationary
  have hlagSmooth := lagrangianValue_contDiffAt (by omega) (halfWord s)
    (multiplier Y) X hfree
  have hpathAffine := second_deriv_comp_eq_affine_of_critical
    (lagrangianValue (by omega) (halfWord s) (multiplier Y)) X u W
    (hlagSmooth.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    (hWsmooth.of_le
      (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
    hW0 hWderiv hcritical
  have hlagObj : (fun t => lagrangianValue (by omega) (halfWord s)
      (multiplier Y) (W t)) =ᶠ[nhds 0]
      fun t => RationalStationarySystem.objective (by omega) (halfWord s) (W t) := by
    filter_upwards [hWclosed] with t ht
    apply lagrangianValue_eq_objective_of_closure
    rwa [sign_halfWord]
  have htransfer := hobjective hm s W 0 hWsmooth.continuousAt
    (by simpa only [hW0] using hwindow) hWclosed
  have hfixedAffine : (fun t => FixedSchurObjectivePaths.objective (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s (W t))) =ᶠ[nhds 0]
      fun t => FixedSchurObjectivePaths.objective (by omega) s (A t) := by
    filter_upwards [hWcoords] with t ht
    rw [ht]
  have hstrict : deriv (deriv (fun t => FixedSchurObjectivePaths.objective
      (by omega) s (A t))) 0 < 0 := by
    apply hcurvature (show 2 ≤ m by omega) s x d 0
    · simpa only [A, CommonFiberCanonicalPaths.affinePath, zero_smul, add_zero] using hx
    · exact hd
    · exact hdne
  calc
    u ⬝ᵥ (RationalBorderedJacobian.lagrangianHessian (by omega) (halfWord s)
        X (multiplier Y) *ᵥ u) =
        deriv (deriv (fun t => lagrangianValue (by omega) (halfWord s)
          (multiplier Y) (FixedSchurRationalLagrangian.affineVariables X u t))) 0 :=
      lagrangianHessian_quadratic_eq_second (by omega) (halfWord s)
        (multiplier Y) X u hfree
    _ = deriv (deriv (fun t => lagrangianValue (by omega) (halfWord s)
          (multiplier Y) (W t))) 0 := hpathAffine.symm
    _ = deriv (deriv (fun t => RationalStationarySystem.objective
          (by omega) (halfWord s) (W t))) 0 := hlagObj.deriv.deriv_eq
    _ = deriv (deriv (fun t => FixedSchurObjectivePaths.objective
          (by omega) s (fixedSchurCoordinates (show 2 ≤ m by omega) s (W t)))) 0 := htransfer
    _ = deriv (deriv (fun t => FixedSchurObjectivePaths.objective
          (by omega) s (A t))) 0 := hfixedAffine.deriv.deriv_eq
    _ < 0 := hstrict

/-- Therefore the Jacobian of the literal square rational stationary system
is nonsingular at every stationary solution in the selected window. -/
theorem eventual_selectedWindow_stationary_jacobian_nonsingular :
    ∀ᶠ m : ℕ in atTop,
      ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
        (Y : RationalStationarySystem.Variables m → ℝ),
        selectedWindowEnergy (by omega) s (RationalStationarySystem.coordinates Y) <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalStationarySystem.Stationary (by omega) (halfWord s) Y →
        (RationalSystemAlgebraicity.jacobian
          (RationalStationarySystem.systemExpression (by omega) (halfWord s)) Y).det ≠ 0 := by
  filter_upwards [eventual_rational_lagrangianHessian_negative,
    eventual_selectedWindow_closureMatrix_surjective,
    eventual_selectedWindow_collisionFree] with m hnegative hsurjective hcollision
  intro hm s Y hwindow hstationary
  let X := RationalStationarySystem.coordinates Y
  have hclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  apply RationalBorderedJacobian.stationary_jacobian_nonsingular
  · exact hcollision hm s X hwindow hclosure
  · exact hsurjective hm s X hwindow hclosure
  · intro u hu hune
    exact hnegative hm s Y hwindow hstationary u hu hune

end
end StructuralNote.FixedSchurRationalStationaryTransfer
