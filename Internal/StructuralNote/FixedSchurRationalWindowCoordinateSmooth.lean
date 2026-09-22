import StructuralNote.FixedSchurRationalWindowClosureDerivative
import StructuralNote.CommonRationalRecovery
import StructuralNote.RationalSelectorRoundTrip
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Smooth coordinate changes between the literal rational chart and the
mean-angle, mean-center common-fiber gauge. -/

namespace StructuralNote.FixedSchurRationalWindowCoordinateSmooth

open Erdos1045 Erdos1045.EventualExact Complex
open LensClosure FiniteFourierLift SchurSpectrum CommonClosureEnergy
open CommonTangentialParameters CommonFiberGeometry CommonRationalChart
open RationalCommonConfiguration RationalAngleBranch RationalBranchRecovery
open scoped BigOperators Topology
noncomputable section

/-- Ambient coordinates for the mean-angle, mean-center common-fiber gauge. -/
abbrev CommonCoordinates (m : ℕ) :=
  (Fin (2 * m) → ℝ) × (Fin (2 * m) → ℂ) × ℂ

/-- The actual removal of the rational chart's base-edge rotation and center
translation, including the recovered positive-branch tangential data. -/
def rationalForward {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    (RationalConfiguration.Variables m → ℝ) → CommonCoordinates m :=
  fun X => (theta hm X, recoveredVector hm σ X, recoveredCorrection hm σ X)

/-- The literal rational parameter recovery map from the common-fiber gauge. -/
def rationalRecovery {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    CommonCoordinates m → (RationalConfiguration.Variables m → ℝ) :=
  fun p => CommonRationalChart.parameters hm p.1 p.2.1 σ p.2.2

@[fun_prop] private theorem angle_differentiable {m : ℕ} (hm : 0 < m) (j : ℕ) :
    Differentiable ℝ (fun X : RationalConfiguration.Variables m → ℝ => angle hm X j) := by
  unfold angle RationalConfiguration.angleParameter
  split
  · fun_prop
  · intro X
    exact ((Real.differentiableAt_arctan _).comp X (by fun_prop)).const_mul 2

private theorem angleMean_differentiable {m : ℕ} (hm : 0 < m) :
    Differentiable ℝ (angleMean hm) := by
  unfold angleMean
  fun_prop (disch := assumption)

@[fun_prop] private theorem crossingArctan_differentiable {m : ℕ} (j : Fin m) :
    Differentiable ℝ (fun X : RationalConfiguration.Variables m → ℝ =>
      Real.arctan (X (.inr j))) := by
  intro X
  exact (Real.differentiableAt_arctan _).comp X (by fun_prop)

private theorem crossingOffset_differentiable {m : ℕ} (hm : 0 < m) (j : Fin m) :
    Differentiable ℝ (fun X : RationalConfiguration.Variables m → ℝ =>
      crossingOffset hm X j) := by
  unfold crossingOffset RationalConfiguration.crossingParameter
  fun_prop

private theorem tangential_differentiable {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (j : Fin m) :
    Differentiable ℝ (fun X : RationalConfiguration.Variables m → ℝ =>
      tangential hm σ X j) := by
  unfold tangential
  exact (differentiable_const _).mul
    ((Real.differentiable_sin.comp (crossingOffset_differentiable hm j)).const_mul 2)

/-- The forward map is globally differentiable: its rotation removal uses
`arctan`, while tangential recovery uses only finite linear operations and
`sin`. -/
theorem rationalForward_differentiable {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) :
    Differentiable ℝ (rationalForward hm σ) := by
  have hθ : Differentiable ℝ (theta hm) := by
    unfold theta
    apply differentiable_pi.mpr
    intro j
    exact (angle_differentiable hm j).sub (angleMean_differentiable hm)
  have ht : Differentiable ℝ (fun X : RationalConfiguration.Variables m → ℝ =>
      tangential hm σ X) := by
    apply differentiable_pi.mpr
    exact tangential_differentiable hm σ
  have hc : Differentiable ℝ (RationalBranchRecovery.correction :
      (Fin m → ℝ) → ℂ) := by
    have hre : Differentiable ℝ (fun t : Fin m → ℝ =>
        2 / (m : ℝ) * ∑ j, t j * Real.cos (midpoint m j)) := by
      fun_prop (disch := aesop)
    have him : Differentiable ℝ (fun t : Fin m → ℝ =>
        2 / (m : ℝ) * ∑ j, t j * Real.sin (midpoint m j)) := by
      fun_prop (disch := aesop)
    change Differentiable ℝ (fun t : Fin m → ℝ => Complex.equivRealProdCLM.symm
      (2 / (m : ℝ) * ∑ j, t j * Real.cos (midpoint m j),
        2 / (m : ℝ) * ∑ j, t j * Real.sin (midpoint m j)))
    exact Complex.equivRealProdCLM.symm.differentiable.comp (hre.prodMk him)
  have hf : Differentiable ℝ (RationalBranchRecovery.freeCoordinates :
      (Fin m → ℝ) → Fin m → ℝ) := by
    unfold RationalBranchRecovery.freeCoordinates
    apply differentiable_pi.mpr
    intro j
    exact (by fun_prop : Differentiable ℝ (fun t : Fin m → ℝ => t j)).sub
      ((harmonicFunctional (midpoint m j)).differentiable.comp hc)
  have hr : Differentiable ℝ (CommonTangentialParameters.reconstruct hm) := by
    have hintegralCoefficient (p : Fin (2 * m)) : Differentiable ℝ
        (fun ν : Fin m → ℝ => FiniteFourierLift.integralCoefficients
          (BoxLensLift.repeatHalf hm (CommonTangentialParameters.halfIncrement ν)) p) := by
      unfold FiniteFourierLift.integralCoefficients
      split
      · fun_prop
      · unfold FourierMultiplier.coefficient BoxLensLift.repeatHalf
          CommonTangentialParameters.halfIncrement
        fun_prop (disch := aesop)
    unfold CommonTangentialParameters.reconstruct FiniteFourierLift.integral
      FourierMultiplier.synthesis
    apply differentiable_pi.mpr
    intro j
    have hsum (S : Finset (Fin (2 * m))) : Differentiable ℝ (fun ν : Fin m → ℝ =>
        ∑ p ∈ S, FiniteFourierLift.integralCoefficients
            (BoxLensLift.repeatHalf hm (CommonTangentialParameters.halfIncrement ν)) p *
          FourierMultiplier.character (2 * m) p j) := by
      induction S using Finset.induction_on with
      | empty => simp only [Finset.sum_empty]; fun_prop
      | @insert a S ha ih =>
          simp only [Finset.sum_insert ha]
          exact ((hintegralCoefficient a).mul_const _).add ih
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      hsum (Finset.univ : Finset (Fin (2 * m)))
  change Differentiable ℝ (fun X : RationalConfiguration.Variables m → ℝ =>
    (theta hm X,
      (CommonTangentialParameters.reconstruct hm)
        (RationalBranchRecovery.freeCoordinates (tangential hm σ X)),
      RationalBranchRecovery.correction (tangential hm σ X)))
  exact hθ.prodMk ((hr.comp (hf.comp ht)).prodMk (hc.comp ht))

@[fun_prop] private theorem unit_comp_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => unit (f y)) x := by
  unfold unit
  exact ((Complex.ofRealCLM.differentiableAt.comp x hf).mul_const I).cexp

@[fun_prop] private theorem equivRealProd_symm_comp_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun y => Complex.equivRealProdCLM.symm (f y, g y)) x :=
  Complex.equivRealProdCLM.symm.differentiableAt.comp x (hf.prodMk hg)

@[fun_prop] private theorem height_comp_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hsmall : f x ^ 2 < 4) :
    DifferentiableAt ℝ (fun y => Lens.height (f y)) x := by
  have hroot : 4 - f x ^ 2 ≠ 0 := by nlinarith
  unfold Lens.height
  fun_prop (disch := assumption)

@[fun_prop] private theorem tan_comp_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hcos : Real.cos (f x) ≠ 0) :
    DifferentiableAt ℝ (fun y => Real.tan (f y)) x := by
  rw [show (fun y => Real.tan (f y)) =
      fun y => Real.sin (f y) / Real.cos (f y) by
    funext y
    exact Real.tan_eq_sin_div_cos (f y)]
  fun_prop (disch := assumption)

@[fun_prop] private theorem re_comp_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => (f y).re) x :=
  Complex.reCLM.differentiableAt.comp x hf

@[fun_prop] private theorem im_comp_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => (f y).im) x :=
  Complex.imCLM.differentiableAt.comp x hf

@[fun_prop] private theorem heightCoordinate_differentiable {m : ℕ} (hm : 0 < m)
    (j : Fin m) :
    Differentiable ℝ (fun p : CommonCoordinates m =>
      heightParameter (coordinates hm p.2.1) p.2.2 j) := by
  unfold heightParameter CommonTangentialParameters.coordinates
    FiniteFourierLift.difference
  fun_prop

@[fun_prop] private theorem heightCoordinate_differentiableAt {m : ℕ} (hm : 0 < m)
    (j : Fin m) (p : CommonCoordinates m) :
    DifferentiableAt ℝ (fun q : CommonCoordinates m =>
      heightParameter (coordinates hm q.2.1) q.2.2 j) p :=
  heightCoordinate_differentiable hm j p

@[fun_prop] private theorem relativeAngle_differentiableAt {m : ℕ} (hm : 0 < m)
    (j : Fin m) (p : CommonCoordinates m) :
    DifferentiableAt ℝ (fun q : CommonCoordinates m => relativeAngle hm q.1 j) p := by
  unfold relativeAngle initialAngle
  fun_prop

@[fun_prop] private theorem relativeAverage_differentiableAt {m : ℕ} (hm : 0 < m)
    (j : Fin m) (p : CommonCoordinates m) :
    DifferentiableAt ℝ (fun q : CommonCoordinates m => relativeAverage hm q.1 j) p := by
  unfold relativeAverage initialAngle CommonClosureEnergy.angleAverage
  fun_prop

@[fun_prop] private theorem crossingRelative_differentiableAt {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (p : CommonCoordinates m)
    (hheight : ∀ j, heightParameter (coordinates hm p.2.1) p.2.2 j ^ 2 < 4)
    (j : Fin m) :
    DifferentiableAt ℝ (fun q : CommonCoordinates m =>
      crossingRelative hm q.1 q.2.1 σ q.2.2 j) p := by
  let t : CommonCoordinates m → ℝ := fun q =>
    heightParameter (coordinates hm q.2.1) q.2.2 j
  rw [show (fun q : CommonCoordinates m =>
      crossingRelative hm q.1 q.2.1 σ q.2.2 j) =
      fun q => unit (relativeAverage hm q.1 j) *
        Complex.equivRealProdCLM.symm (Lens.height (t q) / 2, σ j * t q / 2) by
    funext q
    rfl]
  unfold t relativeAverage initialAngle CommonClosureEnergy.angleAverage
  fun_prop (disch := aesop)

/-- The inverse rational chart is differentiable at every point where its
positive square root, tangent branch, and stereographic denominator are
nondegenerate. -/
theorem rationalRecovery_differentiableAt {m : ℕ} (hm : 0 < m)
    (σ : Fin m → ℝ) (p : CommonCoordinates m)
    (hangle : ∀ j : Fin m, Real.cos (relativeAngle hm p.1 j / 2) ≠ 0)
    (hheight : ∀ j, heightParameter (coordinates hm p.2.1) p.2.2 j ^ 2 < 4)
    (hden : ∀ j, 1 + (crossingRelative hm p.1 p.2.1 σ p.2.2 j).re ≠ 0) :
    DifferentiableAt ℝ (rationalRecovery hm σ) p := by
  unfold rationalRecovery CommonRationalChart.parameters
    RationalParameterRecovery.parameters
  apply differentiableAt_pi.mpr
  intro i
  cases i with
  | inl k =>
      change DifferentiableAt ℝ (fun q : CommonCoordinates m =>
        Real.tan (relativeAngle hm q.1 ⟨k.val + 1, by omega⟩ / 2)) p
      fun_prop (disch := aesop)
  | inr j =>
      change DifferentiableAt ℝ (fun q : CommonCoordinates m =>
        RationalChartInverse.parameter
          (crossingRelative hm q.1 q.2.1 σ q.2.2 j)) p
      unfold RationalChartInverse.parameter
      fun_prop (disch := (first | assumption | exact hheight _ | exact hden _))

/-- On the actual small rational window, normalization followed by rational
parameter recovery returns every literal rational coordinate. -/
theorem rationalRecovery_forward {m : ℕ} (hm : 2 ≤ m) (σ : Fin m → ℝ)
    (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (hs : ∀ j, σ j ^ 2 = 1) :
    rationalRecovery (by omega) σ (rationalForward (by omega) σ X) = X := by
  simpa only [rationalRecovery, rationalForward] using
    RationalSelectorRoundTrip.parameters_recovered hm σ X hX hs

/-- The square-root, tangent, and stereographic branches occurring in the
recovery map are automatically nondegenerate at every actual point in the
small rational window. -/
theorem rationalRecovery_differentiableAt_forward {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin m → ℝ) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (hs : ∀ j, σ j ^ 2 = 1) :
    DifferentiableAt ℝ (rationalRecovery (by omega) σ)
      (rationalForward (by omega) σ X) := by
  apply rationalRecovery_differentiableAt
  · intro j
    simp only [rationalForward]
    rw [RationalSelectorRoundTrip.relativeAngle_theta]
    unfold RationalAngleBranch.angle
    simp only [Nat.mod_eq_of_lt j.isLt]
    have he : 2 * Real.arctan (RationalConfiguration.angleParameter X j) / 2 =
        Real.arctan (RationalConfiguration.angleParameter X j) := by ring
    rw [he, Real.cos_arctan]
    positivity
  · intro j
    simp only [rationalForward]
    rw [RationalCommonConfiguration.recovered_height hm σ X]
    unfold RationalAngleBranch.tangential
    rw [mul_pow, hs j, one_mul]
    have hc := RationalAngleBranch.crossingOffset_cos_pos hm X hX j
    nlinarith [Real.sin_sq_add_cos_sq
      (RationalAngleBranch.crossingOffset (by omega) X j), sq_pos_of_pos hc]
  · intro j
    simp only [rationalForward]
    rw [RationalSelectorRoundTrip.crossingRelative_recovered hm σ X hX j (hs j)]
    exact (RationalChart.one_add_rotation_re_pos _).ne'

private theorem eventually_smallWindow {m : ℕ}
    (X : RationalConfiguration.Variables m → ℝ) (hX : SmallWindow X) :
    ∀ᶠ Y in 𝓝 X, SmallWindow Y := by
  unfold SmallWindow at hX ⊢
  rw [Filter.eventually_all]
  intro i
  have hi : ContinuousAt
      (fun Y : RationalConfiguration.Variables m → ℝ => |Y i|) X := by
    have happly : ContinuousAt
        (fun Y : RationalConfiguration.Variables m → ℝ => Y i) X :=
      continuousAt_apply i X
    exact happly.abs
  exact hi.tendsto.eventually (eventually_lt_nhds (hX i))

/-- The recovery-forward identity remains exact throughout a neighborhood of
an actual point.  This is the local identity needed when differentiating the
coordinate change, rather than merely a pointwise round trip. -/
theorem rationalRecovery_forward_eventuallyEq {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin m → ℝ) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (hs : ∀ j, σ j ^ 2 = 1) :
    (fun Y => rationalRecovery (by omega) σ
      (rationalForward (by omega) σ Y)) =ᶠ[𝓝 X] id := by
  filter_upwards [eventually_smallWindow X hX] with Y hY
  simpa only [id_eq] using rationalRecovery_forward hm σ Y hY hs

/-- At an actual small-window point, the derivative of recovery is a left
inverse to the derivative of normalization. -/
theorem rationalRecovery_fderiv_comp_forward {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin m → ℝ) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (hs : ∀ j, σ j ^ 2 = 1) :
    (fderiv ℝ (rationalRecovery (by omega) σ)
      (rationalForward (by omega) σ X)).comp
        (fderiv ℝ (rationalForward (by omega) σ) X) =
      ContinuousLinearMap.id ℝ (RationalConfiguration.Variables m → ℝ) := by
  have hforward : DifferentiableAt ℝ (rationalForward (by omega) σ) X :=
    (rationalForward_differentiable (by omega) σ) X
  have hrecovery := rationalRecovery_differentiableAt_forward hm σ X hX hs
  have hcomp := hrecovery.hasFDerivAt.comp X hforward.hasFDerivAt
  have hid : HasFDerivAt
      (fun Y => rationalRecovery (by omega) σ
        (rationalForward (by omega) σ Y))
      (ContinuousLinearMap.id ℝ (RationalConfiguration.Variables m → ℝ)) X :=
    (hasFDerivAt_id X).congr_of_eventuallyEq
      (rationalRecovery_forward_eventuallyEq hm σ X hX hs)
  exact hcomp.unique hid

/-- Normalization has no infinitesimal kernel on the literal rational chart. -/
theorem rationalForward_fderiv_injective {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin m → ℝ) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (hs : ∀ j, σ j ^ 2 = 1) :
    Function.Injective (fderiv ℝ (rationalForward (by omega) σ) X) := by
  have hcomp := rationalRecovery_fderiv_comp_forward hm σ X hX hs
  have hleft : Function.LeftInverse
      (fderiv ℝ (rationalRecovery (by omega) σ)
        (rationalForward (by omega) σ X))
      (fderiv ℝ (rationalForward (by omega) σ) X) := by
    intro u
    have hu := congrArg (fun f => f u) hcomp
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hu
  exact hleft.injective

/-- The recovery derivative covers every literal rational coordinate
direction at an actual point. -/
theorem rationalRecovery_fderiv_surjective {m : ℕ} (hm : 2 ≤ m)
    (σ : Fin m → ℝ) (X : RationalConfiguration.Variables m → ℝ)
    (hX : SmallWindow X) (hs : ∀ j, σ j ^ 2 = 1) :
    Function.Surjective (fderiv ℝ (rationalRecovery (by omega) σ)
      (rationalForward (by omega) σ X)) := by
  have hcomp := rationalRecovery_fderiv_comp_forward hm σ X hX hs
  have hleft : Function.LeftInverse
      (fderiv ℝ (rationalRecovery (by omega) σ)
        (rationalForward (by omega) σ X))
      (fderiv ℝ (rationalForward (by omega) σ) X) := by
    intro u
    have hu := congrArg (fun f => f u) hcomp
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using hu
  exact hleft.surjective

end
end StructuralNote.FixedSchurRationalWindowCoordinateSmooth
