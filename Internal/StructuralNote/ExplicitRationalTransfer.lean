import StructuralNote.ExplicitRationalClosure
import StructuralNote.ExplicitHessianThresholdFixedSchurGeometry
import StructuralNote.FixedSchurRationalWindowObjectiveTransfer
/-! Exact transfer of the rational objective at an explicit order. -/
namespace StructuralNote.ExplicitRationalTransfer
open Erdos1045 Erdos1045.EventualExact Complex Filter
open FourierMultiplier FiniteFourierLift SchurSpectrum
open RationalCommonConfiguration RationalAngleBranch
open RationalStationarySystem FixedSchurRationalClosureMatrix
open LensClosure
open CommonDomainClosure CommonDomainRadius
open FixedSchurLinear FixedSchurChart FixedSchurChartGeometry
open FixedSchurObjective FixedSchurObjectivePaths
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open FixedSchurRationalWindowRepresentation
open FixedSchurRationalWindowAngleChart
open FixedSchurRationalWindowCrossingChart
open scoped BigOperators Topology
open FixedSchurRationalWindowObjectiveTransfer
noncomputable section
theorem selectedWindow_smallWindow {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        SmallWindow X := by
  have hangle := ExplicitRationalWindow.selectedWindow_angleParameter_small ((le_max_left _ _).trans hN)
  have hcross := ExplicitRationalClosure.selectedWindow_crossingParameter_small hN
  clear hN
  intro hm s X hwindow hclosure i
  cases i with
  | inl k =>
      have h := hangle (show 2 ≤ m by omega) s X hwindow
        ⟨k.val + 1, by omega⟩
      simpa only [RationalConfiguration.angleParameter,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, dite_false,
        Nat.add_sub_cancel] using h
  | inr j =>
      simpa only [RationalConfiguration.crossingParameter] using
        hcross hm s X hwindow hclosure j

/-- The rational single-window point lands in the actual fixed-Schur domain. -/

theorem fixedSchurCoordinates_inDomain {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        fixedSchurCoordinates (show 2 ≤ m by omega) s X ∈
          FixedSchurChartSmooth.domain (by omega) := by
  have hdomain := ExplicitRationalWindow.selectedWindow_inDomain ((le_max_left _ _).trans hN)
  clear hN
  intro hm s X hwindow
  exact hdomain (show 2 ≤ m by omega) s X hwindow

/-- On a closed selected-window point, the chosen fixed-Schur configuration
is exactly the normalized rigid image of the literal rational configuration. -/

theorem fixed_configuration_eq_rigid {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        FixedSchurChart.configuration (by omega) s
            (fixedSchurCoordinates (show 2 ≤ m by omega) s X).1
            (fixedSchurCoordinates (show 2 ≤ m by omega) s X).2 =
          fun j => unit (-angleMean (by omega) X) *
            (RationalConfiguration.configuration (by omega) (rationalSign s) X j -
              centerMean (by omega) (rationalSign s) X) := by
  have hrepresentation := ExplicitRationalRepresentation.selectedWindow_representation hN
  clear hN
  intro hm s X hwindow hclosure
  have hrep := hrepresentation (show 2 ≤ m by omega) s X hwindow hclosure
  dsimp only at hrep
  exact hrep.2.2.1.symm.trans hrep.2.2.2.1

/-- Every point in the closed single window is collision-free, as a
consequence of its exact fixed-Schur representation. -/

theorem selectedWindow_collisionFree {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        CollisionFree (by omega) (halfWord s) X := by
  have hrigid := fixed_configuration_eq_rigid hN
  have hdomain := fixedSchurCoordinates_inDomain hN
  have hgeometry := ExplicitHessianThresholdFixedSchurGeometry.geometric_properties ((le_max_left _ _).trans hN)
  clear hN
  intro hm s X hwindow hclosure
  have hdom := hdomain hm s X hwindow
  have hinj := (hgeometry (show 2 ≤ m by omega) s
    (fixedSchurCoordinates (show 2 ≤ m by omega) s X).1
    (fixedSchurCoordinates (show 2 ≤ m by omega) s X).2 hdom).injective
  have he := hrigid hm s X hwindow hclosure
  change Function.Injective
    (RationalConfiguration.configuration (by omega)
      (RationalConfigurationPolynomials.sign (halfWord s)) X)
  rw [sign_halfWord]
  intro i j hij
  apply hinj
  rw [congrFun he i, congrFun he j, hij]

/-- Rigid normalization preserves the discriminant at every selected-window
point represented in the chosen fixed-Schur chart. -/

theorem fixed_discriminant_eq_rational {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        Configuration.discriminant
            (FixedSchurChart.configuration (by omega) s
              (fixedSchurCoordinates (show 2 ≤ m by omega) s X).1
              (fixedSchurCoordinates (show 2 ≤ m by omega) s X).2) =
          Configuration.discriminant
            (RationalConfiguration.configuration (by omega) (rationalSign s) X) := by
  have hrigid := fixed_configuration_eq_rigid hN
  clear hN
  intro hm s X hwindow hclosure
  let z := RationalConfiguration.configuration (by omega) (rationalSign s) X
  let u := unit (-angleMean (by omega) X)
  let c := centerMean (by omega) (rationalSign s) X
  have he := hrigid hm s X hwindow hclosure
  have haffine : (fun j => u * (z j - c)) = fun j => -u * c + u * z j := by
    funext j
    ring
  rw [show FixedSchurChart.configuration (by omega) s
      (fixedSchurCoordinates (show 2 ≤ m by omega) s X).1
      (fixedSchurCoordinates (show 2 ≤ m by omega) s X).2 =
        fun j => u * (z j - c) by simpa only [u, z, c] using he,
    haffine]
  simpa only [u, z, norm_unit, one_pow, one_mul] using
    Configuration.discriminant_affine z (-u * c) u

/-- The rational logarithmic objective and the chosen fixed-Schur objective
are literally equal on the closed single window. -/

theorem rational_objective_eq_fixed {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (X : RationalConfiguration.Variables m → ℝ),
        selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 →
        RationalStationarySystem.objective (by omega) (halfWord s) X =
          FixedSchurObjectivePaths.objective (by omega) s
            (fixedSchurCoordinates (show 2 ≤ m by omega) s X) := by
  have hcollision := selectedWindow_collisionFree hN
  have hdisc := fixed_discriminant_eq_rational hN
  clear hN
  intro hm s X hwindow hclosure
  have hfree := hcollision hm s X hwindow hclosure
  rw [RationalStationarySystem.objective_eq_log_discriminant
    (by omega) (halfWord s) X hfree]
  unfold FixedSchurObjectivePaths.objective FixedSchurObjective.F
  rw [sign_halfWord]
  exact congrArg Real.log (hdisc hm s X hwindow hclosure).symm

@[fun_prop] private theorem angle_differentiable {m : ℕ} (hm : 0 < m)
    (j : ℕ) : Differentiable ℝ
      (fun X : RationalConfiguration.Variables m → ℝ => angle hm X j) := by
  unfold angle RationalConfiguration.angleParameter
  split
  · fun_prop
  · intro X
    exact ((Real.differentiableAt_arctan _).comp X (by fun_prop)).const_mul 2

@[fun_prop] private theorem angleMean_differentiable {m : ℕ} (hm : 0 < m) :
    Differentiable ℝ (angleMean hm) := by
  unfold angleMean
  fun_prop (disch := assumption)

@[fun_prop] private theorem rationalDiameter_differentiable {m : ℕ}
    (hm : 0 < m) (j : ℕ) : Differentiable ℝ
      (fun X : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.diameter hm X j) := by
  unfold RationalConfiguration.diameter
  exact (differentiable_const _).mul
    (FixedSchurRationalWindowClosureDerivative.rotation_differentiable.comp (by
      unfold RationalConfiguration.angleParameter
      split <;> fun_prop))

@[fun_prop] private theorem rationalCrossingUnit_differentiable {m : ℕ}
    (j : Fin m) : Differentiable ℝ
      (fun X : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.crossingUnit X j) := by
  unfold RationalConfiguration.crossingUnit RationalConfiguration.crossingParameter
  exact (differentiable_const _).mul
    (FixedSchurRationalWindowClosureDerivative.rotation_differentiable.comp (by fun_prop))

@[fun_prop] private theorem rationalIncrement_differentiable {m : ℕ}
    (hm : 0 < m) (σ : Fin m → ℝ) (j : Fin m) : Differentiable ℝ
      (fun X : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.increment hm σ X j) := by
  unfold RationalConfiguration.increment RationalChart.crossingIncrement
  have hU := rationalCrossingUnit_differentiable j
  have hd₀ := rationalDiameter_differentiable hm j
  have hd₁ := rationalDiameter_differentiable hm (j.val + 1)
  exact (differentiable_const _).mul
    ((((differentiable_const _).mul hU).sub hd₀).sub hd₁)

@[fun_prop] private theorem centerPrefix_differentiable {m : ℕ}
    (hm : 0 < m) (σ : Fin m → ℝ) (r : ℕ) : Differentiable ℝ
      (fun X : RationalConfiguration.Variables m → ℝ =>
        RationalConfiguration.centerPrefix hm σ X r) := by
  unfold RationalConfiguration.centerPrefix
  have hterm (j : ℕ) : Differentiable ℝ
      (fun X : RationalConfiguration.Variables m → ℝ =>
        if hj : j < m then RationalConfiguration.increment hm σ X ⟨j, hj⟩ else 0) := by
    split
    · exact rationalIncrement_differentiable hm σ _
    · fun_prop
  have hsum (S : Finset ℕ) : Differentiable ℝ
      (fun X : RationalConfiguration.Variables m → ℝ =>
        ∑ j ∈ S, if hj : j < m then
          RationalConfiguration.increment hm σ X ⟨j, hj⟩ else 0) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; fun_prop
    | @insert a S ha ih =>
        simp only [Finset.sum_insert ha]
        exact (hterm a).add ih
  exact hsum (Finset.range r)

@[fun_prop] private theorem centerMean_differentiable {m : ℕ}
    (hm : 0 < m) (σ : Fin m → ℝ) : Differentiable ℝ
      (centerMean hm σ) := by
  unfold centerMean
  fun_prop (disch := exact centerPrefix_differentiable hm σ _)

@[fun_prop] private theorem normalizedCenter_differentiable {m : ℕ}
    (hm : 0 < m) (σ : Fin m → ℝ) : Differentiable ℝ
      (normalizedCenter hm σ) := by
  unfold normalizedCenter LensClosure.unit
  apply differentiable_pi.mpr
  intro j
  fun_prop (disch := first | exact angleMean_differentiable hm |
    exact centerPrefix_differentiable hm σ _ | exact centerMean_differentiable hm σ)

@[fun_prop] private theorem constraint_differentiable {m : ℕ} (hm : 2 ≤ m) :
    Differentiable ℝ (SchurLift.constraint (show 0 < 2 * m by omega) :
      (Fin (2 * m) → ℂ) → (Fin (2 * m) → ℝ)) := by
  unfold SchurLift.constraint FiniteFourierLift.difference
  fun_prop

@[fun_prop] private theorem canonicalLift_differentiable {n : ℕ} :
    Differentiable ℝ (SchurLift.canonicalLift :
      (Fin n → ℝ) → (Fin n → ℂ)) := by
  have hcoefficient (p : Fin n) : Differentiable ℝ
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
  apply differentiable_pi.mpr
  intro j
  have hsum (S : Finset (Fin n)) : Differentiable ℝ
      (fun q : Fin n → ℝ => ∑ p ∈ S,
        FiniteFourierLift.integralCoefficients (SchurLift.increment q) p *
          FourierMultiplier.character n p j) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; fun_prop
    | @insert a S ha ih =>
        simp only [Finset.sum_insert ha]
        exact ((hcoefficient a).mul_const _).add ih
  simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
    hsum (Finset.univ : Finset (Fin n))

@[fun_prop] private theorem projection_differentiable {m : ℕ} (hm : 2 ≤ m) :
    Differentiable ℝ (projection hm :
      (Fin (2 * m) → ℂ) → (Fin (2 * m) → ℂ)) := by
  unfold projection
  exact differentiable_id.sub
    (canonicalLift_differentiable.comp (constraint_differentiable hm))

/-- The actual rational-to-fixed coordinate map is globally differentiable;
the closure equation and the selected-window inequalities enter only when
identifying its image with the chosen geometric configuration. -/

theorem objective_path_eventuallyEq {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : ℝ → RationalConfiguration.Variables m → ℝ) (x : ℝ),
        ContinuousAt Z x →
        selectedWindowEnergy (by omega) s (Z x) <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        (∀ᶠ t in 𝓝 x,
          RationalConfiguration.closure (by omega) (rationalSign s) (Z t) = 0) →
        (fun t => RationalStationarySystem.objective (by omega) (halfWord s) (Z t)) =ᶠ[𝓝 x]
          (fun t => FixedSchurObjectivePaths.objective (by omega) s
            (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t))) := by
  have hobjective := rational_objective_eq_fixed hN
  clear hN
  intro hm s Z x hZ hwindow hclosure
  have henergy : ContinuousAt
      (fun t => selectedWindowEnergy (by omega) s (Z t)) x :=
    (selectedWindowEnergy_differentiable (by omega) s).continuous.continuousAt.comp hZ
  have hwindowNear : ∀ᶠ t in 𝓝 x,
      selectedWindowEnergy (by omega) s (Z t) <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) :=
    henergy.tendsto.eventually (eventually_lt_nhds hwindow)
  filter_upwards [hwindowNear, hclosure] with t ht hc
  exact hobjective hm s (Z t) ht hc

/-- First derivatives agree along every locally closed rational path through
the strict single window. -/

theorem objective_path_deriv_eq {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : ℝ → RationalConfiguration.Variables m → ℝ) (x : ℝ),
        ContinuousAt Z x →
        selectedWindowEnergy (by omega) s (Z x) <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        (∀ᶠ t in 𝓝 x,
          RationalConfiguration.closure (by omega) (rationalSign s) (Z t) = 0) →
        deriv (fun t => RationalStationarySystem.objective (by omega)
            (halfWord s) (Z t)) x =
          deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s
            (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t))) x := by
  have heq := objective_path_eventuallyEq hN
  clear hN
  intro hm s Z x hZ hwindow hclosure
  exact (heq hm s Z x hZ hwindow hclosure).deriv_eq

/-- The genuine second derivatives also agree.  At a stationary point this is
the constrained-Hessian congruence used by the nonsingularity argument. -/

theorem objective_path_second_deriv_eq {m : ℕ} (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
        (Z : ℝ → RationalConfiguration.Variables m → ℝ) (x : ℝ),
        ContinuousAt Z x →
        selectedWindowEnergy (by omega) s (Z x) <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
        (∀ᶠ t in 𝓝 x,
          RationalConfiguration.closure (by omega) (rationalSign s) (Z t) = 0) →
        deriv (deriv (fun t => RationalStationarySystem.objective (by omega)
            (halfWord s) (Z t))) x =
          deriv (deriv (fun t => FixedSchurObjectivePaths.objective (by omega) s
            (fixedSchurCoordinates (show 2 ≤ m by omega) s (Z t)))) x := by
  have heq := objective_path_eventuallyEq hN
  clear hN
  intro hm s Z x hZ hwindow hclosure
  exact (heq hm s Z x hZ hwindow hclosure).deriv.deriv_eq

end
end StructuralNote.ExplicitRationalTransfer
