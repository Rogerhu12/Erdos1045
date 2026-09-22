import StructuralNote.ExplicitActualRationalStationary
import StructuralNote.ExplicitRationalStationaryTransfer
import StructuralNote.FixedSchurRationalStationarySelection
/-! Uniqueness and algebraicity of the stationary branch at explicit orders. -/
namespace StructuralNote.ExplicitRationalStationarySelection

open Filter Matrix Complex Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open RationalCommonConfiguration RationalExpressions RationalStationarySystem
open RationalSystemAlgebraicity
open FixedSchurRationalClosureMatrix FixedSchurRationalWindowEnergy
open FixedSchurRationalWindowDomain
open FixedSchurRationalWindowObjectiveTransfer FixedSchurRationalWindowRepresentation
open FixedSchurRationalStationaryTransfer FixedSchurStationaryUniqueness
open FixedSchurActualCanonicalEntry FixedSchurActualRationalStationary
open FixedSchurLinear FixedSchurChart CommonDomainRadius
open scoped BigOperators Topology

noncomputable section


theorem selectedWindow_stationary_unique {m : ℕ} {hm3 : 3 ≤ m} (D : ExplicitHessianThresholdDownstream.FixedSchurFiberData hm3) 
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (Y Z : RationalStationarySystem.Variables m → ℝ),
      selectedWindowEnergy (by omega) s (coordinates Y) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      Stationary (by omega) (halfWord s) Y →
      selectedWindowEnergy (by omega) s (coordinates Z) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      Stationary (by omega) (halfWord s) Z → Y = Z := by
  have hfixed := ExplicitRationalStationaryTransfer.rational_stationary_fixed hN
  have hdomain := ExplicitRationalTransfer.fixedSchurCoordinates_inDomain hN
  have hrepresentation := ExplicitRationalRepresentation.selectedWindow_representation hN
  have hsurjective := ExplicitRationalClosure.selectedWindow_closureMatrix_surjective hN
  clear hN
  intro hm s Y Z hYwindow hYstationary hZwindow hZstationary
  let X := coordinates Y
  let X' := coordinates Z
  have hYclosure : RationalConfiguration.closure (by omega) (rationalSign s) X = 0 := by
    rw [← sign_halfWord]
    exact hYstationary.1
  have hZclosure : RationalConfiguration.closure (by omega) (rationalSign s) X' = 0 := by
    rw [← sign_halfWord]
    exact hZstationary.1
  have hYfixed := hfixed hm s Y hYwindow hYstationary
  have hZfixed := hfixed hm s Z hZwindow hZstationary
  have hfixedEq : fixedSchurCoordinates (show 2 ≤ m by omega) s X =
      fixedSchurCoordinates (show 2 ≤ m by omega) s X' := by
    apply ExplicitHessianThresholdDownstream.stationary_unique D s
    · exact hdomain hm s X hYwindow
    · exact hdomain hm s X' hZwindow
    · exact hYfixed
    · exact hZfixed
  have htheta : theta (by omega) X = theta (by omega) X' :=
    congrArg Prod.fst hfixedEq
  have hprojection : projection (show 2 ≤ m by omega)
      (normalizedCenter (by omega) (rationalSign s) X) =
      projection (show 2 ≤ m by omega)
        (normalizedCenter (by omega) (rationalSign s) X') :=
    congrArg Prod.snd hfixedEq
  have hYrep := hrepresentation (show 2 ≤ m by omega) s X hYwindow hYclosure
  have hZrep := hrepresentation (show 2 ≤ m by omega) s X' hZwindow hZclosure
  dsimp only at hYrep hZrep
  have hcenter : normalizedCenter (by omega) (rationalSign s) X =
      normalizedCenter (by omega) (rationalSign s) X' := by
    calc
      normalizedCenter (by omega) (rationalSign s) X =
          center (coordinate (by omega) s (theta (by omega) X)
            (projection (show 2 ≤ m by omega)
              (normalizedCenter (by omega) (rationalSign s) X)))
            (projection (show 2 ≤ m by omega)
              (normalizedCenter (by omega) (rationalSign s) X)) := hYrep.2.1
      _ = center (coordinate (by omega) s (theta (by omega) X')
            (projection (show 2 ≤ m by omega)
              (normalizedCenter (by omega) (rationalSign s) X')))
            (projection (show 2 ≤ m by omega)
              (normalizedCenter (by omega) (rationalSign s) X')) := by
        rw [htheta, hprojection]
      _ = normalizedCenter (by omega) (rationalSign s) X' := hZrep.2.1.symm
  have hXeq : X = X' := by
    calc
      X = FixedSchurRationalRecovery.parameters (show 2 ≤ m by omega) s
          (theta (by omega) X)
          (normalizedCenter (by omega) (rationalSign s) X) :=
        (physical_recovery_parameters_eq (show 2 ≤ m by omega) s X hYclosure).symm
      _ = FixedSchurRationalRecovery.parameters (show 2 ≤ m by omega) s
          (theta (by omega) X')
          (normalizedCenter (by omega) (rationalSign s) X') := by
        rw [htheta, hcenter]
      _ = X' := physical_recovery_parameters_eq (show 2 ≤ m by omega) s X' hZclosure
  have hrow (i : RationalConfiguration.Variables m) :
      ∑ k, multiplier Y k * closureMatrix (by omega) (halfWord s) X k i =
        ∑ k, multiplier Z k * closureMatrix (by omega) (halfWord s) X k i := by
    have hYi := hYstationary.2 i
    have hZi := hZstationary.2 i
    change deriv (fun t => objective (by omega) (halfWord s)
        (Function.update X i t)) (X i) =
      ∑ k, multiplier Y k * closureMatrix (by omega) (halfWord s) X k i at hYi
    change deriv (fun t => objective (by omega) (halfWord s)
        (Function.update X' i t)) (X' i) =
      ∑ k, multiplier Z k * closureMatrix (by omega) (halfWord s) X' k i at hZi
    rw [← hXeq] at hZi
    exact hYi.symm.trans hZi
  have hmul : multiplier Y = multiplier Z := by
    funext k
    obtain ⟨v, hv⟩ := hsurjective hm s X hYwindow hYclosure (Pi.single k 1)
    have hs :
        ∑ i, (∑ l, multiplier Y l * closureMatrix (by omega) (halfWord s) X l i) * v i =
          ∑ i, (∑ l, multiplier Z l * closureMatrix (by omega) (halfWord s) X l i) * v i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun r => r * v i) (hrow i)
    have hdot :
        ∑ l, multiplier Y l *
            ((closureMatrix (by omega) (halfWord s) X) *ᵥ v) l =
          ∑ l, multiplier Z l *
            ((closureMatrix (by omega) (halfWord s) X) *ᵥ v) l := by
      calc
        ∑ l, multiplier Y l *
            ((closureMatrix (by omega) (halfWord s) X) *ᵥ v) l =
            ∑ l, ∑ i, multiplier Y l *
              (closureMatrix (by omega) (halfWord s) X l i * v i) := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        _ = ∑ i, ∑ l, multiplier Y l *
              (closureMatrix (by omega) (halfWord s) X l i * v i) := by
          rw [Finset.sum_comm]
        _ = ∑ i, (∑ l, multiplier Y l *
              closureMatrix (by omega) (halfWord s) X l i) * v i := by
          simp only [Finset.sum_mul, mul_assoc]
        _ = ∑ i, (∑ l, multiplier Z l *
              closureMatrix (by omega) (halfWord s) X l i) * v i := hs
        _ = ∑ i, ∑ l, multiplier Z l *
              (closureMatrix (by omega) (halfWord s) X l i * v i) := by
          simp only [Finset.sum_mul, mul_assoc]
        _ = ∑ l, ∑ i, multiplier Z l *
              (closureMatrix (by omega) (halfWord s) X l i * v i) := by
          rw [Finset.sum_comm]
        _ = ∑ l, multiplier Z l *
            ((closureMatrix (by omega) (halfWord s) X) *ᵥ v) l := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [hv] at hdot
    simpa only [Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using hdot
  funext q
  cases q with
  | inl i => exact congrFun hXeq i
  | inr k => exact congrFun hmul k

/-- Every stationary root in the selected window has algebraic full system
coordinates, algebraic rational configuration coordinates, all algebraic
pairwise distances, and algebraic discriminant. -/


theorem selectedWindow_stationary_algebraic {m : ℕ} 
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega))
      (Y : RationalStationarySystem.Variables m → ℝ),
      selectedWindowEnergy (by omega) s (coordinates Y) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      Stationary (by omega) (halfWord s) Y →
      (RationalSystemAlgebraicity.jacobian
        (systemExpression (by omega) (halfWord s)) Y).det ≠ 0 ∧
      (∀ q, MvPolynomial.aeval Y (polynomials (by omega) (halfWord s) q) = 0) ∧
      (PolynomialAlgebraicity.jacobian (polynomials (by omega) (halfWord s)) Y).det ≠ 0 ∧
      (∀ q, IsAlgebraic ℚ (Y q)) ∧
      (∀ j, IsAlgebraic ℚ
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y) j).re ∧
        IsAlgebraic ℚ
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y) j).im) ∧
      (∀ i j, IsAlgebraic ℚ
        ‖RationalConfiguration.configuration (by omega) (rationalSign s)
              (coordinates Y) i -
          RationalConfiguration.configuration (by omega) (rationalSign s)
              (coordinates Y) j‖) ∧
      IsAlgebraic ℚ (Configuration.discriminant
        (RationalConfiguration.configuration (by omega) (rationalSign s)
          (coordinates Y))) := by
  have hcollision := ExplicitRationalTransfer.selectedWindow_collisionFree hN
  have hnonsingular := ExplicitRationalStationaryTransfer.selectedWindow_stationary_jacobian_nonsingular hN
  clear hN
  intro hm s Y hwindow hstationary
  have hclosure : RationalConfiguration.closure (by omega) (rationalSign s)
      (coordinates Y) = 0 := by
    rw [← sign_halfWord]
    exact hstationary.1
  have hfree := hcollision hm s (coordinates Y) hwindow hclosure
  have hJ := hnonsingular hm s Y hwindow hstationary
  have hYalg := stationary_coordinates_algebraic (by omega) (halfWord s) Y
    hfree hstationary hJ
  have hpoly := (polynomial_system_iff (by omega) (halfWord s) Y hfree).2 hstationary
  have hvalid (q : RationalStationarySystem.Variables m) :
      (systemExpression (by omega) (halfWord s) q).Valid Y := by
    cases q with
    | inl i => exact residual_valid (by omega) (halfWord s) Y hfree i
    | inr k =>
        change ((closureCoordinate (by omega) (halfWord s) k).rename Sum.inl).Valid Y
        exact Expression.valid_rename _ _
          (closureCoordinate_valid (by omega) (halfWord s) k _)
  have hzero (q : RationalStationarySystem.Variables m) :
      (systemExpression (by omega) (halfWord s) q).eval Y = 0 :=
    (Expression.eval_eq_zero_iff (hvalid q)).2 (hpoly q)
  have hcleared := cleared_jacobian_nonsingular
    (systemExpression (by omega) (halfWord s)) Y hvalid hzero hJ
  have hXalg : ∀ i, IsAlgebraic ℚ (coordinates Y i) := by
    intro i
    exact hYalg (.inl i)
  refine ⟨hJ, hpoly, hcleared, hYalg, ?_, ?_, ?_⟩
  · intro j
    rw [← sign_halfWord]
    exact configuration_coordinates_algebraic (by omega) (halfWord s)
      (coordinates Y) hXalg j
  · intro i j
    rw [← sign_halfWord]
    exact distance_algebraic (by omega) (halfWord s) (coordinates Y) hXalg i j
  · rw [← sign_halfWord]
    exact discriminant_algebraic (by omega) (halfWord s) (coordinates Y) hXalg

/-- The rational recovery of every sufficiently large actual extremizer is
the unique complete stationary root in its selected window.  Its full system
coordinates and geometric data are algebraic, and its rational discriminant
is the discriminant of the original extremizer. -/


theorem actual_extremizer_unique_algebraic_root {m : ℕ} (hm : 8 ≤ m)
    (D : ExplicitHessianThresholdDownstream.FixedSchurFiberData (show 3 ≤ m by omega))
    {δ : ℝ} (hδ : 0 < δ)
    (hfinite : ExplicitBalancedSelection.FiniteImprovement m SinglePressureEstimate.budgetConstant δ)
    (hN : ExplicitActualRationalStationary.orderThreshold δ ≤ 2 * m)
    (z : Points (2 * m)) (hz : ExtremalNormalization.DiameterExtremal z) :
      ∃ (hm : 3 ≤ m) (x : FixedSchurEquationSmooth.SchurParameters m)
        (Y : RationalStationarySystem.Variables m → ℝ),
        CanonicalRepresentative hm z x ∧
        let s := FixedSchurCanonicalWordSymmetry.canonicalPattern hm
        let C := center (coordinate (by omega) s x.1 x.2) x.2
        let X := FixedSchurRationalRecovery.parameters (by omega) s x.1 C
        theta (by omega) X = x.1 ∧
        normalizedCenter (by omega) (rationalSign s) X = C ∧
        RationalConfiguration.closure (by omega) (rationalSign s) X = 0 ∧
        selectedWindowEnergy (by omega) s X <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ∧
        coordinates Y = X ∧ Stationary (by omega) (halfWord s) Y ∧
        (RationalSystemAlgebraicity.jacobian
          (systemExpression (by omega) (halfWord s)) Y).det ≠ 0 ∧
        (∀ q, MvPolynomial.aeval Y (polynomials (by omega) (halfWord s) q) = 0) ∧
        (PolynomialAlgebraicity.jacobian
          (polynomials (by omega) (halfWord s)) Y).det ≠ 0 ∧
        (∀ Z : RationalStationarySystem.Variables m → ℝ,
          selectedWindowEnergy (by omega) s (coordinates Z) <
              (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
          Stationary (by omega) (halfWord s) Z → Z = Y) ∧
        (∀ q, IsAlgebraic ℚ (Y q)) ∧
        (∀ j, IsAlgebraic ℚ
            (RationalConfiguration.configuration (by omega) (rationalSign s) X j).re ∧
          IsAlgebraic ℚ
            (RationalConfiguration.configuration (by omega) (rationalSign s) X j).im) ∧
        (∀ i j, IsAlgebraic ℚ
          ‖RationalConfiguration.configuration (by omega) (rationalSign s) X i -
            RationalConfiguration.configuration (by omega) (rationalSign s) X j‖) ∧
        IsAlgebraic ℚ (Configuration.discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s) X)) ∧
        Configuration.discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s) X) =
            Configuration.discriminant z := by
  have hreprN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hunique := selectedWindow_stationary_unique D hreprN
  have halgebraic := selectedWindow_stationary_algebraic hreprN
  have hdisc := ExplicitRationalTransfer.fixed_discriminant_eq_rational hreprN
  have hproperties := ExplicitHessianThresholdFixedSchur.coordinate_properties
    ((le_max_left _ _).trans hreprN)
  obtain ⟨x, Y, hx, htheta, hcenter, hclosure, hwindow,
      hYX, hYstationary⟩ := ExplicitActualRationalStationary.actual_extremizer_rational_stationary hm D hδ hfinite hN hz
  let hm3 : 3 ≤ m := by omega
  let s := FixedSchurCanonicalWordSymmetry.canonicalPattern hm3
  let C := center (coordinate (by omega) s x.1 x.2) x.2
  let X := FixedSchurRationalRecovery.parameters (by omega) s x.1 C
  have hcoords : fixedSchurCoordinates (show 2 ≤ m by omega) s X = x := by
    apply Prod.ext
    · exact htheta
    · dsimp only [fixedSchurCoordinates]
      rw [hcenter]
      exact (hproperties (show 2 ≤ m by omega) s x.1 x.2 hx.1).free_projection
  have huniqueY : ∀ Z : RationalStationarySystem.Variables m → ℝ,
      selectedWindowEnergy (by omega) s (coordinates Z) <
          (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) →
      Stationary (by omega) (halfWord s) Z → Z = Y := by
    intro Z hZwindow hZstationary
    exact hunique (show 8 ≤ m by omega) s Z Y hZwindow hZstationary
      (by simpa only [hYX] using hwindow) hYstationary
  have hYwindow : selectedWindowEnergy (by omega) s (coordinates Y) <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [hYX] using hwindow
  obtain ⟨hJ, hpoly, hcleared, hYalg, hconfigAlg, hdistanceAlg, hdiscAlg⟩ :=
    halgebraic (show 8 ≤ m by omega) s Y hYwindow hYstationary
  have hdiscEq : Configuration.discriminant
      (RationalConfiguration.configuration (by omega) (rationalSign s) X) =
        Configuration.discriminant z := by
    have hfixedRational := hdisc (show 8 ≤ m by omega) s X hwindow hclosure
    rw [hcoords] at hfixedRational
    exact hfixedRational.symm.trans hx.2.2
  refine ⟨hm3, x, Y, hx, htheta, hcenter, hclosure, hwindow, hYX,
    hYstationary, hJ, hpoly, hcleared, huniqueY, hYalg, ?_, ?_, ?_, hdiscEq⟩
  · simpa only [hYX] using hconfigAlg
  · simpa only [hYX] using hdistanceAlg
  · simpa only [hYX] using hdiscAlg


end
end StructuralNote.ExplicitRationalStationarySelection
