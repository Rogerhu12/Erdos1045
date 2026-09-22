import StructuralNote.ExplicitRationalStationarySelection
import StructuralNote.ExplicitRationalPolynomial
import StructuralNote.RewrittenEvenPolynomialSelection
/-! One polynomial inequality selects the exact algebraic maximizer at an explicit order. -/
namespace StructuralNote.ExplicitPolynomialSelection

open Filter Matrix Complex MvPolynomial
open Erdos1045 Erdos1045.Configuration Erdos1045.EventualExact
open RationalExpressions RationalConfigurationPolynomials
open RationalStationarySystem RationalSystemAlgebraicity
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open FixedSchurRationalWindowObjectiveTransfer FixedSchurRationalClosureMatrix
open FixedSchurRationalWindowPolynomial
open FixedSchurRationalStationarySelection
open FixedSchurCanonicalWordSymmetry CommonDomainRadius
open scoped BigOperators Topology

noncomputable section


theorem window_polynomial_system_iff {m : ℕ}
    (hN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m) :
    ∀ (hm : 8 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m))
      (P : MvPolynomial (RationalConfiguration.Variables m) Coeff),
      (∀ X : RationalConfiguration.Variables m → ℝ,
        (selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ↔
          0 < aeval X P)) →
      ∀ Y : RationalStationarySystem.Variables m → ℝ,
        0 < aeval (coordinates Y) P →
        ((∀ q, aeval Y (polynomials (by omega) (halfWord s) q) = 0) ↔
          Stationary (by omega) (halfWord s) Y) := by
  have hcollision := ExplicitRationalTransfer.selectedWindow_collisionFree hN
  clear hN
  intro hm s P hP Y hYwindowPolynomial
  have hwindow : selectedWindowEnergy (by omega) s (coordinates Y) <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) :=
    (hP (coordinates Y)).2 hYwindowPolynomial
  constructor
  · intro hzero
    have hcoordinateZero (k : Fin 2) :
        (closureCoordinate (by omega) (halfWord s) k).eval (coordinates Y) = 0 := by
      apply (Expression.eval_eq_zero_iff
        (closureCoordinate_valid (by omega) (halfWord s) k (coordinates Y))).2
      have hk := hzero (.inr k)
      change aeval Y (MvPolynomial.rename Sum.inl
        (closureCoordinate (by omega) (halfWord s) k).numerator) = 0 at hk
      rw [MvPolynomial.aeval_rename] at hk
      simpa only [coordinates] using hk
    have hclosureBool : RationalConfiguration.closure (by omega)
        (sign (halfWord s)) (coordinates Y) = 0 :=
      (closure_equations_iff (by omega) (halfWord s) (coordinates Y)).1 hcoordinateZero
    have hclosure : RationalConfiguration.closure (by omega)
        (rationalSign s) (coordinates Y) = 0 := by
      rw [← sign_halfWord]
      exact hclosureBool
    have hfree : CollisionFree (by omega) (halfWord s) (coordinates Y) :=
      hcollision hm s (coordinates Y) hwindow hclosure
    exact (polynomial_system_iff (by omega) (halfWord s) Y hfree).1 hzero
  · intro hstationary
    have hclosure : RationalConfiguration.closure (by omega)
        (rationalSign s) (coordinates Y) = 0 := by
      rw [← sign_halfWord]
      exact hstationary.1
    have hfree : CollisionFree (by omega) (halfWord s) (coordinates Y) :=
      hcollision hm s (coordinates Y) hwindow hclosure
    exact (polynomial_system_iff (by omega) (halfWord s) Y hfree).2 hstationary

/-- For every sufficiently large even order, one polynomial inequality selects
the unique complete real root of the cleared stationary system.  The same root
is the genuine rational stationary point, both its rational and cleared
Jacobians are nonsingular, all coordinates and geometric distances are
algebraic, and its discriminant is the actual maximum `M (2m)`. -/


theorem even_maximum_single_polynomial_root {m : ℕ} (hm : 8 ≤ m)
    (D : ExplicitHessianThresholdDownstream.FixedSchurFiberData (show 3 ≤ m by omega))
    {δ : ℝ} (hδ : 0 < δ)
    (hfinite : ExplicitBalancedSelection.FiniteImprovement m SinglePressureEstimate.budgetConstant δ)
    (hN : ExplicitActualRationalStationary.orderThreshold δ ≤ 2 * m) :
      ∃ (hm : 3 ≤ m) (Y : RationalStationarySystem.Variables m → ℝ)
        (P : MvPolynomial (RationalConfiguration.Variables m) Coeff),
        let s := canonicalPattern hm
        Fintype.card (RationalStationarySystem.Variables m) = 2 * m + 1 ∧
        0 < aeval (coordinates Y) P ∧
        Stationary (by omega) (halfWord s) Y ∧
        (∀ Z : RationalStationarySystem.Variables m → ℝ,
          0 < aeval (coordinates Z) P →
          ((∀ q, aeval Z (polynomials (by omega) (halfWord s) q) = 0) ↔
            Stationary (by omega) (halfWord s) Z)) ∧
        (∀ Z : RationalStationarySystem.Variables m → ℝ,
          0 < aeval (coordinates Z) P →
          (∀ q, aeval Z (polynomials (by omega) (halfWord s) q) = 0) → Z = Y) ∧
        (RationalSystemAlgebraicity.jacobian
          (systemExpression (by omega) (halfWord s)) Y).det ≠ 0 ∧
        (∀ q, aeval Y (polynomials (by omega) (halfWord s) q) = 0) ∧
        (PolynomialAlgebraicity.jacobian
          (polynomials (by omega) (halfWord s)) Y).det ≠ 0 ∧
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
        IsAlgebraic ℚ (discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y))) ∧
        M (2 * m) = discriminant
          (RationalConfiguration.configuration (by omega) (rationalSign s)
            (coordinates Y)) ∧
        IsAlgebraic ℚ (M (2 * m)) := by
  have hreprN : ExplicitRationalRepresentation.orderThreshold ≤ 2 * m :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hwindowPolynomial := ExplicitRationalPolynomial.exists_selectedWindowPolynomial
    ((le_max_left _ _).trans hreprN)
  have hsystemIff := window_polynomial_system_iff hreprN
  obtain ⟨z, hz⟩ := WholeBoxLowerBound.exists_diameterExtremal
    (show 0 < 2 * m by omega)
  obtain ⟨hm3, x, Y, _, _, _, _, hwindow, hcoordinates, hstationary,
    hJ, hpolyZero, hclearedJ, hunique, hYalg, hconfigAlg, hdistanceAlg,
    hdiscAlg, hdiscEq⟩ := ExplicitRationalStationarySelection.actual_extremizer_unique_algebraic_root hm D hδ hfinite hN z hz
  let s := canonicalPattern hm3
  obtain ⟨P, hP⟩ := hwindowPolynomial (show 2 ≤ m by omega) s
  have hYwindow : selectedWindowEnergy (by omega) s (coordinates Y) <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [hcoordinates] using hwindow
  have hYpolynomial : 0 < aeval (coordinates Y) P :=
    (hP (coordinates Y)).1 hYwindow
  have hiff (Z : RationalStationarySystem.Variables m → ℝ)
      (hZwindow : 0 < aeval (coordinates Z) P) :
      ((∀ q, aeval Z (polynomials (by omega) (halfWord s) q) = 0) ↔
        Stationary (by omega) (halfWord s) Z) :=
    hsystemIff (show 8 ≤ m by omega) s P hP Z hZwindow
  have huniquePolynomial (Z : RationalStationarySystem.Variables m → ℝ)
      (hZwindow : 0 < aeval (coordinates Z) P)
      (hZzero : ∀ q, aeval Z (polynomials (by omega) (halfWord s) q) = 0) :
      Z = Y := by
    apply hunique Z
    · exact (hP (coordinates Z)).2 hZwindow
    · exact (hiff Z hZwindow).1 hZzero
  have hM : M (2 * m) = discriminant z :=
    (StructuralNote.M_eq_verified_diameterMaximum _).trans
      (WholeBoxLowerBound.diameterMaximum_eq_of_extremal hz)
  have hMroot : M (2 * m) = discriminant
      (RationalConfiguration.configuration (by omega) (rationalSign s)
        (coordinates Y)) := by
    calc
      M (2 * m) = discriminant z := hM
      _ = discriminant (RationalConfiguration.configuration (by omega)
          (rationalSign s) (coordinates Y)) := by
        rw [hcoordinates]
        exact hdiscEq.symm
  have hMalg : IsAlgebraic ℚ (M (2 * m)) := by
    rw [hMroot]
    simpa only [hcoordinates] using hdiscAlg
  refine ⟨hm3, Y, P, variables_card (by omega), hYpolynomial, hstationary, hiff,
    huniquePolynomial, hJ, hpolyZero, hclearedJ, hYalg, ?_, ?_, ?_,
    hMroot, hMalg⟩
  · simpa only [hcoordinates] using hconfigAlg
  · simpa only [hcoordinates] using hdistanceAlg
  · simpa only [hcoordinates] using hdiscAlg


end
end StructuralNote.ExplicitPolynomialSelection
