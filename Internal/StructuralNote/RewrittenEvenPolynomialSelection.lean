import StructuralNote.FixedSchurRationalWindowPolynomial
import StructuralNote.RewrittenEvenAlgebraicMaximum

/-! The one polynomial window and the actual rational stationary system are
assembled at the canonical even-order maximizer.  Polynomial-system zeros are
compared with genuine stationary roots only after the window equations force
closure and collision-freeness, so invalid cleared-denominator zeros are not
silently admitted. -/

namespace StructuralNote.RewrittenEvenPolynomialSelection

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

/-- Inside the single polynomial window, the cleared polynomial equations are
equivalent to the genuine rational stationary system.  The forward direction
first recovers the two closure equations, then invokes window
collision-freeness; this excludes spurious roots caused by cleared invalid
denominators. -/
theorem eventual_window_polynomial_system_iff : ∀ᶠ m : ℕ in atTop,
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
  filter_upwards [eventual_selectedWindow_collisionFree] with m hcollision
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
theorem eventual_even_maximum_single_polynomial_root :
    ∃ m₀ : ℕ, ∀ m ≥ m₀,
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
  obtain ⟨m₀, hroot⟩ := eventual_actual_extremizer_unique_algebraic_root
  obtain ⟨m₁, hwindowPolynomial⟩ := eventually_atTop.1
    eventual_exists_selectedWindowPolynomial
  obtain ⟨m₂, hsystemIff⟩ := eventually_atTop.1
    eventual_window_polynomial_system_iff
  refine ⟨max 8 (max m₀ (max m₁ m₂)), ?_⟩
  intro m hm
  obtain ⟨z, hz⟩ := WholeBoxLowerBound.exists_diameterExtremal
    (show 0 < 2 * m by omega)
  obtain ⟨hm3, x, Y, _, _, _, _, hwindow, hcoordinates, hstationary,
    hJ, hpolyZero, hclearedJ, hunique, hYalg, hconfigAlg, hdistanceAlg,
    hdiscAlg, hdiscEq⟩ := hroot m (by omega) z hz
  let s := canonicalPattern hm3
  obtain ⟨P, hP⟩ := hwindowPolynomial m (by omega)
    (show 2 ≤ m by omega) s
  have hYwindow : selectedWindowEnergy (by omega) s (coordinates Y) <
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
    simpa only [hcoordinates] using hwindow
  have hYpolynomial : 0 < aeval (coordinates Y) P :=
    (hP (coordinates Y)).1 hYwindow
  have hiff (Z : RationalStationarySystem.Variables m → ℝ)
      (hZwindow : 0 < aeval (coordinates Z) P) :
      ((∀ q, aeval Z (polynomials (by omega) (halfWord s) q) = 0) ↔
        Stationary (by omega) (halfWord s) Z) :=
    hsystemIff m (by omega) (show 8 ≤ m by omega) s P hP Z hZwindow
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
end StructuralNote.RewrittenEvenPolynomialSelection
