import StructuralNote.ExplicitFixedSchurCoefficients
import StructuralNote.FixedSchurRationalWindowPolynomial
/-! Algebraic reference coordinates and a single polynomial selection window
at an explicit order. -/
namespace StructuralNote.ExplicitRationalPolynomial
open Complex Filter Matrix MvPolynomial
open Erdos1045 Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open FixedSchurAlgebraicData RationalExpressions
open EdgeCoordinates FixedSchurData FixedSchurChart FixedSchurRotatedCoefficients
open CommonClosureEnergy CommonDomainClosure CommonTangentialParameters
open FixedSchurRationalWindowEnergy
open scoped BigOperators Topology
open Erdos1045 Erdos1045.EventualExact Complex Filter
open RationalExpressions RationalConfigurationPolynomials
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open FixedSchurAlgebraicData
open FixedSchurReferenceAlgebraic
open AngularObjectiveCurvature CommonDomainRadius
open SchurSpectrum
open MvPolynomial
open scoped BigOperators
open FixedSchurReferenceAlgebraic FixedSchurRationalWindowPolynomial
noncomputable section
theorem reference_algebraic {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega)),
      (∀ j, IsAlgebraic ℚ (coordinate (by omega) s 0 0 j)) ∧
      ∀ j, AlgebraicParts (fixedReferenceCenter (by omega) s j) := by
  have hprops := ExplicitHessianThresholdFixedSchur.coordinate_properties hN
  have hinput := ExplicitHessianThresholdFixedSchur.ball_positive_input hN
  have hbound := ExplicitFixedSchurCoefficients.actual_solution_bounds hN
  clear hN
  intro hm s
  let q := coordinate (by omega) s 0 0
  have hdom := zero_inDomain (show 0 < m by omega)
  have hp := hprops hm s 0 0 hdom
  have hs := hinput (show 0 < m by omega) 0 0 _ hdom (FiniteBox.patternSign_is_sign s) q hp.close
  have hroot (j : Fin (2 * m)) := FixedSchurEquations.solution_positive_branch
    (show 0 < m by omega) 0 0 _ q (FiniteBox.patternSign_is_sign s) hp.fixed hs j
  have hr (j : Fin (2 * m)) :
      0 < 2 * Real.cos (Real.pi / (2 * m)) + FiniteBox.patternSign s j * epsilon (2 * m) * q j ∧
      (2 * Real.cos (Real.pi / (2 * m)) + FiniteBox.patternSign s j * epsilon (2 * m) * q j)^2 +
        (epsilon (2 * m) * J q j)^2 = 4 := by
    have hh := hroot j
    simp only [(zero_data (by omega : 0 < m) j).1,
      (zero_data (by omega : 0 < m) j).2.1,
      Pi.add_apply, (zero_data (by omega : 0 < m) j).2.2, add_zero, zero_add] at hh
    refine ⟨hh.1, ?_⟩
    rcases FiniteBox.patternSign_is_sign s j with hj | hj
    · simpa only [hj, one_mul] using hh.2
    · simpa only [hj, neg_one_mul, neg_mul, neg_sq, one_mul] using hh.2
  have hz : ∀ j, aeval q (referencePolynomial s j) = 0 := by
    intro j
    rw [eval_referencePolynomial]
    linarith [(hr j).2]
  have hker : ∀ w : Fin (2 * m) → ℝ,
      PolynomialAlgebraicity.jacobian (referencePolynomial s) q *ᵥ w = 0 → w = 0 := by
    intro w hw
    have hlin : normalLinearization (by omega) s 0 0 w = 0 := by
      funext j
      have hR := (hr j).1
      have hH : FixedSchurRotatedPath.H (epsilon (2 * m)) (J q j) =
          2 * Real.cos (Real.pi / (2 * m)) +
            FiniteBox.patternSign s j * epsilon (2 * m) * q j := by
        unfold FixedSchurRotatedPath.H
        rw [show 4 - (epsilon (2 * m) * J q j)^2 =
          (2 * Real.cos (Real.pi / (2 * m)) +
            FiniteBox.patternSign s j * epsilon (2 * m) * q j)^2 by linarith [(hr j).2],
          Real.sqrt_sq_eq_abs, abs_of_pos hR]
      have heps := epsilon_pos (show 2 ≤ 2 * m by omega)
      have hsign : FiniteBox.patternSign s j ≠ 0 := by
        rcases FiniteBox.patternSign_is_sign s j with hj | hj <;> rw [hj] <;> norm_num
      have heq : 2 * FiniteBox.patternSign s j * epsilon (2 * m) *
          (2 * Real.cos (Real.pi / (2 * m)) + FiniteBox.patternSign s j * epsilon (2 * m) * q j) *
          normalLinearization (by omega) s 0 0 w j =
          (PolynomialAlgebraicity.jacobian (referencePolynomial s) q *ᵥ w) j := by
        rw [normalLinearization_zero, jacobian_mulVec]
        change 2 * FiniteBox.patternSign s j * epsilon (2 * m) * _ *
          (w j + FiniteBox.patternSign s j * epsilon (2 * m) *
            (J q j / FixedSchurRotatedPath.H (epsilon (2 * m)) (J q j)) * J w j) = _
        rw [hH]
        field_simp
        rcases FiniteBox.patternSign_is_sign s j with hj | hj <;> rw [hj] <;> ring
      rw [hw, Pi.zero_apply] at heq
      exact (mul_eq_zero.mp heq).resolve_left
        (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hsign) heps.ne') hR.ne')
    have hn := (hbound hm s 0 0 hdom w).2.2
    rw [hlin, norm_zero, mul_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg w))
  have hJ : (PolynomialAlgebraicity.jacobian (referencePolynomial s) q).det ≠ 0 := by
    have hi : Function.Injective
        (PolynomialAlgebraicity.jacobian (referencePolynomial s) q).mulVec := by
      intro u v huv
      apply sub_eq_zero.mp
      apply hker
      rw [Matrix.mulVec_sub, huv, sub_self]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero
  let : Algebra.IsAlgebraic ℚ Coeff := algebraicClosure.isAlgebraic ℚ ℝ
  have hq : ∀ j, IsAlgebraic ℚ (q j) :=
    PolynomialAlgebraicity.isAlgebraic_over_base_of_nonsingular_zero _ q hz hJ
  refine ⟨hq, fun j => ?_⟩
  simpa only [fixedReferenceCenter, FixedSchurLinear.center, Pi.add_apply, Pi.zero_apply,
    add_zero] using canonicalLift_algebraic q hq j

theorem exists_selectedWindowPolynomial {m : ℕ} (hN : ExplicitHessianThreshold.orderThreshold ≤ 2 * m) : ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m)),
      ∃ P : MvPolynomial (RationalConfiguration.Variables m) Coeff, ∀ X : RationalConfiguration.Variables m → ℝ,
        (selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ↔
          0 < aeval X P) := by
  have href := reference_algebraic hN
  clear hN
  intro hm s
  let ref : ComplexFamilyEncoding (fixedReferenceCenter (by omega) s) :=
    complexFamilyEncodingOfAlgebraic (href hm s).2
  exact ⟨selectedWindowPolynomial (by omega) s ref,
    fun X => selectedWindow_lt_iff_polynomial_pos (by omega) s ref X⟩

end
end StructuralNote.ExplicitRationalPolynomial
