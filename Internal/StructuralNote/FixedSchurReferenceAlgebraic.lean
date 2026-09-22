import StructuralNote.FixedSchurAlgebraicData
import StructuralNote.FixedSchurRotatedCoefficients
import StructuralNote.PolynomialAlgebraicity

/-! A polynomial system for the fixed reference center. -/

namespace StructuralNote.FixedSchurReferenceAlgebraic

open Complex Filter Matrix MvPolynomial
open Erdos1045 Erdos1045.EventualExact FourierMultiplier FiniteFourierLift SchurLift SchurSpectrum
open FixedSchurAlgebraicData RationalExpressions
open EdgeCoordinates FixedSchurData FixedSchurChart FixedSchurRotatedCoefficients
open CommonClosureEnergy CommonDomainClosure CommonTangentialParameters
open FixedSchurRationalWindowEnergy
open scoped BigOperators Topology
noncomputable section

def jWeight {n : ℕ} (j k : Fin n) : ℝ :=
  2 * ((frame n k).re * (frame n j).im - (frame n k).im * (frame n j).re) / n

theorem jWeight_algebraic {n : ℕ} (j k : Fin n) : IsAlgebraic ℚ (jWeight j k) :=
  algebraic_div ((isAlgebraic_natCast 2).mul
    (((algebraicParts_frame n k).1.mul (algebraicParts_frame n j).2).sub
      ((algebraicParts_frame n k).2.mul (algebraicParts_frame n j).1)))
        (isAlgebraic_natCast n)

theorem J_eq_sum {n : ℕ} (q : Fin n → ℝ) (j : Fin n) :
    J q j = ∑ k, jWeight j k * q k := by
  simp [EdgeCoordinates.J, firstCoefficient, mul_im,
    jWeight, Finset.sum_mul, Finset.sum_div]
  simp only [Finset.mul_sum]
  congr 1
  funext k
  ring

def jCoeff {n : ℕ} (j k : Fin n) : Coeff :=
  ⟨jWeight j k, mem_algebraicClosure_iff.mpr (jWeight_algebraic j k)⟩

def jPolynomial {n : ℕ} (j : Fin n) : MvPolynomial (Fin n) Coeff :=
  ∑ k, C (jCoeff j k) * MvPolynomial.X k

@[simp] theorem eval_jPolynomial {n : ℕ} (j : Fin n) (q : Fin n → ℝ) :
    aeval q (jPolynomial j) = J q j := by
  rw [J_eq_sum]
  simp [jPolynomial, jCoeff]

def epsCoeff (n : ℕ) : Coeff :=
  ⟨epsilon n, mem_algebraicClosure_iff.mpr (epsilon_algebraic n)⟩

def chordCoeff (n : ℕ) : Coeff := 2 * RationalExpressions.ComplexExpression.cosine (1 / n)

@[simp] theorem chordCoeff_val (n : ℕ) :
    (chordCoeff n : ℝ) = 2 * Real.cos (Real.pi / n) := by
  have he : (((1 : ℚ) / n : ℚ) : ℝ) * Real.pi = Real.pi / n := by push_cast; ring
  change 2 * Real.cos ((((1 : ℚ) / n : ℚ) : ℝ) * Real.pi) = _
  rw [he]

def signCoeff {m : ℕ} {hm : 0 < m} (s : FiniteBox.SignPattern hm)
    (j : Fin (2 * m)) : Coeff :=
  ⟨FiniteBox.patternSign s j, mem_algebraicClosure_iff.mpr (by
    rcases FiniteBox.patternSign_is_sign s j with h | h
    · rw [h]; exact isAlgebraic_one
    · rw [h]; exact isAlgebraic_one.neg)⟩

def referencePolynomial {m : ℕ} {hm : 0 < m} (s : FiniteBox.SignPattern hm)
    (j : Fin (2 * m)) : MvPolynomial (Fin (2 * m)) Coeff :=
  (C (chordCoeff (2 * m)) + C (signCoeff s j * epsCoeff (2 * m)) *
    MvPolynomial.X j) ^ 2 + (C (epsCoeff (2 * m)) * jPolynomial j) ^ 2 - 4

theorem eval_referencePolynomial {m : ℕ} {hm : 0 < m} (s : FiniteBox.SignPattern hm)
    (q : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    aeval q (referencePolynomial s j) =
      (2 * Real.cos (Real.pi / (2 * m)) + FiniteBox.patternSign s j *
        epsilon (2 * m) * q j) ^ 2 + (epsilon (2 * m) * J q j) ^ 2 - 4 := by
  simp [referencePolynomial, signCoeff, epsCoeff]

theorem jacobian_mulVec {m : ℕ} {hm : 0 < m} (s : FiniteBox.SignPattern hm)
    (q w : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    (PolynomialAlgebraicity.jacobian (referencePolynomial s) q *ᵥ w) j =
      2 * FiniteBox.patternSign s j * epsilon (2 * m) *
        (2 * Real.cos (Real.pi / (2 * m)) +
          FiniteBox.patternSign s j * epsilon (2 * m) * q j) * w j +
        2 * epsilon (2 * m) ^ 2 * J q j * J w j := by
  classical
  have hj (k : Fin (2 * m)) :
      aeval q (pderiv k (jPolynomial j)) = jWeight j k := by
    simp [jPolynomial, jCoeff, Pi.single_apply, apply_ite]
  simp only [mulVec, dotProduct, PolynomialAlgebraicity.jacobian]
  have hder (k : Fin (2 * m)) :
      aeval q (pderiv k (referencePolynomial s j)) =
        2 * (2 * Real.cos (Real.pi / (2 * m)) +
          FiniteBox.patternSign s j * epsilon (2 * m) * q j) *
          (FiniteBox.patternSign s j * epsilon (2 * m) * (if j = k then 1 else 0)) +
          2 * epsilon (2 * m)^2 * J q j * jWeight j k := by
    have hfour : pderiv k (4 : MvPolynomial (Fin (2 * m)) Coeff) = 0 := by
      change pderiv k (C (4 : Coeff)) = 0
      exact pderiv_C
    simp [referencePolynomial, hj, signCoeff, epsCoeff, Pi.single_apply, apply_ite, hfour]
    split_ifs <;> ring
  simp_rw [hder]
  rw [J_eq_sum w]
  simp only [add_mul, Finset.sum_add_distrib]
  simp [mul_ite, ite_mul, ← Finset.mul_sum, mul_assoc]
  ring

theorem zero_data {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    FixedSchurData.X (by omega) 0 j = 2 * Real.cos (Real.pi / (2 * m)) ∧
    FixedSchurData.Y (by omega) 0 j = 0 ∧ tangent (by omega) (0 : Fin (2 * m) → ℂ) j = 0 := by
  have hanti : HalfPeriodic hm (fun _ : Fin (2 * m) => ((0 : ℝ) : ℂ)) := fun _ => rfl
  rw [FixedSchurChartRotated.X_eq_chordLength_mul_cos hm 0 hanti,
    FixedSchurChartRotated.Y_eq_chordLength_mul_sin hm 0 hanti]
  simp [FixedSchurChartRotated.chordLength, angleAverage, angleDifference,
    tangent, edgeRatio, LocalDFT.pairRatio, periodize]

theorem normalLinearization_zero {m : ℕ} (hm : 0 < m) (s : FiniteBox.SignPattern hm)
    (w : Fin (2 * m) → ℝ) (j : Fin (2 * m)) :
    normalLinearization hm s 0 0 w j = w j + FiniteBox.patternSign s j * epsilon (2 * m) *
      (J (coordinate hm s 0 0) j / FixedSchurRotatedPath.H (epsilon (2 * m))
        (J (coordinate hm s 0 0) j)) * J w j := by
  simp [normalLinearization, FixedSchurRotatedInverse.linearized, coefficientA, coefficientB,
    FixedSchurRotatedPath.alpha, FixedSchurRotatedPath.beta,
    FixedSchurNormalExpansion.rotatedS, FixedSchurNormalExpansion.rotatedP,
    FixedSchurRotatedAlgebra.tangential, angleAverage, (zero_data hm j).2.2]

theorem eventual_reference_algebraic : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (m := m) (by omega)),
      (∀ j, IsAlgebraic ℚ (coordinate (by omega) s 0 0 j)) ∧
      ∀ j, AlgebraicParts (fixedReferenceCenter (by omega) s j) := by
  filter_upwards [eventual_coordinate_properties, FixedSchurExistence.eventual_ball_positive_input,
    eventual_actual_solution_bounds] with m hprops hinput hbound
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

end
end StructuralNote.FixedSchurReferenceAlgebraic
