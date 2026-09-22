import StructuralNote.FixedSchurRationalWindowDomain
import StructuralNote.RationalConfigurationPolynomials
import StructuralNote.FixedSchurAlgebraicData
import StructuralNote.FixedSchurReferenceAlgebraic

/-! The literal Section 11 window is one rational inequality.  This file
constructs its rational expression and clears its (positive) denominator to
one polynomial inequality.  The reference-center encoding is kept explicit:
instantiating it for the noncomputably selected fixed-Schur reference is the
remaining algebraicity input, rather than being hidden in the clearing step. -/

namespace StructuralNote.FixedSchurRationalWindowPolynomial

open Erdos1045 Erdos1045.EventualExact Complex Filter
open RationalExpressions RationalConfigurationPolynomials
open FixedSchurRationalWindowEnergy FixedSchurRationalWindowDomain
open FixedSchurAlgebraicData
open FixedSchurReferenceAlgebraic
open AngularObjectiveCurvature CommonDomainRadius
open SchurSpectrum
open MvPolynomial
open scoped BigOperators
noncomputable section

abbrev Vars := RationalConfiguration.Variables

/-- Algebraic coefficients representing a prescribed complex-valued finite
family.  This is the precise input needed for a rational expression containing
the fixed reference center. -/
structure ComplexFamilyEncoding {n : ℕ} (c : Fin n → ℂ) where
  re : Fin n → Coeff
  im : Fin n → Coeff
  value_eq : ∀ j, (⟨((re j : Coeff) : ℝ), ((im j : Coeff) : ℝ)⟩ : ℂ) = c j

namespace ComplexFamilyEncoding

variable {n : ℕ} {c : Fin n → ℂ}

def expression (e : ComplexFamilyEncoding c) {i : Type*} (j : Fin n) :
    ComplexExpression i :=
  ⟨Expression.constant (e.re j), Expression.constant (e.im j)⟩

theorem valid (e : ComplexFamilyEncoding c) {i : Type*} (j : Fin n) (X : i → ℝ) :
    (e.expression j).Valid X :=
  ⟨Expression.valid_constant _ _, Expression.valid_constant _ _⟩

theorem eval (e : ComplexFamilyEncoding c) {i : Type*} (j : Fin n) (X : i → ℝ) :
    (e.expression j).eval X = c j := by
  simpa [expression, ComplexExpression.eval] using e.value_eq j

end ComplexFamilyEncoding

/-- Algebraic real and imaginary parts canonically give coefficients in the
real algebraic closure. -/
def complexFamilyEncodingOfAlgebraic {n : ℕ} {c : Fin n → ℂ}
    (h : ∀ j, IsAlgebraic ℚ (c j).re ∧ IsAlgebraic ℚ (c j).im) :
    ComplexFamilyEncoding c where
  re j := ⟨(c j).re, mem_algebraicClosure_iff.mpr (h j).1⟩
  im j := ⟨(c j).im, mem_algebraicClosure_iff.mpr (h j).2⟩
  value_eq _ := rfl

/-- Algebraic coefficients for the inverse squared chords occurring in pair
energy.  The diagonal coefficient is zero because Lean's field division uses
`0⁻¹ = 0`. -/
structure PairEnergyWeights (n : ℕ) where
  coefficient : Fin n → Fin n → Coeff
  value_eq : ∀ i j, ((coefficient i j : Coeff) : ℝ) =
    (normSq (LocalPhase.regularRoot n ^ (i : ℕ) -
      LocalPhase.regularRoot n ^ (j : ℕ)))⁻¹

/-- The pair-energy chord weights themselves are algebraic; unlike the fixed
reference center, they require no additional hypothesis. -/
def chordWeights (n : ℕ) : PairEnergyWeights n where
  coefficient i j :=
    ⟨(normSq (LocalPhase.regularRoot n ^ (i : ℕ) -
        LocalPhase.regularRoot n ^ (j : ℕ)))⁻¹,
      mem_algebraicClosure_iff.mpr (by
        have hi := (algebraicParts_root n).pow i.val
        have hj := (algebraicParts_root n).pow j.val
        have hd := hi.sub hj
        exact IsAlgebraic.inv_iff.mpr
          ((hd.1.mul hd.1).add (hd.2.mul hd.2)))⟩
  value_eq _ _ := rfl

/-- A rational expression for pair energy once its constant algebraic chord
weights have been supplied. -/
def pairEnergyExpression {i : Type*} {n : ℕ} (w : PairEnergyWeights n)
    (c : Fin n → ComplexExpression i) : Expression i :=
  Expression.sum Finset.univ (fun a =>
    Expression.sum Finset.univ (fun b =>
      (c a - c b).squareNorm * Expression.constant (w.coefficient a b))) /
    Expression.constant 2

theorem pairEnergyExpression_valid {i : Type*} {n : ℕ} (w : PairEnergyWeights n)
    (c : Fin n → ComplexExpression i) (X : i → ℝ)
    (hc : ∀ j, (c j).Valid X) :
    (pairEnergyExpression w c).Valid X := by
  apply Expression.Valid.div
  · apply Expression.valid_sum
    intro a _
    apply Expression.valid_sum
    intro b _
    exact (ComplexExpression.valid_squareNorm ((hc a).sub (hc b))).mul
      (Expression.valid_constant _ _)
  · exact Expression.valid_constant _ _
  · norm_num

theorem pairEnergyExpression_eval {i : Type*} {n : ℕ} (hn : 0 < n)
    (w : PairEnergyWeights n) (c : Fin n → ComplexExpression i) (X : i → ℝ)
    (hc : ∀ j, (c j).Valid X) :
    (pairEnergyExpression w c).eval X = pairEnergy hn (fun j => (c j).eval X) := by
  rw [pairEnergyExpression, Expression.eval_div,
    Expression.eval_sum _ _ X]
  · have htwo : ((2 : Coeff) : ℝ) = 2 := rfl
    rw [show (Expression.constant (2 : Coeff)).eval X = 2 by
      simpa only [Expression.eval_constant] using htwo]
    simp only [pairEnergy_eq_chord_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [Expression.eval_sum]
    · apply Finset.sum_congr rfl
      intro b _
      rw [Expression.eval_mul,
        ComplexExpression.eval_squareNorm ((hc a).sub (hc b)),
        ComplexExpression.eval_sub (hc a) (hc b), Expression.eval_constant,
        w.value_eq, div_eq_mul_inv]
    · intro b _
      exact (ComplexExpression.valid_squareNorm ((hc a).sub (hc b))).mul
        (Expression.valid_constant _ _)
  · intro a _
    apply Expression.valid_sum
    intro b _
    exact (ComplexExpression.valid_squareNorm ((hc a).sub (hc b))).mul
      (Expression.valid_constant _ _)

def windowHalfWord {m : ℕ} {hm : 0 < m}
    (s : FiniteBox.SignPattern hm) : Fin m → Bool :=
  fun j => s.val ⟨j.val, by omega⟩

theorem sign_windowHalfWord {m : ℕ} {hm : 0 < m}
    (s : FiniteBox.SignPattern hm) :
    sign (windowHalfWord s) = rationalSign s := by
  funext j
  rfl

def angleExpression {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    ComplexExpression (Vars m) :=
  ComplexExpression.ofReal
    (angle ⟨j.val % m, Nat.mod_lt _ hm⟩)

theorem angleExpression_valid {m : ℕ} (hm : 0 < m) (j : Fin (2 * m))
    (X : Vars m → ℝ) :
    (angleExpression hm j).Valid X :=
  ComplexExpression.valid_ofReal (angle_valid _ X)

theorem angleExpression_eval {m : ℕ} (hm : 0 < m) (j : Fin (2 * m))
    (X : Vars m → ℝ) :
    (angleExpression hm j).eval X = (extendedAngleParameter hm X j : ℂ) := by
  simp [angleExpression, angle_eval, extendedAngleParameter]

def centerExpression {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (j : Fin (2 * m)) :
    ComplexExpression (Vars m) :=
  centerPrefix hm (windowHalfWord s) (j.val % m)

theorem centerExpression_valid {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (j : Fin (2 * m)) (X : Vars m → ℝ) :
    (centerExpression hm s j).Valid X :=
  centerPrefix_valid hm _ _ X

theorem centerExpression_eval {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm) (j : Fin (2 * m)) (X : Vars m → ℝ) :
    (centerExpression hm s j).eval X = rationalCenter hm (rationalSign s) X j := by
  rw [centerExpression, centerPrefix_eval, sign_windowHalfWord]
  rfl

/-- The exact rational expression for the literal selected window, conditional
only on an algebraic encoding of its fixed reference and of the constant chord
weights. -/
def selectedWindowExpression {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm)
    (ref : ComplexFamilyEncoding (fixedReferenceCenter hm s)) : Expression (Vars m) :=
  pairEnergyExpression (chordWeights (2 * m)) (angleExpression hm) +
    pairEnergyExpression (chordWeights (2 * m))
      (fun j => centerExpression hm s j - ref.expression j)

theorem selectedWindowExpression_valid {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm)
    (ref : ComplexFamilyEncoding (fixedReferenceCenter hm s))
    (X : Vars m → ℝ) :
    (selectedWindowExpression hm s ref).Valid X := by
  apply Expression.Valid.add
  · exact pairEnergyExpression_valid (chordWeights _) _ X
      (fun j => angleExpression_valid hm j X)
  · exact pairEnergyExpression_valid (chordWeights _) _ X
      (fun j => (centerExpression_valid hm s j X).sub (ref.valid j X))

theorem selectedWindowExpression_eval {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm)
    (ref : ComplexFamilyEncoding (fixedReferenceCenter hm s))
    (X : Vars m → ℝ) :
    (selectedWindowExpression hm s ref).eval X = selectedWindowEnergy hm s X := by
  rw [selectedWindowExpression,
    Expression.eval_add
      (pairEnergyExpression_valid (chordWeights _) _ X
        (fun j => angleExpression_valid hm j X))
      (pairEnergyExpression_valid (chordWeights _) _ X
        (fun j => (centerExpression_valid hm s j X).sub (ref.valid j X))),
    pairEnergyExpression_eval (by omega) (chordWeights _) _ X
      (fun j => angleExpression_valid hm j X),
    pairEnergyExpression_eval (by omega) (chordWeights _) _ X
      (fun j => (centerExpression_valid hm s j X).sub (ref.valid j X))]
  have hangle : (fun j => (angleExpression hm j).eval X) =
      fun j => (extendedAngleParameter hm X j : ℂ) := by
    funext j
    exact angleExpression_eval hm j X
  have hcenter : (fun j => (centerExpression hm s j - ref.expression j).eval X) =
      rationalCenter hm (rationalSign s) X - fixedReferenceCenter hm s := by
    funext j
    rw [ComplexExpression.eval_sub (centerExpression_valid hm s j X) (ref.valid j X),
      centerExpression_eval, ref.eval]
    rfl
  unfold selectedWindowEnergy
  rw [hangle, hcenter]

/-- The rational coefficient equal to the Section 11 window radius. -/
def windowRadiusCoeff (m : ℕ) : Coeff :=
  ⟨(logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2),
    mem_algebraicClosure_iff.mpr (by
      rw [div_eq_mul_inv]
      exact ((isAlgebraic_natCast (logOrder (2 * m))).pow 2).mul
        (IsAlgebraic.inv_iff.mpr
          ((isAlgebraic_natCast 8).mul
            (((isAlgebraic_natCast 2).mul (isAlgebraic_natCast m)).pow 2))))⟩

theorem windowRadiusCoeff_value (m : ℕ) :
    ((windowRadiusCoeff m : Coeff) : ℝ) =
      (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) := by
  rfl

/-- The one polynomial obtained after multiplying by the square of the
denominator.  Squaring makes the clearing step independent of its sign. -/
def selectedWindowPolynomial {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm)
    (ref : ComplexFamilyEncoding (fixedReferenceCenter hm s)) :
    MvPolynomial (Vars m) Coeff :=
  C (windowRadiusCoeff m) * (selectedWindowExpression hm s ref).denominator ^ 2 -
    (selectedWindowExpression hm s ref).numerator *
      (selectedWindowExpression hm s ref).denominator

/-- The literal strict energy window is exactly one strict polynomial
inequality.  Validity of the rational expression is already proved globally;
the squared-denominator form therefore needs no sign hypothesis. -/
theorem selectedWindow_lt_iff_polynomial_pos {m : ℕ} (hm : 0 < m)
    (s : FiniteBox.SignPattern hm)
    (ref : ComplexFamilyEncoding (fixedReferenceCenter hm s))
    (X : Vars m → ℝ) :
    selectedWindowEnergy hm s X <
        (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ↔
      0 < aeval X (selectedWindowPolynomial hm s ref) := by
  let q := selectedWindowExpression hm s ref
  have hvalid : aeval X q.denominator ≠ 0 :=
    selectedWindowExpression_valid hm s ref X
  have hrewrite : aeval X q.numerator / aeval X q.denominator =
      (aeval X q.numerator * aeval X q.denominator) /
        aeval X q.denominator ^ 2 := by
    field_simp
  rw [← selectedWindowExpression_eval hm s ref X,
    ← windowRadiusCoeff_value m]
  unfold Expression.eval
  rw [hrewrite, div_lt_iff₀ (sq_pos_of_ne_zero hvalid)]
  simp only [selectedWindowPolynomial, map_sub, map_mul, map_pow, aeval_C]
  rw [show algebraMap Coeff ℝ (windowRadiusCoeff m) =
      (windowRadiusCoeff m : ℝ) by rfl]
  constructor <;> intro h <;> linarith

/-- For every sufficiently large half-size and every fixed-Schur word, one
polynomial over the real algebraic numbers cuts out exactly the manuscript's
literal selected energy window.  There are no extra branch, smallness, or
denominator hypotheses. -/
theorem eventual_exists_selectedWindowPolynomial : ∀ᶠ m : ℕ in atTop,
    ∀ (hm : 2 ≤ m) (s : FiniteBox.SignPattern (by omega : 0 < m)),
      ∃ P : MvPolynomial (Vars m) Coeff, ∀ X : Vars m → ℝ,
        (selectedWindowEnergy (by omega) s X <
            (logOrder (2 * m) : ℝ) ^ 2 / (8 * (2 * m : ℝ) ^ 2) ↔
          0 < aeval X P) := by
  filter_upwards [eventual_reference_algebraic] with m href
  intro hm s
  let ref : ComplexFamilyEncoding (fixedReferenceCenter (by omega) s) :=
    complexFamilyEncodingOfAlgebraic (href hm s).2
  exact ⟨selectedWindowPolynomial (by omega) s ref,
    fun X => selectedWindow_lt_iff_polynomial_pos (by omega) s ref X⟩

end
end StructuralNote.FixedSchurRationalWindowPolynomial
