import StructuralNote.RationalComplexExpressions

/-! Explicit real polynomial fractions for the actual configuration (10.4),
including the two closure polynomials and every squared pair distance. -/

namespace StructuralNote.RationalConfigurationPolynomials

open RationalExpressions Erdos1045.EventualExact
open scoped BigOperators
noncomputable section

abbrev Vars := RationalConfiguration.Variables
abbrev RExpr (m : ℕ) := Expression (Vars m)
abbrev CExpr (m : ℕ) := ComplexExpression (Vars m)

def sign {m : ℕ} (σ : Fin m → Bool) (j : Fin m) : ℝ := if σ j then 1 else -1
def signExpr {m : ℕ} (σ : Fin m → Bool) (j : Fin m) : RExpr m :=
  Expression.constant (if σ j then 1 else -1)
def angle {m : ℕ} (j : Fin m) : RExpr m :=
  if hj : j.val = 0 then 0 else Expression.var (.inl ⟨j.val - 1, by omega⟩)
def crossingAngle {m : ℕ} (j : Fin m) : RExpr m := Expression.var (.inr j)

def diameter {m : ℕ} (hm : 0 < m) (j : ℕ) : CExpr m :=
  ComplexExpression.unit ((j : ℚ) / m) *
    ComplexExpression.rotation (angle ⟨j % m, Nat.mod_lt _ hm⟩)
def crossingUnit {m : ℕ} (j : Fin m) : CExpr m :=
  ComplexExpression.unit (((j.val : ℚ) + 1 / 2) / m) * ComplexExpression.rotation (crossingAngle j)
def increment {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : Fin m) : CExpr m :=
  ComplexExpression.ofReal (signExpr σ j) *
    (ComplexExpression.ofReal (Expression.constant 2) * crossingUnit j -
      diameter hm j - diameter hm (j.val + 1))
def centerPrefix {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (r : ℕ) : CExpr m :=
  ComplexExpression.sum (Finset.range r) (fun j => if hj : j < m then increment hm σ ⟨j, hj⟩ else 0)
def closure {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) : CExpr m :=
  ComplexExpression.sum Finset.univ (increment hm σ)
def point {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : ℕ) : CExpr m :=
  centerPrefix hm σ (j % m) + diameter hm j
def configuration {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : Fin (2 * m)) : CExpr m :=
  point hm σ j

theorem sign_valid {m : ℕ} (σ : Fin m → Bool) (j : Fin m) (X : Vars m → ℝ) :
    (signExpr σ j).Valid X := Expression.valid_constant _ _
theorem sign_eval {m : ℕ} (σ : Fin m → Bool) (j : Fin m) (X : Vars m → ℝ) :
    (signExpr σ j).eval X = sign σ j := by
  cases h : σ j <;> simp [signExpr, sign, h]

theorem angle_valid {m : ℕ} (j : Fin m) (X : Vars m → ℝ) : (angle j).Valid X := by
  unfold angle
  split
  · exact Expression.valid_zero X
  · exact Expression.valid_variable _ _
theorem angle_eval {m : ℕ} (j : Fin m) (X : Vars m → ℝ) :
    (angle j).eval X = RationalConfiguration.angleParameter X j := by
  unfold angle RationalConfiguration.angleParameter
  split <;> simp

theorem diameter_valid {m : ℕ} (hm : 0 < m) (j : ℕ) (X : Vars m → ℝ) :
    (diameter hm j).Valid X :=
  (ComplexExpression.valid_unit _ X).mul (ComplexExpression.valid_rotation (angle_valid _ X))
theorem diameter_eval {m : ℕ} (hm : 0 < m) (j : ℕ) (X : Vars m → ℝ) :
    (diameter hm j).eval X = RationalConfiguration.diameter hm X j := by
  rw [diameter, ComplexExpression.eval_mul (ComplexExpression.valid_unit _ X)
    (ComplexExpression.valid_rotation (angle_valid _ X)), ComplexExpression.eval_unit,
    ComplexExpression.eval_rotation (angle_valid _ X), angle_eval]
  have he : (((j : ℚ) / m : ℚ) : ℝ) * Real.pi = Real.pi / m * j := by push_cast; ring
  rw [he]
  rfl

theorem crossingUnit_valid {m : ℕ} (j : Fin m) (X : Vars m → ℝ) :
    (crossingUnit j).Valid X :=
  (ComplexExpression.valid_unit _ X).mul (ComplexExpression.valid_rotation (Expression.valid_variable _ X))
theorem crossingUnit_eval {m : ℕ} (j : Fin m) (X : Vars m → ℝ) :
    (crossingUnit j).eval X = RationalConfiguration.crossingUnit X j := by
  rw [crossingUnit, crossingAngle, ComplexExpression.eval_mul (ComplexExpression.valid_unit _ X)
    (ComplexExpression.valid_rotation (Expression.valid_variable _ X)), ComplexExpression.eval_unit,
    ComplexExpression.eval_rotation (Expression.valid_variable _ X)]
  have he : ((((j.val : ℚ) + 1 / 2) / m : ℚ) : ℝ) * Real.pi = LensClosure.midpoint m j := by
    unfold LensClosure.midpoint
    push_cast
    ring
  rw [he]
  simp [RationalConfiguration.crossingUnit, RationalConfiguration.crossingParameter]

theorem increment_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : Fin m) (X : Vars m → ℝ) :
    (increment hm σ j).Valid X :=
  (ComplexExpression.valid_ofReal (sign_valid σ j X)).mul
    (((ComplexExpression.valid_ofReal (Expression.valid_constant 2 X)).mul (crossingUnit_valid j X)).sub
      (diameter_valid hm j X) |>.sub (diameter_valid hm (j.val + 1) X))

theorem increment_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : Fin m) (X : Vars m → ℝ) :
    (increment hm σ j).eval X = RationalConfiguration.increment hm (sign σ) X j := by
  have hs := ComplexExpression.valid_ofReal (sign_valid σ j X)
  have h2 := ComplexExpression.valid_ofReal (Expression.valid_constant 2 X)
  have hu := crossingUnit_valid j X
  have hd := diameter_valid hm j X
  have he := diameter_valid hm (j.val + 1) X
  rw [increment, ComplexExpression.eval_mul hs (((h2.mul hu).sub hd).sub he),
    ComplexExpression.eval_sub ((h2.mul hu).sub hd) he,
    ComplexExpression.eval_sub (h2.mul hu) hd, ComplexExpression.eval_mul h2 hu]
  simp only [ComplexExpression.eval_ofReal, Expression.eval_constant, sign_eval,
    crossingUnit_eval, diameter_eval, RationalConfiguration.increment, RationalChart.crossingIncrement]
  have htwo : ((2 : Coeff) : ℝ) = 2 := rfl
  rw [htwo]
  norm_num

theorem centerPrefix_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (r : ℕ) (X : Vars m → ℝ) :
    (centerPrefix hm σ r).Valid X := by
  apply ComplexExpression.valid_sum
  intro j _
  split
  · exact increment_valid hm σ _ X
  · exact ComplexExpression.valid_zero X

theorem centerPrefix_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (r : ℕ) (X : Vars m → ℝ) :
    (centerPrefix hm σ r).eval X = RationalConfiguration.centerPrefix hm (sign σ) X r := by
  rw [centerPrefix, ComplexExpression.eval_sum]
  · apply Finset.sum_congr rfl
    intro j _
    split <;> simp [increment_eval]
  · intro j _
    split
    · exact increment_valid hm σ _ X
    · exact ComplexExpression.valid_zero X

theorem closure_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) :
    (closure hm σ).Valid X := ComplexExpression.valid_sum _ _ X (fun j _ => increment_valid hm σ j X)
theorem closure_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) :
    (closure hm σ).eval X = RationalConfiguration.closure hm (sign σ) X := by
  rw [closure, ComplexExpression.eval_sum _ _ X (fun j _ => increment_valid hm σ j X)]
  simp only [increment_eval, RationalConfiguration.closure]

theorem point_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : ℕ) (X : Vars m → ℝ) :
    (point hm σ j).Valid X := (centerPrefix_valid hm σ _ X).add (diameter_valid hm j X)
theorem point_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : ℕ) (X : Vars m → ℝ) :
    (point hm σ j).eval X = RationalConfiguration.point hm (sign σ) X j := by
  rw [point, ComplexExpression.eval_add (centerPrefix_valid hm σ _ X) (diameter_valid hm j X),
    centerPrefix_eval, diameter_eval]
  rfl
theorem configuration_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : Fin (2 * m)) (X : Vars m → ℝ) :
    (configuration hm σ j).Valid X := point_valid hm σ j X
theorem configuration_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (j : Fin (2 * m)) (X : Vars m → ℝ) :
    (configuration hm σ j).eval X = RationalConfiguration.configuration hm (sign σ) X j := point_eval hm σ j X

def closurePolynomials {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (i : Fin 2) :
    MvPolynomial (Vars m) Coeff := if i.val = 0 then (closure hm σ).re.numerator else (closure hm σ).im.numerator

theorem closure_polynomials_iff {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) :
    (∀ i, MvPolynomial.aeval X (closurePolynomials hm σ i) = 0) ↔
      RationalConfiguration.closure hm (sign σ) X = 0 := by
  have hvalid := closure_valid hm σ X
  have he := closure_eval hm σ X
  rw [← he, Complex.ext_iff]
  constructor
  · intro h
    exact ⟨(Expression.eval_eq_zero_iff hvalid.1).2 (h 0),
      (Expression.eval_eq_zero_iff hvalid.2).2 (h 1)⟩
  · intro h i
    fin_cases i
    · exact (Expression.eval_eq_zero_iff hvalid.1).1 h.1
    · exact (Expression.eval_eq_zero_iff hvalid.2).1 h.2

def squaredDistance {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (i j : Fin (2 * m)) : RExpr m :=
  (configuration hm σ i - configuration hm σ j).squareNorm
theorem squaredDistance_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (i j : Fin (2 * m)) (X : Vars m → ℝ) : (squaredDistance hm σ i j).Valid X :=
  ComplexExpression.valid_squareNorm ((configuration_valid hm σ i X).sub (configuration_valid hm σ j X))
theorem squaredDistance_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (i j : Fin (2 * m)) (X : Vars m → ℝ) :
    (squaredDistance hm σ i j).eval X = Complex.normSq
      (RationalConfiguration.configuration hm (sign σ) X i - RationalConfiguration.configuration hm (sign σ) X j) := by
  rw [squaredDistance, ComplexExpression.eval_squareNorm
    ((configuration_valid hm σ i X).sub (configuration_valid hm σ j X)),
    ComplexExpression.eval_sub (configuration_valid hm σ i X) (configuration_valid hm σ j X),
    configuration_eval, configuration_eval]

end
end StructuralNote.RationalConfigurationPolynomials
