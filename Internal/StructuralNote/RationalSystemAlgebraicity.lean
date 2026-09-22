import StructuralNote.RationalStationarySystem
import StructuralNote.PolynomialAlgebraicity

/-! Clearing denominators rescales the actual coordinate Jacobian rows at a
zero. This connects a geometric nondegeneracy proof to algebraicity of the
specified distance-product system, without postulating a polynomial encoding. -/

namespace StructuralNote.RationalSystemAlgebraicity

open RationalExpressions MvPolynomial
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def jacobian (f : ι → Expression ι) (x : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => deriv (fun t => (f i).eval (Function.update x j t)) (x j)

omit [Fintype ι] [DecidableEq ι] in
theorem numerator_partial_at_zero (f : Expression ι) (x : ι → ℝ)
    (hv : f.Valid x) (hz : f.eval x = 0) (i : ι) :
    aeval x (pderiv i f.numerator) = aeval x f.denominator *
      (Expression.coordinateDerivative i f).eval x := by
  have hn := (Expression.eval_eq_zero_iff hv).1 hz
  change _ = aeval x f.denominator *
    (aeval x (pderiv i f.numerator * f.denominator - f.numerator * pderiv i f.denominator) /
      aeval x (f.denominator * f.denominator))
  rw [map_sub, map_mul, map_mul, map_mul, hn, zero_mul, sub_zero]
  field_simp [show aeval x f.denominator ≠ 0 from hv]

theorem cleared_jacobian_eq (f : ι → Expression ι) (x : ι → ℝ)
    (hv : ∀ i, (f i).Valid x) (hz : ∀ i, (f i).eval x = 0) :
    PolynomialAlgebraicity.jacobian (fun i => (f i).numerator) x =
      Matrix.diagonal (fun i => aeval x (f i).denominator) * jacobian f x := by
  ext i j
  rw [Matrix.diagonal_mul]
  exact (numerator_partial_at_zero (f i) x (hv i) (hz i) j).trans
    (congrArg (fun r => aeval x (f i).denominator * r) (Expression.deriv_update (hv i) j).symm)

theorem cleared_jacobian_nonsingular (f : ι → Expression ι) (x : ι → ℝ)
    (hv : ∀ i, (f i).Valid x) (hz : ∀ i, (f i).eval x = 0)
    (hJ : (jacobian f x).det ≠ 0) :
    (PolynomialAlgebraicity.jacobian (fun i => (f i).numerator) x).det ≠ 0 := by
  rw [cleared_jacobian_eq f x hv hz, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)) hJ

theorem algebraic_coordinates (f : ι → Expression ι) (x : ι → ℝ)
    (hv : ∀ i, (f i).Valid x) (hz : ∀ i, (f i).eval x = 0)
    (hJ : (jacobian f x).det ≠ 0) : ∀ i, IsAlgebraic ℚ (x i) := by
  let : Algebra.IsAlgebraic ℚ Coeff := algebraicClosure.isAlgebraic ℚ ℝ
  exact PolynomialAlgebraicity.isAlgebraic_over_base_of_nonsingular_zero
    (fun i => (f i).numerator) x (fun i => (Expression.eval_eq_zero_iff (hv i)).1 (hz i))
    (cleared_jacobian_nonsingular f x hv hz hJ)

omit [Fintype ι] [DecidableEq ι] in
theorem algebraic_aeval (p : MvPolynomial ι Coeff) (x : ι → ℝ)
    (hx : ∀ i, IsAlgebraic ℚ (x i)) : IsAlgebraic ℚ (aeval x p) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa using (mem_algebraicClosure_iff.mp c.property : IsAlgebraic ℚ (c : ℝ))
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hx i)

omit [Fintype ι] [DecidableEq ι] in
theorem algebraic_eval (f : Expression ι) (x : ι → ℝ)
    (hx : ∀ i, IsAlgebraic ℚ (x i)) : IsAlgebraic ℚ (f.eval x) := by
  rw [Expression.eval, div_eq_mul_inv]
  exact (algebraic_aeval f.numerator x hx).mul (IsAlgebraic.inv_iff.mpr (algebraic_aeval f.denominator x hx))

theorem algebraic_prod {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, IsAlgebraic ℚ (f a)) : IsAlgebraic ℚ (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isAlgebraic_one : IsAlgebraic ℚ (1 : ℝ))
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hf a (by simp)).mul (ih (fun b hb => hf b (by simp [hb])))

open RationalStationarySystem RationalConfigurationPolynomials

/-- This is the remaining interface to geometric nondegeneracy: the system and
its algebraic coefficients have already been constructed explicitly. -/
theorem stationary_coordinates_algebraic {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (hc : CollisionFree hm σ (coordinates Y))
    (hs : Stationary hm σ Y) (hJ : (jacobian (systemExpression hm σ) Y).det ≠ 0) :
    ∀ i, IsAlgebraic ℚ (Y i) := by
  have hv (i : Variables m) : (systemExpression hm σ i).Valid Y := by
    cases i with
    | inl i => exact residual_valid hm σ Y hc i
    | inr k => exact Expression.valid_rename _ _ (closureCoordinate_valid hm σ k _)
  have hz := (polynomial_system_iff hm σ Y hc).2 hs
  exact algebraic_coordinates _ Y hv (fun i => (Expression.eval_eq_zero_iff (hv i)).2 (hz i)) hJ

theorem configuration_coordinates_algebraic {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (hX : ∀ i, IsAlgebraic ℚ (X i)) (j : Fin (2 * m)) :
    IsAlgebraic ℚ (RationalConfiguration.configuration hm (sign σ) X j).re ∧
      IsAlgebraic ℚ (RationalConfiguration.configuration hm (sign σ) X j).im := by
  rw [← configuration_eval hm σ j X]
  exact ⟨algebraic_eval _ _ hX, algebraic_eval _ _ hX⟩

theorem distance_algebraic {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (hX : ∀ i, IsAlgebraic ℚ (X i)) (i j : Fin (2 * m)) :
    IsAlgebraic ℚ ‖RationalConfiguration.configuration hm (sign σ) X i -
      RationalConfiguration.configuration hm (sign σ) X j‖ := by
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  rw [← Complex.normSq_eq_norm_sq, ← squaredDistance_eval hm σ i j X]
  exact algebraic_eval _ _ hX

theorem discriminant_algebraic {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (hX : ∀ i, IsAlgebraic ℚ (X i)) :
    IsAlgebraic ℚ (Erdos1045.Configuration.discriminant
      (RationalConfiguration.configuration hm (sign σ) X)) := by
  unfold Erdos1045.Configuration.discriminant
  apply algebraic_prod
  intro i _
  apply algebraic_prod
  intro j _
  exact distance_algebraic hm σ X hX i j

end
end StructuralNote.RationalSystemAlgebraicity
