import StructuralNote.RationalConfigurationPolynomials
import StructuralNote.RationalExpressionDerivatives
import Erdos1045.LocalConfiguration

/-! The explicit square polynomial system of (10.5), in the base-edge gauge.
Its zeros on the collision-free domain are exactly the two closure equations
and the actual logarithmic distance-product stationarity equations. -/

namespace StructuralNote.RationalStationarySystem

open RationalExpressions RationalConfigurationPolynomials
open scoped BigOperators Topology
noncomputable section

abbrev Variables (m : ℕ) := Vars m ⊕ Fin 2

def coordinates {m : ℕ} (Y : Variables m → ℝ) : Vars m → ℝ := Y ∘ Sum.inl
def multiplier {m : ℕ} (Y : Variables m → ℝ) (k : Fin 2) : ℝ := Y (.inr k)

def pairs (m : ℕ) : Finset (Fin (2 * m) × Fin (2 * m)) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2)

def closureCoordinate {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (k : Fin 2) : RExpr m :=
  if k.val = 0 then (closure hm σ).re else (closure hm σ).im

def objective {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) : ℝ :=
  (∑ p ∈ pairs m, Real.log ((squaredDistance hm σ p.1 p.2).eval X)) / 2

def gradient {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (i : Vars m) : RExpr m :=
  Expression.sum (pairs m) (fun p =>
    Expression.coordinateDerivative i (squaredDistance hm σ p.1 p.2) /
      squaredDistance hm σ p.1 p.2) / Expression.constant 2

def residual {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (i : Vars m) : Expression (Variables m) :=
  (gradient hm σ i).rename Sum.inl -
    Expression.sum Finset.univ (fun k : Fin 2 => Expression.var (.inr k) *
      (Expression.coordinateDerivative i (closureCoordinate hm σ k)).rename Sum.inl)

def systemExpression {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) : Variables m → Expression (Variables m)
  | .inl i => residual hm σ i
  | .inr k => (closureCoordinate hm σ k).rename Sum.inl

def polynomials {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) : Variables m → MvPolynomial (Variables m) Coeff :=
  fun i => (systemExpression hm σ i).numerator

def CollisionFree {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) : Prop :=
  Function.Injective (RationalConfiguration.configuration hm (sign σ) X)

def Stationary {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (Y : Variables m → ℝ) : Prop :=
  RationalConfiguration.closure hm (sign σ) (coordinates Y) = 0 ∧
    ∀ i, deriv (fun t => objective hm σ (Function.update (coordinates Y) i t)) (coordinates Y i) =
      ∑ k : Fin 2, multiplier Y k * deriv (fun t =>
        (closureCoordinate hm σ k).eval (Function.update (coordinates Y) i t)) (coordinates Y i)

theorem variables_card {m : ℕ} (hm : 0 < m) : Fintype.card (Variables m) = 2 * m + 1 := by
  simp only [Variables, Fintype.card_sum, RationalConfiguration.variables_card hm, Fintype.card_fin]
  omega

theorem closureCoordinate_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (k : Fin 2) (X : Vars m → ℝ) :
    (closureCoordinate hm σ k).Valid X := by
  unfold closureCoordinate
  split
  · exact (closure_valid hm σ X).1
  · exact (closure_valid hm σ X).2

theorem closureReal_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) :
    (closureCoordinate hm σ 0).eval X = (RationalConfiguration.closure hm (sign σ) X).re :=
  congrArg Complex.re (closure_eval hm σ X)

theorem closureImag_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) :
    (closureCoordinate hm σ 1).eval X = (RationalConfiguration.closure hm (sign σ) X).im :=
  congrArg Complex.im (closure_eval hm σ X)

theorem squaredDistance_ne_zero {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) {p : Fin (2 * m) × Fin (2 * m)} (hp : p ∈ pairs m) :
    (squaredDistance hm σ p.1 p.2).eval X ≠ 0 := by
  rw [squaredDistance_eval, Complex.normSq_eq_norm_sq]
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hX.ne (Finset.mem_filter.mp hp).2)))

theorem objective_eq_log_discriminant {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) : objective hm σ X =
      Real.log (Erdos1045.Configuration.discriminant (RationalConfiguration.configuration hm (sign σ) X)) := by
  rw [Erdos1045.LocalConfiguration.logDiscriminant_eq_sum _ hX]
  unfold objective
  simp only [squaredDistance_eval]
  have hs : (∑ p ∈ pairs m, Real.log (Complex.normSq
      (RationalConfiguration.configuration hm (sign σ) X p.1 -
        RationalConfiguration.configuration hm (sign σ) X p.2))) =
      ∑ i, ∑ j, Real.log (Complex.normSq
        (RationalConfiguration.configuration hm (sign σ) X i -
          RationalConfiguration.configuration hm (sign σ) X j)) := by
    rw [pairs, Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i = j <;> simp [hij]
  rw [hs]
  simp only [Complex.normSq_eq_norm_sq, Real.log_pow, Nat.cast_ofNat,
    ← Finset.mul_sum]
  ring

theorem gradient_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) : (gradient hm σ i).Valid X := by
  apply Expression.Valid.div
  · apply Expression.valid_sum
    intro p hp
    have hv := squaredDistance_valid hm σ p.1 p.2 X
    exact (Expression.valid_coordinateDerivative hv i).div hv (squaredDistance_ne_zero hm σ X hX hp)
  · exact Expression.valid_constant _ _
  · rw [Expression.eval_constant]
    exact_mod_cast (show (2 : ℝ) ≠ 0 by norm_num)

theorem gradient_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    (gradient hm σ i).eval X = (∑ p ∈ pairs m,
      (Expression.coordinateDerivative i (squaredDistance hm σ p.1 p.2)).eval X /
        (squaredDistance hm σ p.1 p.2).eval X) / 2 := by
  rw [gradient, Expression.eval_div, Expression.eval_sum]
  · simp only [Expression.eval_div, Expression.eval_constant]
    rfl
  · intro p hp
    have hv := squaredDistance_valid hm σ p.1 p.2 X
    exact (Expression.valid_coordinateDerivative hv i).div hv (squaredDistance_ne_zero hm σ X hX hp)

theorem objective_hasDerivAt {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    HasDerivAt (fun t => objective hm σ (Function.update X i t)) ((gradient hm σ i).eval X) (X i) := by
  rw [gradient_eval hm σ X hX i]
  apply HasDerivAt.div_const
  apply HasDerivAt.fun_sum
  intro p hp
  simpa only [Expression.eval_div] using Expression.hasDerivAt_log_update
    (squaredDistance_valid hm σ p.1 p.2 X) (squaredDistance_ne_zero hm σ X hX hp) i

theorem objective_deriv {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    deriv (fun t => objective hm σ (Function.update X i t)) (X i) = (gradient hm σ i).eval X :=
  (objective_hasDerivAt hm σ X hX i).deriv

theorem collisionFree_eventually_update {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    ∀ᶠ t in 𝓝 (X i), CollisionFree hm σ (Function.update X i t) := by
  have he : ∀ p ∈ pairs m, ∀ᶠ t in 𝓝 (X i),
      (squaredDistance hm σ p.1 p.2).eval (Function.update X i t) ≠ 0 := by
    intro p hp
    apply (Expression.hasDerivAt_update (squaredDistance_valid hm σ p.1 p.2 X) i).continuousAt.eventually_ne
    simpa only [Function.update_eq_self] using squaredDistance_ne_zero hm σ X hX hp
  filter_upwards [(Filter.eventually_all_finset (pairs m)).2 he] with t ht
  intro a b hab
  by_contra hn
  have h := ht (a, b) (by simp [pairs, hn])
  rw [squaredDistance_eval, hab, sub_self, map_zero] at h
  exact h rfl

theorem log_discriminant_hasDerivAt {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    HasDerivAt (fun t => Real.log (Erdos1045.Configuration.discriminant
      (RationalConfiguration.configuration hm (sign σ) (Function.update X i t))))
      ((gradient hm σ i).eval X) (X i) := by
  apply (objective_hasDerivAt hm σ X hX i).congr_of_eventuallyEq
  filter_upwards [collisionFree_eventually_update hm σ X hX i] with t ht
  exact (objective_eq_log_discriminant hm σ _ ht).symm

theorem residual_valid {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (Y : Variables m → ℝ)
    (hY : CollisionFree hm σ (coordinates Y)) (i : Vars m) : (residual hm σ i).Valid Y := by
  apply Expression.Valid.sub
  · exact Expression.valid_rename _ _ (gradient_valid hm σ (coordinates Y) hY i)
  · apply Expression.valid_sum
    intro k _
    exact (Expression.valid_variable _ _).mul (Expression.valid_rename _ _
      (Expression.valid_coordinateDerivative (closureCoordinate_valid hm σ k (coordinates Y)) i))

theorem residual_eval {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (Y : Variables m → ℝ)
    (hY : CollisionFree hm σ (coordinates Y)) (i : Vars m) :
    (residual hm σ i).eval Y =
      deriv (fun t => objective hm σ (Function.update (coordinates Y) i t)) (coordinates Y i) -
      ∑ k : Fin 2, multiplier Y k * deriv (fun t =>
        (closureCoordinate hm σ k).eval (Function.update (coordinates Y) i t)) (coordinates Y i) := by
  have hv : ∀ k ∈ (Finset.univ : Finset (Fin 2)),
      (Expression.var (Sum.inr k) *
        (Expression.coordinateDerivative i (closureCoordinate hm σ k)).rename Sum.inl).Valid Y := by
    intro k _
    exact (Expression.valid_variable _ _).mul (Expression.valid_rename _ _
      (Expression.valid_coordinateDerivative (closureCoordinate_valid hm σ k (coordinates Y)) i))
  rw [residual, Expression.eval_sub
    (Expression.valid_rename _ _ (gradient_valid hm σ (coordinates Y) hY i))
    (Expression.valid_sum _ _ _ hv), Expression.eval_sum _ _ _ hv]
  rw [objective_deriv hm σ (coordinates Y) hY i]
  simp only [Expression.eval_rename, Expression.eval_mul, Expression.eval_variable,
    coordinates, multiplier, Expression.deriv_update (closureCoordinate_valid hm σ _ _) i]

theorem closure_equations_iff {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (X : Vars m → ℝ) :
    (∀ k, (closureCoordinate hm σ k).eval X = 0) ↔ RationalConfiguration.closure hm (sign σ) X = 0 := by
  rw [← closure_eval hm σ X, Complex.ext_iff]
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · intro h k
    fin_cases k
    · exact h.1
    · exact h.2

theorem polynomial_system_iff {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (Y : Variables m → ℝ)
    (hY : CollisionFree hm σ (coordinates Y)) :
    (∀ i, MvPolynomial.aeval Y (polynomials hm σ i) = 0) ↔ Stationary hm σ Y := by
  have hv (i : Variables m) : (systemExpression hm σ i).Valid Y := by
    cases i with
    | inl i => exact residual_valid hm σ Y hY i
    | inr k => exact Expression.valid_rename _ _ (closureCoordinate_valid hm σ k _)
  have he : (∀ i, MvPolynomial.aeval Y (polynomials hm σ i) = 0) ↔
      ∀ i, (systemExpression hm σ i).eval Y = 0 :=
    forall_congr' (fun i => (Expression.eval_eq_zero_iff (hv i)).symm)
  rw [he]
  constructor
  · intro h
    refine ⟨(closure_equations_iff hm σ _).1 ?_, ?_⟩
    · intro k
      simpa only [systemExpression, Expression.eval_rename, coordinates] using h (.inr k)
    · intro i
      exact sub_eq_zero.mp ((residual_eval hm σ Y hY i).symm.trans (h (.inl i)))
  · rintro ⟨hc, hd⟩ i
    cases i with
    | inl i => exact (residual_eval hm σ Y hY i).trans (sub_eq_zero.mpr (hd i))
    | inr k =>
      exact (Expression.eval_rename _ _ _).trans ((closure_equations_iff hm σ _).2 hc k)

/-- Equation (10.5) uses the actual log distance product and actual real/imaginary
closure derivatives; the rational-expression implementation adds no hypotheses. -/
theorem stationary_iff_log_discriminant {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool) (Y : Variables m → ℝ)
    (hY : CollisionFree hm σ (coordinates Y)) : Stationary hm σ Y ↔
      RationalConfiguration.closure hm (sign σ) (coordinates Y) = 0 ∧
      ∀ i, deriv (fun t => Real.log (Erdos1045.Configuration.discriminant
        (RationalConfiguration.configuration hm (sign σ) (Function.update (coordinates Y) i t))))
        (coordinates Y i) =
        multiplier Y 0 * deriv (fun t => (RationalConfiguration.closure hm (sign σ)
          (Function.update (coordinates Y) i t)).re) (coordinates Y i) +
        multiplier Y 1 * deriv (fun t => (RationalConfiguration.closure hm (sign σ)
          (Function.update (coordinates Y) i t)).im) (coordinates Y i) := by
  unfold Stationary
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  rw [objective_deriv hm σ _ hY i, (log_discriminant_hasDerivAt hm σ _ hY i).deriv]
  simp only [Fin.sum_univ_two, closureReal_eval, closureImag_eval]

end
end StructuralNote.RationalStationarySystem
