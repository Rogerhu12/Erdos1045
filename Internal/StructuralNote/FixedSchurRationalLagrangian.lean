import StructuralNote.FixedSchurRationalClosurePaths
import StructuralNote.RationalBorderedJacobian
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Differential interpretation of the actual rational Lagrangian matrix. -/

namespace StructuralNote.FixedSchurRationalLagrangian

open Filter Matrix RationalExpressions RationalConfigurationPolynomials
open RationalStationarySystem RationalBorderedJacobian
open FixedSchurRationalClosureMatrix
open scoped BigOperators Topology ContDiff

noncomputable section

private theorem aeval_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial ι Coeff) :
    ContDiff ℝ ∞ (fun x : ι → ℝ => MvPolynomial.aeval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using (contDiff_const : ContDiff ℝ ∞
      (fun _ : ι → ℝ => (a : ℝ)))
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
      simp only [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (by fun_prop)

theorem expression_eval_contDiffAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : Expression ι) (x : ι → ℝ) (hx : e.Valid x) :
    ContDiffAt ℝ ∞ e.eval x := by
  unfold Expression.eval Expression.Valid at *
  exact (aeval_contDiff e.numerator).contDiffAt.div
    (aeval_contDiff e.denominator).contDiffAt hx

/-- The actual logarithmic rational objective is smooth at every
collision-free rational configuration. -/
theorem objective_contDiffAt {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (hX : CollisionFree hm σ X) :
    ContDiffAt ℝ ∞ (objective hm σ) X := by
  unfold objective
  apply ContDiffAt.div_const
  apply ContDiffAt.sum
  intro p hp
  exact (expression_eval_contDiffAt (squaredDistance hm σ p.1 p.2) X
    (squaredDistance_valid hm σ p.1 p.2 X)).log
      (squaredDistance_ne_zero hm σ X hX hp)

def lagrangianValue {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (μ : Fin 2 → ℝ) (X : Vars m → ℝ) : ℝ :=
  objective hm σ X - ∑ k, μ k * (closureCoordinate hm σ k).eval X

theorem lagrangianValue_contDiffAt {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (μ : Fin 2 → ℝ) (X : Vars m → ℝ) (hX : CollisionFree hm σ X) :
    ContDiffAt ℝ ∞ (lagrangianValue hm σ μ) X := by
  unfold lagrangianValue
  apply (objective_contDiffAt hm σ X hX).sub
  apply ContDiffAt.sum
  intro k _
  exact contDiffAt_const.mul (expression_eval_contDiffAt (closureCoordinate hm σ k) X
    (closureCoordinate_valid hm σ k X))

theorem fderiv_apply_eq_sum_coordinate_deriv {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : (ι → ℝ) → ℝ) (x u : ι → ℝ)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x u =
      ∑ i, deriv (fun t => f (Function.update x i t)) (x i) * u i := by
  rw [FixedSchurRationalClosureMatrix.linear_eq_sum_basis (fderiv ℝ f x) u]
  apply Finset.sum_congr rfl
  intro i _
  have hu := hasDerivAt_update x i (x i)
  have houter : HasFDerivAt f (fderiv ℝ f x) (Function.update x i (x i)) := by
    simpa only [Function.update_eq_self] using hf.hasFDerivAt
  have hc := houter.comp_hasDerivAt (x i) hu
  have hcd : deriv (fun t => f (Function.update x i t)) (x i) =
      (fderiv ℝ f x) (Pi.single i 1) := by
    rw [show (fun t => f (Function.update x i t)) = f ∘ Function.update x i by rfl]
    exact hc.deriv
  rw [hcd]

theorem lagrangianValue_coordinate_deriv {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    deriv (fun t => lagrangianValue hm σ μ (Function.update X i t)) (X i) =
      lagrangianGradient hm σ X μ i := by
  unfold lagrangianValue lagrangianGradient
  have ho := objective_hasDerivAt hm σ X hX i
  have hc (k : Fin 2) := Expression.hasDerivAt_update
    (closureCoordinate_valid hm σ k X) i
  have hs := HasDerivAt.fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 2))) =>
    (hc k).const_mul (μ k))
  have h := ho.sub hs
  calc
    deriv (fun t => lagrangianValue hm σ μ (Function.update X i t)) (X i) =
        (gradient hm σ i).eval X -
          ∑ k, μ k * (Expression.coordinateDerivative i
            (closureCoordinate hm σ k)).eval X := by
      have he : (fun t => lagrangianValue hm σ μ (Function.update X i t)) =
          (fun t => objective hm σ (Function.update X i t)) -
            (fun t => ∑ k, μ k * (closureCoordinate hm σ k).eval
              (Function.update X i t)) := by
        funext t
        rfl
      rw [he]
      exact h.deriv
    _ = lagrangianGradient hm σ X μ i := by
      unfold lagrangianGradient closureMatrix
      rw [objective_deriv hm σ X hX i]
      simp_rw [Expression.deriv_update (closureCoordinate_valid hm σ _ X) i]

theorem stationary_lagrangianGradient_zero {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (Y : Variables m → ℝ) (hY : Stationary hm σ Y)
    (i : Vars m) :
    lagrangianGradient hm σ (coordinates Y) (multiplier Y) i = 0 := by
  unfold lagrangianGradient
  rw [hY.2 i]
  simp only [closureMatrix]
  ring

/-- A solution of the actual rational stationary system is an ambient
critical point of its Lagrangian. -/
theorem stationary_lagrangian_fderiv_zero {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (Y : Variables m → ℝ)
    (hfree : CollisionFree hm σ (coordinates Y)) (hY : Stationary hm σ Y) :
    fderiv ℝ (lagrangianValue hm σ (multiplier Y)) (coordinates Y) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  change (fderiv ℝ (lagrangianValue hm σ (multiplier Y)) (coordinates Y)) u = 0
  rw [fderiv_apply_eq_sum_coordinate_deriv _ _ _
    ((lagrangianValue_contDiffAt hm σ (multiplier Y) (coordinates Y) hfree).differentiableAt
      (by simp : (∞ : ℕ∞ω) ≠ 0))]
  simp only [lagrangianValue_coordinate_deriv hm σ (multiplier Y) (coordinates Y) hfree,
    stationary_lagrangianGradient_zero hm σ Y hY, zero_mul, Finset.sum_const_zero]

theorem collisionFree_eventually {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (hX : CollisionFree hm σ X) :
    ∀ᶠ Z in nhds X, CollisionFree hm σ Z := by
  have he : ∀ p ∈ pairs m, ∀ᶠ Z in nhds X,
      (squaredDistance hm σ p.1 p.2).eval Z ≠ 0 := by
    intro p hp
    exact (expression_eval_contDiffAt (squaredDistance hm σ p.1 p.2) X
      (squaredDistance_valid hm σ p.1 p.2 X)).continuousAt.eventually_ne
        (squaredDistance_ne_zero hm σ X hX hp)
  filter_upwards [(Filter.eventually_all_finset (pairs m)).2 he] with Z hZ
  intro a b hab
  by_contra hn
  have hz := hZ (a, b) (by simp [pairs, hn])
  rw [squaredDistance_eval, hab, sub_self, map_zero] at hz
  exact hz rfl

def algebraicLagrangianGradient {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (μ : Fin 2 → ℝ) (i : Vars m) (X : Vars m → ℝ) : ℝ :=
  (gradient hm σ i).eval X -
    ∑ k, μ k * (Expression.coordinateDerivative i (closureCoordinate hm σ k)).eval X

theorem lagrangianGradient_eq_algebraic {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    lagrangianGradient hm σ X μ i = algebraicLagrangianGradient hm σ μ i X := by
  unfold lagrangianGradient algebraicLagrangianGradient closureMatrix
  rw [objective_deriv hm σ X hX i]
  simp_rw [Expression.deriv_update (closureCoordinate_valid hm σ _ X) i]

theorem algebraicLagrangianGradient_contDiffAt {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    ContDiffAt ℝ ∞ (algebraicLagrangianGradient hm σ μ i) X := by
  unfold algebraicLagrangianGradient
  apply (expression_eval_contDiffAt (gradient hm σ i) X
    (gradient_valid hm σ X hX i)).sub
  apply ContDiffAt.sum
  intro k _
  exact contDiffAt_const.mul (expression_eval_contDiffAt
    (Expression.coordinateDerivative i (closureCoordinate hm σ k)) X
    (Expression.valid_coordinateDerivative (closureCoordinate_valid hm σ k X) i))

theorem lagrangianGradient_differentiableAt {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ) (X : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    DifferentiableAt ℝ (fun Z => lagrangianGradient hm σ Z μ i) X := by
  have he : (fun Z => lagrangianGradient hm σ Z μ i) =ᶠ[nhds X]
      algebraicLagrangianGradient hm σ μ i := by
    filter_upwards [collisionFree_eventually hm σ X hX] with Z hZ
    exact lagrangianGradient_eq_algebraic hm σ μ Z hZ i
  exact (algebraicLagrangianGradient_contDiffAt hm σ μ X hX i).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0) |>.congr_of_eventuallyEq he

theorem lagrangianGradient_fderiv_apply {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ) (X u : Vars m → ℝ)
    (hX : CollisionFree hm σ X) (i : Vars m) :
    fderiv ℝ (fun Z => lagrangianGradient hm σ Z μ i) X u =
      ∑ j, lagrangianHessian hm σ X μ i j * u j := by
  rw [fderiv_apply_eq_sum_coordinate_deriv _ X u
    (lagrangianGradient_differentiableAt hm σ μ X hX i)]
  rfl

def affineVariables {m : ℕ} (X u : Vars m → ℝ) (t : ℝ) : Vars m → ℝ :=
  X + t • u

theorem lagrangian_affine_deriv {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ) (X u : Vars m → ℝ) (t : ℝ)
    (hfree : CollisionFree hm σ (affineVariables X u t)) :
    deriv (fun r => lagrangianValue hm σ μ (affineVariables X u r)) t =
      ∑ i, lagrangianGradient hm σ (affineVariables X u t) μ i * u i := by
  have houter := (lagrangianValue_contDiffAt hm σ μ (affineVariables X u t) hfree).differentiableAt
    (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hc := houter.hasFDerivAt.comp_hasDerivAt t
    (((hasDerivAt_id t).smul_const u).const_add X)
  simp only [one_smul] at hc
  rw [show (fun r => lagrangianValue hm σ μ (affineVariables X u r)) =
      lagrangianValue hm σ μ ∘ affineVariables X u by rfl,
    hc.deriv, fderiv_apply_eq_sum_coordinate_deriv _ _ _ houter]
  simp_rw [lagrangianValue_coordinate_deriv hm σ μ _ hfree]

/-- The matrix called `lagrangianHessian` in the rational stationary system
is exactly the genuine affine second derivative of the actual Lagrangian. -/
theorem lagrangianHessian_quadratic_eq_second {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (μ : Fin 2 → ℝ) (X u : Vars m → ℝ)
    (hX : CollisionFree hm σ X) :
    u ⬝ᵥ (lagrangianHessian hm σ X μ *ᵥ u) =
      deriv (deriv (fun t => lagrangianValue hm σ μ (affineVariables X u t))) 0 := by
  have hline' : Tendsto (affineVariables X u) (nhds 0) (nhds X) := by
    apply tendsto_pi_nhds.2
    intro i
    change Tendsto (fun t : ℝ => X i + t * u i) (nhds 0) (nhds (X i))
    have hx : Tendsto (fun _ : ℝ => X i) (nhds 0) (nhds (X i)) := tendsto_const_nhds
    have ht : Tendsto (fun t : ℝ => t) (nhds 0) (nhds 0) := tendsto_id
    have hu : Tendsto (fun _ : ℝ => u i) (nhds 0) (nhds (u i)) := tendsto_const_nhds
    simpa using hx.add (ht.mul hu)
  have hfree : ∀ᶠ t in nhds (0 : ℝ), CollisionFree hm σ (affineVariables X u t) :=
    hline'.eventually (collisionFree_eventually hm σ X hX)
  have hfirst : deriv (fun t => lagrangianValue hm σ μ (affineVariables X u t)) =ᶠ[nhds 0]
      fun t => ∑ i, lagrangianGradient hm σ (affineVariables X u t) μ i * u i := by
    filter_upwards [hfree] with t ht
    exact lagrangian_affine_deriv hm σ μ X u t ht
  have hterm (i : Vars m) : HasDerivAt
      (fun t => lagrangianGradient hm σ (affineVariables X u t) μ i * u i)
      ((∑ j, lagrangianHessian hm σ X μ i j * u j) * u i) 0 := by
    have hg := (lagrangianGradient_differentiableAt hm σ μ X hX i).hasFDerivAt
    have hg' : HasFDerivAt (fun Z => lagrangianGradient hm σ Z μ i)
        (fderiv ℝ (fun Z => lagrangianGradient hm σ Z μ i) X)
        (affineVariables X u 0) := by
      simpa only [affineVariables, zero_smul, add_zero] using hg
    have hc := hg'.comp_hasDerivAt 0
      (((hasDerivAt_id (0 : ℝ)).smul_const u).const_add X)
    simp only [one_smul] at hc
    rw [← lagrangianGradient_fderiv_apply hm σ μ X u hX i]
    simpa only [Function.comp_apply] using hc.mul_const (u i)
  have hsum := HasDerivAt.fun_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Vars m))) => hterm i)
  rw [hfirst.deriv_eq, hsum.deriv]
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

end
end StructuralNote.FixedSchurRationalLagrangian

