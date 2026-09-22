import StructuralNote.FixedSchurRationalClosureMatrix
import StructuralNote.RationalSystemAlgebraicity

/-! Exact block form of the Jacobian of the actual rational stationary system. -/

namespace StructuralNote.RationalBorderedJacobian

open Filter Matrix RationalExpressions RationalConfigurationPolynomials
open RationalStationarySystem RationalSystemAlgebraicity FixedSchurRationalClosureMatrix
open scoped BigOperators Topology

noncomputable section

theorem coordinates_update_inl {m : ℕ} (Y : Variables m → ℝ) (i : Vars m) (t : ℝ) :
    coordinates (Function.update Y (.inl i) t) = Function.update (coordinates Y) i t := by
  funext j
  by_cases hj : j = i <;> simp [coordinates, Function.update_apply, hj]

theorem multiplier_update_inl {m : ℕ} (Y : Variables m → ℝ) (i : Vars m) (t : ℝ) :
    multiplier (Function.update Y (.inl i) t) = multiplier Y := by
  funext k
  simp [multiplier]

theorem coordinates_update_inr {m : ℕ} (Y : Variables m → ℝ) (k : Fin 2) (t : ℝ) :
    coordinates (Function.update Y (.inr k) t) = coordinates Y := by
  funext i
  simp [coordinates]

theorem multiplier_update_inr {m : ℕ} (Y : Variables m → ℝ) (k : Fin 2) (t : ℝ) :
    multiplier (Function.update Y (.inr k) t) = Function.update (multiplier Y) k t := by
  funext l
  by_cases hl : l = k <;> simp [multiplier, hl]

def lagrangianGradient {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (μ : Fin 2 → ℝ) (i : Vars m) : ℝ :=
  deriv (fun t => objective hm σ (Function.update X i t)) (X i) -
    ∑ k, μ k * closureMatrix hm σ X k i

def lagrangianHessian {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (X : Vars m → ℝ) (μ : Fin 2 → ℝ) : Matrix (Vars m) (Vars m) ℝ :=
  fun i j => deriv (fun t => lagrangianGradient hm σ (Function.update X j t) μ i) (X j)

theorem residual_eq_lagrangianGradient {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (hY : CollisionFree hm σ (coordinates Y)) (i : Vars m) :
    (residual hm σ i).eval Y = lagrangianGradient hm σ (coordinates Y) (multiplier Y) i :=
  residual_eval hm σ Y hY i

theorem lagrangianGradient_multiplier_hasDerivAt {m : ℕ} (hm : 0 < m)
    (σ : Fin m → Bool) (X : Vars m → ℝ) (μ : Fin 2 → ℝ) (i : Vars m) (k : Fin 2) :
    HasDerivAt (fun t => lagrangianGradient hm σ X (Function.update μ k t) i)
      (-closureMatrix hm σ X k i) (μ k) := by
  have hd (l : Fin 2) := ((hasDerivAt_pi.mp (hasDerivAt_update μ k (μ k))) l).mul_const
    (closureMatrix hm σ X l i)
  have hs := (HasDerivAt.fun_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin 2))) => hd l)).const_sub
    (deriv (fun t => objective hm σ (Function.update X i t)) (X i))
  simpa only [lagrangianGradient, Pi.single_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, neg_mul] using hs

theorem jacobian_inl_inl {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (hY : CollisionFree hm σ (coordinates Y)) (i j : Vars m) :
    jacobian (systemExpression hm σ) Y (.inl i) (.inl j) =
      lagrangianHessian hm σ (coordinates Y) (multiplier Y) i j := by
  have he : (fun t => (residual hm σ i).eval (Function.update Y (.inl j) t)) =ᶠ[𝓝 (Y (.inl j))]
      (fun t => lagrangianGradient hm σ (Function.update (coordinates Y) j t) (multiplier Y) i) := by
    filter_upwards [collisionFree_eventually_update hm σ (coordinates Y) hY j] with t ht
    have hc : CollisionFree hm σ (coordinates (Function.update Y (.inl j) t)) := by
      rwa [coordinates_update_inl]
    rw [residual_eq_lagrangianGradient hm σ _ hc, coordinates_update_inl, multiplier_update_inl]
  exact he.deriv_eq

theorem jacobian_inl_inr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (hY : CollisionFree hm σ (coordinates Y)) (i : Vars m) (k : Fin 2) :
    jacobian (systemExpression hm σ) Y (.inl i) (.inr k) = -closureMatrix hm σ (coordinates Y) k i := by
  have he : (fun t => (residual hm σ i).eval (Function.update Y (.inr k) t)) =
      (fun t => lagrangianGradient hm σ (coordinates Y) (Function.update (multiplier Y) k t) i) := by
    funext t
    have hc : CollisionFree hm σ (coordinates (Function.update Y (.inr k) t)) := by
      rwa [coordinates_update_inr]
    rw [residual_eq_lagrangianGradient hm σ _ hc, coordinates_update_inr, multiplier_update_inr]
  change deriv (fun t => (residual hm σ i).eval (Function.update Y (.inr k) t)) (Y (.inr k)) = _
  rw [he]
  exact (lagrangianGradient_multiplier_hasDerivAt hm σ (coordinates Y) (multiplier Y) i k).deriv

theorem jacobian_inr_inl {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (k : Fin 2) (i : Vars m) :
    jacobian (systemExpression hm σ) Y (.inr k) (.inl i) = closureMatrix hm σ (coordinates Y) k i := by
  change deriv (fun t => ((closureCoordinate hm σ k).rename Sum.inl).eval
    (Function.update Y (.inl i) t)) (Y (.inl i)) = _
  simp only [Expression.eval_rename]
  change deriv (fun t => (closureCoordinate hm σ k).eval
    (coordinates (Function.update Y (.inl i) t))) (Y (.inl i)) = _
  simp only [coordinates_update_inl]
  rfl

theorem jacobian_inr_inr {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (k l : Fin 2) :
    jacobian (systemExpression hm σ) Y (.inr k) (.inr l) = 0 := by
  change deriv (fun t => ((closureCoordinate hm σ k).rename Sum.inl).eval
    (Function.update Y (.inr l) t)) (Y (.inr l)) = _
  simp only [Expression.eval_rename]
  change deriv (fun t => (closureCoordinate hm σ k).eval
    (coordinates (Function.update Y (.inr l) t))) (Y (.inr l)) = _
  simp only [coordinates_update_inr, deriv_const]

theorem jacobian_eq_bordered {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (hY : CollisionFree hm σ (coordinates Y)) :
    jacobian (systemExpression hm σ) Y =
      BorderedHessian.bordered (lagrangianHessian hm σ (coordinates Y) (multiplier Y))
        (closureMatrix hm σ (coordinates Y)) := by
  ext i j
  cases i <;> cases j
  · exact jacobian_inl_inl hm σ Y hY _ _
  · exact jacobian_inl_inr hm σ Y hY _ _
  · exact jacobian_inr_inl hm σ Y _ _
  · exact jacobian_inr_inr hm σ Y _ _

theorem stationary_jacobian_nonsingular {m : ℕ} (hm : 0 < m) (σ : Fin m → Bool)
    (Y : Variables m → ℝ) (hY : CollisionFree hm σ (coordinates Y))
    (hB : Function.Surjective (closureMatrix hm σ (coordinates Y)).mulVec)
    (hQ : ∀ v : Vars m → ℝ, closureMatrix hm σ (coordinates Y) *ᵥ v = 0 → v ≠ 0 →
      v ⬝ᵥ (lagrangianHessian hm σ (coordinates Y) (multiplier Y) *ᵥ v) < 0) :
    (jacobian (systemExpression hm σ) Y).det ≠ 0 := by
  rw [jacobian_eq_bordered hm σ Y hY]
  exact BorderedHessian.bordered_det_ne_zero_of_full_row_rank _ _ hB hQ

end
end StructuralNote.RationalBorderedJacobian
