import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-! The linear algebra in Proposition 10.1. The analytic hypotheses on the
actual closure map and the actual fiber Hessian are not asserted here. -/

noncomputable section
open Matrix

namespace StructuralNote.BorderedHessian

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The Jacobian of the stationary equations and the closure equations. -/
def bordered (Q : Matrix ι ι ℝ) (B : Matrix κ ι ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks Q (-B.transpose) B 0

theorem transpose_injective_of_surjective (B : Matrix κ ι ℝ)
    (hB : Function.Surjective B.mulVec) : Function.Injective B.transpose.mulVec := by
  intro x y hxy
  obtain ⟨v, hv⟩ := hB (x - y)
  have ht : B.transpose *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hd : (x - y) ⬝ᵥ (x - y) = 0 := by
    calc
      (x - y) ⬝ᵥ (x - y) = (x - y) ⬝ᵥ (B *ᵥ v) := by rw [hv]
      _ = v ⬝ᵥ (B.transpose *ᵥ (x - y)) :=
        (Matrix.dotProduct_transpose_mulVec B v (x - y)).symm
      _ = 0 := by rw [ht, dotProduct_zero]
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp hd)

theorem kernel_pair_eq_zero (Q : Matrix ι ι ℝ) (B : Matrix κ ι ℝ)
    (hB : Function.Injective B.transpose.mulVec)
    (hQ : ∀ v : ι → ℝ, B *ᵥ v = 0 → v ≠ 0 → v ⬝ᵥ (Q *ᵥ v) < 0)
    (v : ι → ℝ) (η : κ → ℝ)
    (hfirst : Q *ᵥ v - B.transpose *ᵥ η = 0) (hsecond : B *ᵥ v = 0) :
    v = 0 ∧ η = 0 := by
  have hfirst' : Q *ᵥ v = B.transpose *ᵥ η := sub_eq_zero.mp hfirst
  have hdot : v ⬝ᵥ (Q *ᵥ v) = 0 := by
    rw [hfirst', Matrix.dotProduct_transpose_mulVec, hsecond, dotProduct_zero]
  have hv : v = 0 := by
    by_contra hn
    exact (ne_of_lt (hQ v hsecond hn)) hdot
  refine ⟨hv, hB ?_⟩
  simpa [hv] using hfirst'.symm

theorem bordered_kernel_eq_zero (Q : Matrix ι ι ℝ) (B : Matrix κ ι ℝ)
    (hB : Function.Injective B.transpose.mulVec)
    (hQ : ∀ v : ι → ℝ, B *ᵥ v = 0 → v ≠ 0 → v ⬝ᵥ (Q *ᵥ v) < 0)
    (x : ι ⊕ κ → ℝ) (hx : bordered Q B *ᵥ x = 0) : x = 0 := by
  have hl : Q *ᵥ (x ∘ Sum.inl) - B.transpose *ᵥ (x ∘ Sum.inr) = 0 := by
    funext i
    have hi := congrFun hx (Sum.inl i)
    simpa [bordered, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, sub_eq_add_neg] using hi
  have hr : B *ᵥ (x ∘ Sum.inl) = 0 := by
    funext i
    have hi := congrFun hx (Sum.inr i)
    simpa [bordered, Matrix.fromBlocks_mulVec] using hi
  obtain ⟨hv, hη⟩ := kernel_pair_eq_zero Q B hB hQ _ _ hl hr
  funext i
  cases i with
  | inl i => exact congrFun hv i
  | inr i => exact congrFun hη i

theorem bordered_injective (Q : Matrix ι ι ℝ) (B : Matrix κ ι ℝ)
    (hB : Function.Injective B.transpose.mulVec)
    (hQ : ∀ v : ι → ℝ, B *ᵥ v = 0 → v ≠ 0 → v ⬝ᵥ (Q *ᵥ v) < 0) :
    Function.Injective (bordered Q B).mulVec := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply bordered_kernel_eq_zero Q B hB hQ
  rw [Matrix.mulVec_sub, hxy, sub_self]

/-- This is the exact nonsingularity implication used by the manuscript.
Symmetry of Q is not needed for this implication. -/
theorem bordered_det_ne_zero [DecidableEq ι] [DecidableEq κ]
    (Q : Matrix ι ι ℝ) (B : Matrix κ ι ℝ)
    (hB : Function.Injective B.transpose.mulVec)
    (hQ : ∀ v : ι → ℝ, B *ᵥ v = 0 → v ≠ 0 → v ⬝ᵥ (Q *ᵥ v) < 0) :
    (bordered Q B).det ≠ 0 := by
  have hu := Matrix.mulVec_injective_iff_isUnit.mp (bordered_injective Q B hB hQ)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

theorem bordered_det_ne_zero_of_full_row_rank [DecidableEq ι] [DecidableEq κ]
    (Q : Matrix ι ι ℝ) (B : Matrix κ ι ℝ)
    (hB : Function.Surjective B.mulVec)
    (hQ : ∀ v : ι → ℝ, B *ᵥ v = 0 → v ≠ 0 → v ⬝ᵥ (Q *ᵥ v) < 0) :
    (bordered Q B).det ≠ 0 :=
  bordered_det_ne_zero Q B (transpose_injective_of_surjective B hB) hQ

end StructuralNote.BorderedHessian
