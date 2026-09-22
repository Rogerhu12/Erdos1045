import Erdos1045.MatrixHadamard
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open scoped BigOperators

namespace Erdos1045.MatrixDefect

noncomputable section

theorem norm_det_le_product_column_norm {n : ℕ} (F : Mat n) :
    ‖F.det‖ ≤ ∏ j : Fin n, ‖(WithLp.toLp 2 (fun i : Fin n => F i j) : EuclideanSpace ℂ (Fin n))‖ := by
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun j => WithLp.toLp 2 (fun i => F i j)
  let e := EuclideanSpace.basisFun (Fin n) ℂ
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis hdim f
  have hdet : e.toBasis.det f = F.det := by
    change (e.toBasis.toMatrix f).det = F.det
    congr 1
  have hchange : e.toBasis.det f = e.toBasis.det b * b.toBasis.det f := by
    have h := congrArg (fun g => g f) (e.toBasis.det.eq_smul_basis_det b.toBasis)
    exact h
  have hnorm : ‖F.det‖ = ‖b.toBasis.det f‖ := by
    rw [← hdet, hchange, norm_mul, e.det_to_matrix_orthonormalBasis b, one_mul]
  rw [hnorm]
  change ‖(InnerProductSpace.gramSchmidtOrthonormalBasis hdim f).toBasis.det f‖ ≤ _
  rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  have h := @norm_inner_le_norm ℂ _ _ _ _ (b j) (f j)
  simpa only [b.norm_eq_one j, one_mul] using h

theorem detSq_le_product_column_energy {n : ℕ} (F : Mat n) :
    detSq F ≤ ∏ j, ∑ i, Complex.normSq (F i j) := by
  have h := norm_det_le_product_column_norm F
  have hs := pow_le_pow_left₀ (norm_nonneg F.det) h 2
  rw [← Finset.prod_pow] at hs
  unfold detSq
  rw [Complex.normSq_eq_norm_sq]
  apply hs.trans_eq
  apply Finset.prod_congr rfl
  intro j hj
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.normSq_eq_norm_sq]

/-- Hadamard is derived from orthonormal Gram--Schmidt and Cauchy--Schwarz. -/
theorem classicalMatrixHadamard : ClassicalMatrixHadamard :=
  ⟨detSq_le_product_column_energy⟩

end
end Erdos1045.MatrixDefect
