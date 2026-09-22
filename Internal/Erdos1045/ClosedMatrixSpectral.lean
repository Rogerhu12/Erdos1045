import Erdos1045.MatrixDefect
import Mathlib.Analysis.Matrix.Spectrum

open scoped BigOperators ComplexConjugate

namespace Erdos1045.MatrixDefect

noncomputable section

theorem trace_gram_eq_frobSq {n : ℕ} (A : Mat n) :
    (gram A).trace = (frobSq A : ℂ) := by
  unfold gram Matrix.trace frobSq
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]
  exact Finset.sum_comm

theorem sum_eigenvalue_eq_frobSq {n : ℕ} (A : Mat n) :
    (∑ i, eigenvalue A i) = frobSq A := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  calc
    (∑ i, (eigenvalue A i : ℂ)) = (gram A).trace :=
      (Matrix.isHermitian_conjTranspose_mul_self A).trace_eq_sum_eigenvalues.symm
    _ = _ := trace_gram_eq_frobSq A

theorem det_gram_eq_detSq {n : ℕ} (A : Mat n) :
    (gram A).det = (detSq A : ℂ) := by
  rw [gram, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self]
  rfl

theorem prod_eigenvalue_eq_detSq {n : ℕ} (A : Mat n) :
    (∏ i, eigenvalue A i) = detSq A := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_prod]
  calc
    (∏ i, (eigenvalue A i : ℂ)) = (gram A).det :=
      (Matrix.isHermitian_conjTranspose_mul_self A).det_eq_prod_eigenvalues.symm
    _ = _ := det_gram_eq_detSq A

theorem frobSq_unitary_conjugation {n : ℕ} (u : unitary (Mat n)) (M : Mat n) :
    frobSq (Unitary.conjStarAlgAut ℂ (Mat n) u M) = frobSq M := by
  let e := Unitary.conjStarAlgAut ℂ (Mat n) u
  have hgram : gram (e M) = e (gram M) := by
    change star (e M) * e M = e (star M * M)
    rw [map_mul, map_star]
  apply Complex.ofReal_injective
  rw [← trace_gram_eq_frobSq, ← trace_gram_eq_frobSq]
  change (gram (e M)).trace = _
  rw [hgram]
  dsimp only [e]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul]

theorem gram_deviation_eq {n : ℕ} (A : Mat n) :
    frobSq (gram A - 1) = LogDefect.deviation Finset.univ (eigenvalue A) := by
  let hA := Matrix.isHermitian_conjTranspose_mul_self A
  let e := Unitary.conjStarAlgAut ℂ (Mat n) hA.eigenvectorUnitary
  let D : Mat n := Matrix.diagonal (fun i => (eigenvalue A i : ℂ))
  have hG : gram A = e D := hA.spectral_theorem
  have hsub : gram A - 1 = e (D - 1) := by rw [map_sub, map_one, ← hG]
  rw [hsub, frobSq_unitary_conjugation]
  have hd : D - 1 = Matrix.diagonal (fun i => ((eigenvalue A i - 1 : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · simp [D, hij]
    · simp [D, hij]
  rw [hd]
  simp only [frobSq, Matrix.diagonal_apply]
  simp_rw [apply_ite Complex.normSq]
  simp only [Complex.normSq_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Complex.normSq_ofReal, LogDefect.deviation, pow_two]

/-- The entire spectral interface is now supplied without external inputs. -/
theorem classicalMatrixFacts : ClassicalMatrixFacts where
  sum_eigenvalue := sum_eigenvalue_eq_frobSq
  prod_eigenvalue := prod_eigenvalue_eq_detSq
  gram_deviation := gram_deviation_eq

end
end Erdos1045.MatrixDefect
