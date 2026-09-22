import Erdos1045.ClosedMatrixSpectral
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Direct Frobenius estimates, without any comparison between two spectra. -/

namespace Erdos1045.MatrixDefect

open scoped BigOperators ComplexConjugate
noncomputable section

theorem frobSq_add_le {n : ℕ} (A B : Mat n) :
    frobSq (A + B) ≤ 2 * frobSq A + 2 * frobSq B := by
  simp only [frobSq, Matrix.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg ((A i j).re - (B i j).re),
    sq_nonneg ((A i j).im - (B i j).im)]

@[simp] theorem frobSq_neg {n : ℕ} (A : Mat n) : frobSq (-A) = frobSq A := by
  simp [frobSq]

theorem frobSq_sub_le {n : ℕ} (A B : Mat n) :
    frobSq (A - B) ≤ 2 * frobSq A + 2 * frobSq B := by
  simpa [sub_eq_add_neg] using frobSq_add_le A (-B)

theorem frobSq_sub_comm {n : ℕ} (A B : Mat n) : frobSq (A - B) = frobSq (B - A) := by
  rw [← frobSq_neg, neg_sub]

@[simp] theorem frobSq_conjTranspose {n : ℕ} (A : Mat n) :
    frobSq A.conjTranspose = frobSq A := by
  simp only [frobSq, Matrix.conjTranspose_apply, Complex.star_def, Complex.normSq_conj]
  exact Finset.sum_comm

theorem frobSq_unitary_mul {n : ℕ} (u : unitary (Mat n)) (A : Mat n) :
    frobSq ((u : Mat n) * A) = frobSq A := by
  have hgram : gram ((u : Mat n) * A) = gram A := by
    unfold gram
    rw [Matrix.conjTranspose_mul]
    change (star A * star (u : Mat n)) * ((u : Mat n) * A) = star A * A
    rw [mul_assoc, ← mul_assoc (star (u : Mat n)), Unitary.coe_star_mul_self,
      one_mul]
  apply Complex.ofReal_injective
  rw [← trace_gram_eq_frobSq, ← trace_gram_eq_frobSq, hgram]

theorem frobSq_mul_unitary {n : ℕ} (A : Mat n) (u : unitary (Mat n)) :
    frobSq (A * (u : Mat n)) = frobSq A := by
  rw [← frobSq_conjTranspose (A * (u : Mat n)), Matrix.conjTranspose_mul]
  have h := frobSq_unitary_mul (star u) A.conjTranspose
  simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose, frobSq_conjTranspose] using h

def vectorEnergy {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

theorem vectorEnergy_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ vectorEnergy x :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem vectorEnergy_add_le {n : ℕ} (x y : Fin n → ℂ) :
    vectorEnergy (x + y) ≤ 2 * vectorEnergy x + 2 * vectorEnergy y := by
  simp only [vectorEnergy, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg ((x i).re - (y i).re), sq_nonneg ((x i).im - (y i).im)]

theorem normSq_sum_mul_le {n : ℕ} (a x : Fin n → ℂ) :
    Complex.normSq (∑ j, a j * x j) ≤ vectorEnergy a * vectorEnergy x := by
  have hnorm : ‖∑ j, a j * x j‖ ≤ ∑ j, ‖a j‖ * ‖x j‖ := by
    simpa only [norm_mul] using norm_sum_le (s := Finset.univ) (fun j => a j * x j)
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖x j‖)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simp only [vectorEnergy, Complex.normSq_eq_norm_sq]
  exact hsq.trans hs

theorem vectorEnergy_mulVec_le {n : ℕ} (A : Mat n) (x : Fin n → ℂ) :
    vectorEnergy (A.mulVec x) ≤ frobSq A * vectorEnergy x := by
  unfold vectorEnergy
  calc
    (∑ i, Complex.normSq ((A.mulVec x) i)) ≤
        ∑ i, (∑ j, Complex.normSq (A i j)) * (∑ j, Complex.normSq (x j)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact normSq_sum_mul_le (A i) x
    _ = _ := by rw [← Finset.sum_mul]; rfl

theorem frobSq_diagonal_gram {n : ℕ} (d : Fin n → ℝ) (B : Mat n) :
    (B.conjTranspose * Matrix.diagonal (fun i => (d i : ℂ)) * B).trace =
      ((∑ j, ∑ i, d i * Complex.normSq (B i j) : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.conjTranspose_apply, Complex.star_def,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_eq_conj_mul_self]
  ring

set_option maxHeartbeats 800000 in
theorem frobSq_mul_le_of_eigenvalue_le {n : ℕ} (A B : Mat n) {b : ℝ}
    (hb : ∀ i, eigenvalue A i ≤ b) : frobSq (A * B) ≤ b * frobSq B := by
  let hA := Matrix.isHermitian_conjTranspose_mul_self A
  let u := hA.eigenvectorUnitary
  let D : Mat n := Matrix.diagonal (fun i => (eigenvalue A i : ℂ))
  let W : Mat n := star (u : Mat n) * B
  have hspec : gram A = (u : Mat n) * D * star (u : Mat n) := hA.spectral_theorem
  have hgram : gram (A * B) = W.conjTranspose * D * W := by
    have hstart : gram (A * B) = B.conjTranspose * gram A * B := by
      simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [hstart, hspec]
    dsimp only [W]
    rw [Matrix.conjTranspose_mul]
    simp only [← Matrix.star_eq_conjTranspose, star_star, Matrix.mul_assoc]
  have heq : frobSq (A * B) = ∑ j, ∑ i, eigenvalue A i * Complex.normSq (W i j) := by
    apply Complex.ofReal_injective
    rw [← trace_gram_eq_frobSq, hgram]
    exact frobSq_diagonal_gram _ _
  have hw : frobSq W = frobSq B := frobSq_unitary_mul (star u) B
  rw [heq]
  suffices hh : (∑ j, ∑ i, eigenvalue A i * Complex.normSq (W i j)) ≤ b * frobSq W by
    simpa only [hw] using hh
  calc
    (∑ j, ∑ i, eigenvalue A i * Complex.normSq (W i j)) ≤
        ∑ j, ∑ i, b * Complex.normSq (W i j) := by
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hb i) (Complex.normSq_nonneg _)
    _ = b * frobSq W := by
      simp only [← Finset.mul_sum, frobSq]
      congr 1
      exact Finset.sum_comm

end
end Erdos1045.MatrixDefect
