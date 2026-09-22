import Erdos1045.MatrixStability
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Actual complex matrices and logarithmic defect

All objects are concrete: square complex matrices, their Gram matrices,
mathlib's Gram eigenvalues, the entrywise Frobenius energy, and determinants.
`ClassicalMatrixFacts` records three standard spectral identities, all proved
in `ClosedMatrixSpectral`. Perturbations are handled by direct Gram estimates
in `MatrixDirectTransfer`, without comparing the spectra of two matrices.
-/

namespace Erdos1045.MatrixDefect

open scoped BigOperators
open Erdos1045.LogDefect Erdos1045.MatrixStability

noncomputable section

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def gram {n : ℕ} (A : Mat n) : Mat n := A.conjTranspose * A

def eigenvalue {n : ℕ} (A : Mat n) : Fin n → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues

def frobSq {n : ℕ} (A : Mat n) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

def frob {n : ℕ} (A : Mat n) : ℝ := Real.sqrt (frobSq A)

def detSq {n : ℕ} (A : Mat n) : ℝ := Complex.normSq A.det

def defect {n : ℕ} (A : Mat n) : ℝ := frobSq A - n - Real.log (detSq A)

theorem frobSq_nonneg {n : ℕ} (A : Mat n) : 0 ≤ frobSq A := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem frob_sq {n : ℕ} (A : Mat n) : frob A ^ 2 = frobSq A :=
  Real.sq_sqrt (frobSq_nonneg A)

theorem eigenvalue_nonneg {n : ℕ} (A : Mat n) (i : Fin n) : 0 ≤ eigenvalue A i :=
  Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i

theorem detSq_pos_iff {n : ℕ} (A : Mat n) : 0 < detSq A ↔ A.det ≠ 0 :=
  Complex.normSq_pos

/-- Canonical finite-dimensional spectral inputs, separate from all new estimates. -/
structure ClassicalMatrixFacts : Prop where
  /-- Trace of `Aᴴ A` is both the sum of its eigenvalues and the entrywise energy. -/
  sum_eigenvalue : ∀ {n : ℕ} (A : Mat n), (∑ i, eigenvalue A i) = frobSq A
  /-- Determinant of the Gram matrix is the product of its eigenvalues and `|det A|²`. -/
  prod_eigenvalue : ∀ {n : ℕ} (A : Mat n), (∏ i, eigenvalue A i) = detSq A
  /-- Frobenius distance of a Hermitian Gram matrix from the identity. -/
  gram_deviation : ∀ {n : ℕ} (A : Mat n),
    frobSq (gram A - 1) = deviation Finset.univ (eigenvalue A)

variable (facts : ClassicalMatrixFacts)
include facts

theorem eigenvalue_pos {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) (i : Fin n) :
    0 < eigenvalue A i := by
  have hp : 0 < ∏ j, eigenvalue A j := by
    rw [facts.prod_eigenvalue A]
    exact (detSq_pos_iff A).2 hA
  have hi := Finset.prod_ne_zero_iff.mp hp.ne' i (Finset.mem_univ i)
  exact lt_of_le_of_ne (eigenvalue_nonneg A i) hi.symm

theorem det_ne_zero_of_eigenvalue_pos {n : ℕ} (A : Mat n)
    (hA : ∀ i, 0 < eigenvalue A i) : A.det ≠ 0 := by
  apply (detSq_pos_iff A).1
  rw [← facts.prod_eigenvalue A]
  exact Finset.prod_pos fun i _ => hA i

/-- Concrete trace-minus-log-determinant identity. -/
theorem defect_eq_total {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    defect A = total Finset.univ (eigenvalue A) := by
  rw [total_eq_trace_sub_card_sub_log_prod Finset.univ (eigenvalue A)
    (fun i _ => eigenvalue_pos facts A hA i)]
  rw [facts.sum_eigenvalue A, facts.prod_eigenvalue A]
  simp [defect]

theorem defect_nonneg {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) : 0 ≤ defect A := by
  rw [defect_eq_total facts A hA]
  exact total_nonneg Finset.univ _ (fun i _ => eigenvalue_pos facts A hA i)

/-- The exact coarse hypotheses of Section 5.1 produce bounded defect. -/
theorem coarse_trace_det_bound {n : ℕ} (A : Mat n) {C : ℝ}
    (htrace : frobSq A ≤ n + C) (hdet : 1 ≤ detSq A) :
    A.det ≠ 0 ∧ 0 ≤ defect A ∧ defect A ≤ C := by
  have hA : A.det ≠ 0 := (detSq_pos_iff A).1 (by linarith)
  refine ⟨hA, defect_nonneg facts A hA, ?_⟩
  have hlog := Real.log_nonneg hdet
  unfold defect
  linarith

theorem eigenvalue_bounds {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    {C : ℝ} (hC : defect A ≤ C) (i : Fin n) :
    Real.exp (-C - 1) ≤ eigenvalue A i ∧ eigenvalue A i ≤ 2 * C + 2 := by
  rw [defect_eq_total facts A hA] at hC
  exact coordinate_bounds_of_total_le Finset.univ _
    (fun j _ => eigenvalue_pos facts A hA j) hC (Finset.mem_univ i)

theorem gram_deviation_bound {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    frobSq (gram A - 1) ≤ (4 * defect A + 6) * defect A := by
  rw [facts.gram_deviation A, defect_eq_total facts A hA]
  exact deviation_le_self_bound Finset.univ _ (fun i _ => eigenvalue_pos facts A hA i)

omit facts in
/-- Exact trace normalization identifies the transferred defect with energy loss. -/
theorem defect_eq_neg_log_detSq {n : ℕ} (V : Mat n) (htrace : frobSq V = n) :
    defect V = -Real.log (detSq V) := by
  unfold defect
  rw [htrace]
  ring


end

end Erdos1045.MatrixDefect
