import Erdos1045.MatrixDefect

/-! # Normalization by the square root of the matrix size

These are algebraic identities for actual matrices, with no classical
assumptions. They connect the paper's `F`, `U`, and `R` to `A` and `V`.
-/

namespace Erdos1045.MatrixDefect

open scoped BigOperators

noncomputable section

def normalize {n : ℕ} (A : Mat n) : Mat n := (Real.sqrt (n : ℝ) : ℂ)⁻¹ • A

theorem frobSq_smul {n : ℕ} (c : ℂ) (A : Mat n) :
    frobSq (c • A) = Complex.normSq c * frobSq A := by
  simp [frobSq, Complex.normSq_mul, Finset.mul_sum]

theorem detSq_smul {n : ℕ} (c : ℂ) (A : Mat n) :
    detSq (c • A) = Complex.normSq c ^ n * detSq A := by
  simp [detSq, map_mul, map_pow]

theorem normSq_normalizing_scalar (n : ℕ) :
    Complex.normSq (Real.sqrt (n : ℝ) : ℂ)⁻¹ = (n : ℝ)⁻¹ := by
  rw [Complex.normSq_inv, Complex.normSq_ofReal, ← sq,
    Real.sq_sqrt (Nat.cast_nonneg n)]

theorem frobSq_normalize {n : ℕ} (A : Mat n) :
    frobSq (normalize A) = frobSq A / n := by
  rw [normalize, frobSq_smul, normSq_normalizing_scalar]
  ring

theorem detSq_normalize {n : ℕ} (A : Mat n) :
    detSq (normalize A) = detSq A / (n : ℝ) ^ n := by
  rw [normalize, detSq_smul, normSq_normalizing_scalar, inv_pow]
  ring

theorem normalize_sub {n : ℕ} (A V : Mat n) :
    normalize A - normalize V = normalize (A - V) := by
  simp [normalize, smul_sub]

theorem frobSq_normalized_difference {n : ℕ} (A V : Mat n) :
    frobSq (normalize A - normalize V) = frobSq (A - V) / n := by
  rw [normalize_sub, frobSq_normalize]

theorem frobSq_eq_card_sq_of_unit_entries {n : ℕ} (U : Mat n)
    (hU : ∀ i j, Complex.normSq (U i j) = 1) : frobSq U = (n : ℝ) ^ 2 := by
  simp [frobSq, hU]
  ring

theorem normalized_unit_entries_trace {n : ℕ} (hn : n ≠ 0) (U : Mat n)
    (hU : ∀ i j, Complex.normSq (U i j) = 1) : frobSq (normalize U) = n := by
  rw [frobSq_normalize, frobSq_eq_card_sq_of_unit_entries U hU]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  apply (div_eq_iff hn').2
  ring

theorem defect_normalize {n : ℕ} (A : Mat n) :
    defect (normalize A) = frobSq A / n - n - Real.log (detSq A / (n : ℝ) ^ n) := by
  simp only [defect, frobSq_normalize, detSq_normalize]

theorem defect_normalize_log {n : ℕ} (hn : n ≠ 0) (A : Mat n)
    (hdet : A.det ≠ 0) :
    defect (normalize A) = frobSq A / n - n + n * Real.log n - Real.log (detSq A) := by
  rw [defect_normalize]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hdet' : detSq A ≠ 0 := ((detSq_pos_iff A).2 hdet).ne'
  rw [Real.log_div hdet' (pow_ne_zero n hn'), Real.log_pow]
  ring

theorem normalized_energy_eq {n : ℕ} (hn : n ≠ 0) (U : Mat n)
    (hdet : U.det ≠ 0) (hU : ∀ i j, Complex.normSq (U i j) = 1) :
    defect (normalize U) = n * Real.log n - Real.log (detSq U) := by
  rw [defect, normalized_unit_entries_trace hn U hU, detSq_normalize]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hdet' : detSq U ≠ 0 := ((detSq_pos_iff U).2 hdet).ne'
  rw [Real.log_div hdet' (pow_ne_zero n hn'), Real.log_pow]
  ring

end

end Erdos1045.MatrixDefect
