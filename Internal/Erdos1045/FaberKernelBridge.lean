import Erdos1045.FaberCrossIdentity
import Erdos1045.KernelFourier
import Erdos1045.MatrixTrace

namespace Erdos1045.FaberFourier

open scoped BigOperators ComplexConjugate
noncomputable section

theorem spectral_weight_summable {n : ℕ} (hn : 2 ≤ n) (θ : Fin n → ℝ) :
    Summable (fun k => KernelWeights.weight n k * ‖powerSum θ k‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => mul_nonneg (KernelWeights.weight_nonneg n k) (sq_nonneg _)) _
    ((KernelWeights.summable_weight hn).mul_right ((n : ℝ) ^ 2))
  intro k
  apply mul_le_mul_of_nonneg_left _ (KernelWeights.weight_nonneg n k)
  exact (sq_le_sq₀ (norm_nonneg _) (Nat.cast_nonneg _)).2 (norm_powerSum_le θ k)

theorem powerSum_eq_circlePowerSum {n : ℕ} (θ : ℕ → ℝ) (k : ℕ) :
    powerSum (fun j : Fin n => θ j) k = KernelWeights.circlePowerSum n θ k := by
  unfold powerSum KernelWeights.circlePowerSum
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro j _
  unfold character
  congr 1
  push_cast
  ring

theorem spectralSquareSum_eq_fourierSquareSum {n : ℕ} (θ : CyclicAngles.Angles n) :
    spectralSquareSum (fun j : Fin n => θ.angle j) = KernelWeights.fourierSquareSum θ := by
  unfold spectralSquareSum KernelWeights.fourierSquareSum
  congr 1
  apply tsum_congr
  intro k
  have h := powerSum_eq_circlePowerSum (n := n) (fun i : ℕ => θ.angle i) k
  exact congrArg (fun z : ℂ => KernelWeights.weight n k * ‖z‖ ^ 2) h

def characterMatrix {n : ℕ} (θ : Fin n → ℝ) : MatrixDefect.Mat n :=
  fun j k => conj (character k (θ j))

theorem conj_character (k : ℕ) (t : ℝ) :
    conj (character k t) = Complex.exp ((t : ℂ) * Complex.I) ^ k := by
  unfold character
  rw [← Complex.exp_conj, ← Complex.exp_nat_mul]
  congr 1
  simp only [map_mul, map_neg, map_natCast, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem characterMatrix_eq_powers {n : ℕ} (θ : Fin n → ℝ) :
    characterMatrix θ = fun (j k : Fin n) => Complex.exp ((θ j : ℂ) * Complex.I) ^ (k : ℕ) := by
  ext j k
  exact conj_character k (θ j)

theorem characterMatrix_unit {n : ℕ} (θ : Fin n → ℝ) :
    ∀ j k, Complex.normSq (characterMatrix θ j k) = 1 := by
  intro j k
  simp [characterMatrix, Complex.normSq_eq_norm_sq, norm_character]

theorem matrix_firstOrder_cross_identity {n : ℕ} (hn : 0 < n)
    (c : ℝ) (a : ℕ → ℂ) (θ : Fin n → ℝ) (ha : Summable (fun m => ‖a m‖)) :
    MatrixDefect.cross (characterMatrix θ)
      (coefficientMatrix (fun j => firstOrder (coefficient c a θ j))) =
        (crossSeries a θ).re / c := by
  rw [← firstOrder_cross_identity hn c a θ ha]
  unfold MatrixDefect.cross MatrixDefect.entryInner characterMatrix coefficientMatrix
  simp [Finset.sum_range]

/-- The actual first-order matrix cross term and the exact Section 5.2 kernel.
All convergence required for Cauchy--Schwarz is supplied internally. -/
theorem matrix_firstOrder_cross_le (classic : ClassicalSequenceFacts)
    {n : ℕ} (hn : 2 ≤ n) {c E : ℝ} (hc : 0 < c) (hE0 : 0 ≤ E)
    (a : ℕ → ℂ) (θ : Fin n → ℝ)
    (ha : Summable (fun m : ℕ => (1 + (m : ℝ) ^ 2) * ‖a m‖ ^ 2))
    (haAbs : Summable (fun m => ‖a m‖))
    (hE : E ^ 2 = 2 * Real.pi * (∑' m : ℕ, (m : ℝ) ^ 2 * ‖a m‖ ^ 2)) :
    MatrixDefect.cross (characterMatrix θ)
      (coefficientMatrix (fun j => firstOrder (coefficient c a θ j))) ≤
        ((n : ℝ) * E / (c * Real.sqrt (2 * Real.pi))) * Real.sqrt (spectralSquareSum θ) := by
  rw [matrix_firstOrder_cross_identity (by omega) c a θ haAbs]
  exact crossSeries_cauchy classic hn hc hE0 a θ ha hE (spectral_weight_summable hn θ)

end
end Erdos1045.FaberFourier
