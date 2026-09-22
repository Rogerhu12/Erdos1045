import EventualExact.SchurLiftBounds

/-! Fourier Cauchy--Schwarz for the actual finite real Schur operator. -/

namespace Erdos1045.EventualExact.SchurOperatorBounds

open Complex FourierMultiplier FiniteFourierLift SchurLiftBounds
open scoped BigOperators
noncomputable section
local notation "conj" => (starRingEnd ℂ)

theorem synthesis_normSq {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) :
    (∑ j, normSq (synthesis a j)) = (n : ℝ) * ∑ p, normSq (a p) := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  simp_rw [← Complex.mul_conj, synthesis, map_sum, map_mul]
  rw [LocalFourier.sum_bilinear]
  simp_rw [character_orthogonality hn]
  simp [Finset.mul_sum, mul_comm, mul_left_comm]

theorem realCoefficient_parseval {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    (∑ p, normSq (realCoefficient q p)) = meanSquare q := by
  have h := synthesis_normSq hn (realCoefficient q)
  have hs (j : Fin n) : synthesis (realCoefficient q) j = (q j : ℂ) :=
    synthesis_coefficient hn _ j
  simp_rw [hs, Complex.normSq_ofReal] at h
  unfold meanSquare
  apply (eq_div_iff (by exact_mod_cast hn.ne' : (n : ℝ) ≠ 0)).2
  simpa only [mul_comm, pow_two] using h.symm

theorem operator_abs_le_sum {n : ℕ} (q : Fin n → ℝ) (j : Fin n) :
    |operator n q j| ≤ ∑ p : Fin n, SchurWeights.weight n p * ‖realCoefficient q p‖ := by
  rw [operator_eq_synthesis_re]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  apply Finset.sum_le_sum
  intro p _
  simp [character, ClosedFourier.root_norm, SchurWeights.weight_nonneg,
    abs_of_nonneg]

/-- The normalization is empirical mean square, with the actual finite weight square mass. -/
theorem operator_pointwise_sq_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) (j : Fin n) :
    (operator n q j) ^ 2 ≤ (∑ p : Fin n, SchurWeights.weight n p ^ 2) * meanSquare q := by
  have h := operator_abs_le_sum q j
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun p : Fin n => SchurWeights.weight n p) (fun p => ‖realCoefficient q p‖)
  have hnrm : (∑ p, ‖realCoefficient q p‖ ^ 2) = meanSquare q := by
    simp_rw [← Complex.normSq_eq_norm_sq]
    exact realCoefficient_parseval hn q
  rw [hnrm] at hcs
  have hpos : 0 ≤ ∑ p : Fin n, SchurWeights.weight n p * ‖realCoefficient q p‖ :=
    Finset.sum_nonneg fun p _ => mul_nonneg (SchurWeights.weight_nonneg _ _) (norm_nonneg _)
  have hs := (sq_le_sq₀ (abs_nonneg _) hpos).2 h
  rw [sq_abs] at hs
  exact hs.trans hcs

theorem operator_sup_sq_le {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ) :
    ‖operator n q‖ ^ 2 ≤ (∑ p : Fin n, SchurWeights.weight n p ^ 2) * meanSquare q := by
  have hD : 0 ≤ (∑ p : Fin n, SchurWeights.weight n p ^ 2) * meanSquare q :=
    mul_nonneg (Finset.sum_nonneg fun p _ => sq_nonneg _) (meanSquare_nonneg q)
  have hnorm : ‖operator n q‖ ≤ Real.sqrt
      ((∑ p : Fin n, SchurWeights.weight n p ^ 2) * meanSquare q) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro j
    apply Real.le_sqrt_of_sq_le
    simpa only [Real.norm_eq_abs, sq_abs] using operator_pointwise_sq_le hn q j
  have hsq := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hnorm
  rwa [Real.sq_sqrt hD] at hsq

end
end Erdos1045.EventualExact.SchurOperatorBounds
