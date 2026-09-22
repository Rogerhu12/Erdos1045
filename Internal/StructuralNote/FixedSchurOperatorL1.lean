import EventualExact.SchurOperatorBounds
import EventualExact.SchurWeightBounds

/-! The Schur operator improves a normalized L1 input bound to an L2 bound. -/

namespace StructuralNote.FixedSchurOperatorL1

open Complex Erdos1045 Erdos1045.EventualExact
open FourierMultiplier FiniteFourierLift SchurLiftBounds SchurOperatorBounds
open scoped BigOperators

noncomputable section

theorem coefficient_norm_le_l1 {n : ℕ} (q : Fin n → ℝ) (p : Fin n) :
    ‖realCoefficient q p‖ ≤ (∑ j, |q j|) / (n : ℝ) := by
  change ‖(∑ j, (q j : ℂ) * (starRingEnd ℂ) (character n p j)) / (n : ℂ)‖ ≤ _
  rw [norm_div, norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro j _
  simp only [norm_mul, norm_conj, norm_real, Real.norm_eq_abs, character,
    norm_pow, ClosedFourier.root_norm, one_pow, mul_one]

theorem meanSquare_operator_eq {n : ℕ} (hn : 0 < n) (heven : Even n) (q : Fin n → ℝ) :
    meanSquare (operator n q) = ∑ p : Fin n,
      SchurWeights.weight n p ^ 2 * ‖realCoefficient q p‖ ^ 2 := by
  rw [← realCoefficient_parseval hn]
  simp only [coefficient_operator hn heven, normSq_eq_norm_sq, norm_mul,
    norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

theorem meanSquare_operator_l1 {n : ℕ} (hn : 0 < n) (heven : Even n) (q : Fin n → ℝ) :
    meanSquare (operator n q) ≤ (∑ p : Fin n, SchurWeights.weight n p ^ 2) *
      ((∑ j, |q j|) / (n : ℝ)) ^ 2 := by
  rw [meanSquare_operator_eq hn heven, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (coefficient_norm_le_l1 q p) 2) (sq_nonneg _)

theorem even_operator_l1_bound {m : ℕ} (hm : 2048 ≤ 2 * m) (q : Fin (2 * m) → ℝ) :
    meanSquare (operator (2 * m) q) ≤
      ((∑ j, |q j|) / (2 * m : ℝ)) ^ 2 / 2 := by
  have h := meanSquare_operator_l1 (show 0 < 2 * m by omega) (⟨m, by omega⟩ : Even (2 * m)) q
  have hw := SchurWeights.weight_square_sum_lt_half hm
  have hh := mul_le_mul_of_nonneg_right hw.le
    (sq_nonneg ((∑ j, |q j|) / ((2 * m : ℕ) : ℝ)))
  apply (h.trans hh).trans_eq
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  ring

end
end StructuralNote.FixedSchurOperatorL1
