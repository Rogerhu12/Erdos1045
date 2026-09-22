import EventualExact.SchurOperatorBounds
import EventualExact.SchurWeightBounds

/-! A strict actual Schur-potential bound from an ordinary mean-square budget. -/

namespace Erdos1045.EventualExact.SchurOperatorBounds

open FourierMultiplier SchurLiftBounds
noncomputable section

theorem operator_sup_sq_le_fifteen_thirtytwo {m : ℕ} (hm : 2048 ≤ 2 * m)
    (q : Fin (2 * m) → ℝ) : ‖operator (2 * m) q‖ ^ 2 ≤ (15 / 32 : ℝ) * meanSquare q := by
  exact (operator_sup_sq_le (by omega) q).trans
    (mul_le_mul_of_nonneg_right (SchurWeights.weight_square_sum_le_fifteen_thirtytwo hm)
      (meanSquare_nonneg q))

theorem operator_sup_sq_le_budget {m : ℕ} (hm : 2048 ≤ 2 * m)
    (q : Fin (2 * m) → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbudget : meanSquare q ≤ 3 * Real.pi ^ 2 / 2 + ε) :
    ‖operator (2 * m) q‖ ^ 2 ≤ 45 * Real.pi ^ 2 / 64 + ε := by
  have h := operator_sup_sq_le_fifteen_thirtytwo hm q
  nlinarith

theorem operator_sup_le_seven_eighths_pi {m : ℕ} (hm : 2048 ≤ 2 * m)
    (q : Fin (2 * m) → ℝ) {ε : ℝ} (hε : ε ≤ Real.pi ^ 2 / 16)
    (hbudget : meanSquare q ≤ 3 * Real.pi ^ 2 / 2 + ε) :
    ‖operator (2 * m) q‖ ≤ 7 * Real.pi / 8 := by
  have h := operator_sup_sq_le_fifteen_thirtytwo hm q
  have hp := Real.pi_pos
  have hq := norm_nonneg (operator (2 * m) q)
  nlinarith [sq_nonneg (8 * ‖operator (2 * m) q‖ - 7 * Real.pi)]

theorem operator_relative_sup_lt_one {m : ℕ} (hm : 2048 ≤ 2 * m)
    (q : Fin (2 * m) → ℝ) {ε : ℝ} (hε : ε ≤ Real.pi ^ 2 / 16)
    (hbudget : meanSquare q ≤ 3 * Real.pi ^ 2 / 2 + ε) :
    ‖operator (2 * m) q‖ / Real.pi < 1 := by
  apply (div_lt_one Real.pi_pos).2
  have h := operator_sup_le_seven_eighths_pi hm q hε hbudget
  linarith [Real.pi_pos]

end
end Erdos1045.EventualExact.SchurOperatorBounds
