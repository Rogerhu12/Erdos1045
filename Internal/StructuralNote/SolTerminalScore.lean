import StructuralNote.SolTerminalInteraction
import StructuralNote.SolTerminalBackground

namespace StructuralNote.SolTerminalScore

open Finset
open scoped BigOperators
open SolTerminalDistances SolTerminalInteraction SolTerminalBackground

def compressionScore (E : Finset ℕ) (b K : ℕ → ℝ) (cB cI : ℝ) (L : ℕ) : ℝ :=
  cB * ∑ x ∈ E, b (slideAt L x) +
    cI * ∑ x ∈ E, ∑ y ∈ E, K (Nat.dist (slideAt L x) (slideAt L y))

theorem normalized_score_gain (E : Finset ℕ) {b K : ℕ → ℝ} {N L R : ℕ}
    {A n gamma : ℝ} (hA : 0 ≤ A) (hn : 0 < n)
    (hL : 0 < L)
    (hBg : gamma * (R - L + 1) ≤
      (∑ x ∈ E, b (slideAt L x)) - ∑ x ∈ E, b x)
    (hbound : ∀ x ∈ E, ∀ y ∈ E, Nat.dist x y ≤ N)
    (hmono : AntitoneOn K (Set.Icc 0 N)) :
    (4 * A / n) * (gamma * (R - L + 1)) ≤
      compressionScore E b K (4 * A / n) (16 * A^2 / n^2) L -
        ((4 * A / n) * ∑ x ∈ E, b x +
          (16 * A^2 / n^2) * ∑ x ∈ E, ∑ y ∈ E, K (Nat.dist x y)) := by
  have hcB : 0 ≤ 4 * A / n := div_nonneg (mul_nonneg (by norm_num) hA) hn.le
  have hcI : 0 ≤ 16 * A^2 / n^2 := div_nonneg (mul_nonneg (by norm_num) (sq_nonneg A)) (sq_nonneg n)
  have hi := ordered_interaction_nondecreasing E hL hbound hmono
  unfold compressionScore
  nlinarith [mul_le_mul_of_nonneg_left hBg hcB, mul_le_mul_of_nonneg_left hi hcI]

end StructuralNote.SolTerminalScore
