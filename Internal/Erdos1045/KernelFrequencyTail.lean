import Erdos1045.KernelWeights
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum

open scoped BigOperators

namespace Erdos1045.KernelWeights

noncomputable section

theorem reciprocal_square_le_telescoping {x : ℝ} (hx : 0 < x) :
    1 / (x + 1) ^ 2 ≤ 1 / x - 1 / (x + 1) := by
  have hx1 : 0 < x + 1 := by linarith
  have hid : 1 / x - 1 / (x + 1) = 1 / (x * (x + 1)) := by
    field_simp
    ring
  rw [hid]
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hx hx1)
  nlinarith

theorem weight_le_telescoping {n k : ℕ} (hn : 2 ≤ n) (hk : n < k) :
    weight n k ≤ ((n - 1 : ℕ) : ℝ) ^ 2 *
      (1 / ((k - 2 : ℕ) : ℝ) - 1 / ((k - 1 : ℕ) : ℝ)) := by
  have hx : (0 : ℝ) < (k - 2 : ℕ) := by exact_mod_cast (show 0 < k - 2 by omega)
  have hcast : ((k - 1 : ℕ) : ℝ) = ((k - 2 : ℕ) : ℝ) + 1 := by
    norm_cast
    omega
  rw [weight_of_gt hn hk, hcast]
  have h := mul_le_mul_of_nonneg_left (reciprocal_square_le_telescoping hx)
    (sq_nonneg (((n - 1 : ℕ) : ℝ)))
  simpa only [mul_one_div] using h

theorem sum_shifted_weight_le {n L : ℕ} (hn : 2 ≤ n) (hL : n < L) (N : ℕ) :
    (∑ k ∈ Finset.range N, weight n (k + L)) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 / ((L - 2 : ℕ) : ℝ) := by
  have htel : (∑ k ∈ Finset.range N,
      (1 / (((k + L) - 2 : ℕ) : ℝ) - 1 / (((k + L) - 1 : ℕ) : ℝ))) =
      1 / ((L - 2 : ℕ) : ℝ) - 1 / (((N + L) - 2 : ℕ) : ℝ) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have hidx : N + 1 + L - 2 = N + L - 1 := by omega
      rw [hidx]
      ring
  calc
    (∑ k ∈ Finset.range N, weight n (k + L)) ≤
        ∑ k ∈ Finset.range N, ((n - 1 : ℕ) : ℝ) ^ 2 *
          (1 / (((k + L) - 2 : ℕ) : ℝ) - 1 / (((k + L) - 1 : ℕ) : ℝ)) :=
      Finset.sum_le_sum (fun k _ => weight_le_telescoping hn (by omega))
    _ = ((n - 1 : ℕ) : ℝ) ^ 2 *
        (1 / ((L - 2 : ℕ) : ℝ) - 1 / (((N + L) - 2 : ℕ) : ℝ)) := by
      rw [← Finset.mul_sum, htel]
    _ ≤ ((n - 1 : ℕ) : ℝ) ^ 2 / ((L - 2 : ℕ) : ℝ) := by
      rw [mul_sub, mul_one_div, mul_one_div]
      have hp : 0 ≤ ((n - 1 : ℕ) : ℝ) ^ 2 / (((N + L) - 2 : ℕ) : ℝ) := by positivity
      linarith

theorem summable_weight {n : ℕ} (hn : 2 ≤ n) : Summable (weight n) := by
  apply (summable_nat_add_iff (n + 1)).mp
  exact summable_of_sum_range_le (fun k => weight_nonneg n (k + (n + 1)))
    (sum_shifted_weight_le hn (by omega))

theorem tsum_shifted_weight_le {n L : ℕ} (hn : 2 ≤ n) (hL : n < L) :
    (∑' k, weight n (k + L)) ≤
      ((n - 1 : ℕ) : ℝ) ^ 2 / ((L - 2 : ℕ) : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun k => weight_nonneg n (k + L))
    (sum_shifted_weight_le hn hL)

theorem tsum_weight_le {n : ℕ} (hn : 2 ≤ n) :
    (∑' k, weight n k) ≤ 2 * (n : ℝ) := by
  have hprefix : (∑ k ∈ Finset.range (n + 1), weight n k) ≤ (n + 1 : ℕ) := by
    calc
      (∑ k ∈ Finset.range (n + 1), weight n k) ≤ ∑ _k ∈ Finset.range (n + 1), (1 : ℝ) :=
        Finset.sum_le_sum (fun k _ => weight_le_one hn k)
      _ = (n + 1 : ℕ) := by simp
  have htail := tsum_shifted_weight_le (n := n) (L := n + 1) hn (by omega)
  have hidx : n + 1 - 2 = n - 1 := by omega
  rw [hidx, sq, mul_div_cancel_right₀ _ (by exact_mod_cast (show n - 1 ≠ 0 by omega))] at htail
  rw [← (summable_weight hn).sum_add_tsum_nat_add (n + 1)]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  push_cast at hprefix
  rw [hcast] at htail
  linarith

theorem normalized_frequency_tail_le {n M : ℕ} (hn : 2 ≤ n) (hM : 2 ≤ M) :
    (∑' k, weight n (k + M * n)) / (n : ℝ) ≤ 2 / (M : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMn : n < M * n := by nlinarith
  have hprod : 4 ≤ M * n := by nlinarith
  have hden : (0 : ℝ) < (M * n - 2 : ℕ) := by
    exact_mod_cast (show 0 < M * n - 2 by omega)
  have htail := tsum_shifted_weight_le hn hMn
  have hcast : ((M * n - 2 : ℕ) : ℝ) = (M : ℝ) * n - 2 := by
    rw [Nat.cast_sub (show 2 ≤ M * n by nlinarith), Nat.cast_mul]
    norm_num
  have hncast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  calc
    (∑' k, weight n (k + M * n)) / (n : ℝ) ≤
        (((n - 1 : ℕ) : ℝ) ^ 2 / ((M * n - 2 : ℕ) : ℝ)) / n := by
      exact div_le_div_of_nonneg_right htail hn0.le
    _ ≤ 2 / (M : ℝ) := by
      rw [div_div]
      apply (div_le_div_iff₀ (mul_pos hden hn0) hM0).mpr
      rw [hcast, hncast]
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith [mul_nonneg (show 0 ≤ (M : ℝ) - 2 by linarith) (sq_nonneg (n : ℝ))]

end

end Erdos1045.KernelWeights
