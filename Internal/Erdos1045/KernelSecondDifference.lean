import Erdos1045.KernelWeights
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

namespace Erdos1045.KernelWeights

noncomputable section

def secondDiff (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  a (k + 2) - 2 * a (k + 1) + a k

theorem sum_secondDiff (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, secondDiff a k) =
      (a (N + 1) - a N) - (a 1 - a 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    dsimp [secondDiff]
    ring

theorem inverse_square_secondDiff_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ 1 / (x + 2) ^ 2 - 2 / (x + 1) ^ 2 + 1 / x ^ 2 := by
  have hx1 : x + 1 ≠ 0 := by linarith
  have hx2 : x + 2 ≠ 0 := by linarith
  have hid : 1 / (x + 2) ^ 2 - 2 / (x + 1) ^ 2 + 1 / x ^ 2 =
      (6 * x ^ 2 + 12 * x + 4) / (x ^ 2 * (x + 1) ^ 2 * (x + 2) ^ 2) := by
    field_simp
    ring
  rw [hid]
  positivity

theorem weight_secondDiff_rising {n k : ℕ} (hn : 2 ≤ n) (hk : k + 2 ≤ n) :
    0 ≤ secondDiff (weight n) k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rcases k with _ | k
  · simp [secondDiff, weight, hn]
    positivity
  rcases k with _ | k
  · have hn3 : 3 ≤ n := by omega
    norm_num [secondDiff, weight, hn, hn3]
    field_simp
    norm_num
  · have hk2 : 2 ≤ k + 2 := by omega
    unfold secondDiff
    rw [weight_of_le (by omega) (by omega), weight_of_le (by omega) (by omega),
      weight_of_le (by omega) (by omega)]
    push_cast
    field_simp
    nlinarith

theorem weight_secondDiff_falling {n k : ℕ} (hn : 2 ≤ n) (hk : n ≤ k) :
    0 ≤ secondDiff (weight n) k := by
  have hk1 : 1 ≤ k := by omega
  have hk0 : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
  have hbase : weight n k = ((n - 1 : ℕ) : ℝ) ^ 2 / ((k - 1 : ℕ) : ℝ) ^ 2 := by
    rcases eq_or_lt_of_le hk with h | h
    · subst k
      rw [weight_diagonal hn, div_self]
      positivity
    · exact weight_of_gt hn h
  unfold secondDiff
  rw [weight_of_gt hn (by omega), weight_of_gt hn (by omega), hbase]
  have h1 : (((k + 1) - 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 1 := by
    norm_cast
    omega
  have h2 : (((k + 2) - 1 : ℕ) : ℝ) = ((k - 1 : ℕ) : ℝ) + 2 := by
    norm_cast
    omega
  rw [h1, h2]
  have h := mul_nonneg (sq_nonneg (((n - 1 : ℕ) : ℝ)))
    (inverse_square_secondDiff_nonneg hk0)
  convert h using 2 <;> first | rfl | ring

theorem weight_secondDiff_nonneg_except {n k : ℕ} (hn : 2 ≤ n)
    (hk : k ≠ n - 1) : 0 ≤ secondDiff (weight n) k := by
  by_cases h : k + 2 ≤ n
  · exact weight_secondDiff_rising hn h
  · exact weight_secondDiff_falling hn (by omega)

theorem weight_secondDiff_turn_lower {n : ℕ} (hn : 2 ≤ n) :
    -(4 / (n : ℝ)) ≤ secondDiff (weight n) (n - 1) := by
  rcases eq_or_lt_of_le hn with rfl | hn
  · norm_num [secondDiff, weight]
  have hn2 : 2 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast (show 3 ≤ n by omega)
  have h1 : n - 1 + 1 = n := by omega
  have h2 : n - 1 + 2 = n + 1 := by omega
  unfold secondDiff
  rw [h1, h2, weight_diagonal hn2,
    weight_of_le (n := n) (k := n - 1) (by omega) (by omega),
    weight_of_gt (n := n) (k := n + 1) hn2 (by omega)]
  simp only [Nat.add_sub_cancel, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  field_simp
  nlinarith

theorem weight_firstDiff_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    weight n (k + 1) - weight n k ≤ 4 / (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  by_cases hk : k < n
  · rcases k with _ | k
    · simp
      positivity
    rcases k with _ | k
    · rw [show 0 + 1 + 1 = 2 by omega, weight_of_le (by omega) hn, weight_one]
      norm_num
      apply (div_le_div_iff₀ (sq_pos_of_pos hn0) hn0).mpr
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    · rw [weight_of_le (by omega) (by omega), weight_of_le (by omega) (by omega)]
      have hkn : (k : ℝ) + 2 ≤ n := by exact_mod_cast (show k + 2 ≤ n by omega)
      push_cast
      field_simp
      nlinarith
  · have hkn : n ≤ k := by omega
    have hbase : weight n k = ((n - 1 : ℕ) : ℝ) ^ 2 / ((k - 1 : ℕ) : ℝ) ^ 2 := by
      rcases eq_or_lt_of_le hkn with h | h
      · subst k
        rw [weight_diagonal hn, div_self]
        exact pow_ne_zero _ (by exact_mod_cast (show n - 1 ≠ 0 by omega))
      · exact weight_of_gt hn h
    have hle : weight n (k + 1) ≤ weight n k := by
      rw [weight_of_gt hn (by omega), hbase]
      apply div_le_div_of_nonneg_left (sq_nonneg _)
      · have hk0 : (0 : ℝ) < (k - 1 : ℕ) := by exact_mod_cast (show 0 < k - 1 by omega)
        positivity
      · gcongr
        omega
    have hpos : 0 ≤ 4 / (n : ℝ) := by positivity
    linarith

theorem abs_weight_secondDiff_le {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    |secondDiff (weight n) k| ≤ secondDiff (weight n) k +
      if k = n - 1 then 8 / (n : ℝ) else 0 := by
  by_cases hk : k = n - 1
  · subst k
    simp only [↓reduceIte]
    apply abs_le.mpr
    have h := weight_secondDiff_turn_lower hn
    have hpos : 0 ≤ 8 / (n : ℝ) := by positivity
    have heq : 8 / (n : ℝ) = 2 * (4 / (n : ℝ)) := by ring
    constructor <;> linarith
  · rw [if_neg hk, add_zero, abs_of_nonneg (weight_secondDiff_nonneg_except hn hk)]

theorem sum_abs_weight_secondDiff_le {n : ℕ} (hn : 2 ≤ n) (N : ℕ) :
    (∑ k ∈ Finset.range N, |secondDiff (weight n) k|) ≤ 12 / (n : ℝ) := by
  have hpos : 0 ≤ 8 / (n : ℝ) := by positivity
  have hind : (∑ k ∈ Finset.range N, if k = n - 1 then 8 / (n : ℝ) else 0) ≤
      8 / (n : ℝ) := by
    simp only [Finset.sum_ite_eq']
    split_ifs <;> linarith
  calc
    (∑ k ∈ Finset.range N, |secondDiff (weight n) k|) ≤
        ∑ k ∈ Finset.range N, (secondDiff (weight n) k +
          if k = n - 1 then 8 / (n : ℝ) else 0) :=
      Finset.sum_le_sum (fun k _ => abs_weight_secondDiff_le hn k)
    _ = (weight n (N + 1) - weight n N) +
        ∑ k ∈ Finset.range N, if k = n - 1 then 8 / (n : ℝ) else 0 := by
      rw [Finset.sum_add_distrib, sum_secondDiff]
      simp
    _ ≤ 12 / (n : ℝ) := by
      have hfirst := weight_firstDiff_le hn N
      have heq : 4 / (n : ℝ) + 8 / (n : ℝ) = 12 / (n : ℝ) := by ring
      linarith

theorem summable_abs_weight_secondDiff {n : ℕ} (hn : 2 ≤ n) :
    Summable (fun k => |secondDiff (weight n) k|) :=
  summable_of_sum_range_le (fun _ => abs_nonneg _) (sum_abs_weight_secondDiff_le hn)

theorem tsum_abs_weight_secondDiff_le {n : ℕ} (hn : 2 ≤ n) :
    (∑' k, |secondDiff (weight n) k|) ≤ 12 / (n : ℝ) :=
  Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) (sum_abs_weight_secondDiff_le hn)

end

end Erdos1045.KernelWeights
