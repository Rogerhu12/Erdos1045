import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-!
# The discrete weights and the low-frequency cosine kernel

The weight is the piecewise weight of Section 5.2. We prove its elementary
bounds and a Lipschitz bound for the finite truncation of the normalized kernel.
This verifies only the low-frequency half of the direct-comparison strategy;
neither an infinite kernel nor its spatial tail estimate is asserted here.
-/

open scoped BigOperators

namespace Erdos1045.KernelWeights

noncomputable section

/-- The exact piecewise weights, including the omitted frequencies zero and one. -/
def weight (n k : ℕ) : ℝ :=
  if k < 2 then 0
  else if k ≤ n then (k : ℝ) ^ 2 / (n : ℝ) ^ 2
  else ((n - 1 : ℕ) : ℝ) ^ 2 / ((k - 1 : ℕ) : ℝ) ^ 2

@[simp] theorem weight_zero (n : ℕ) : weight n 0 = 0 := by
  simp [weight]

@[simp] theorem weight_one (n : ℕ) : weight n 1 = 0 := by
  simp [weight]

theorem weight_of_le {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    weight n k = (k : ℝ) ^ 2 / (n : ℝ) ^ 2 := by
  simp [weight, not_lt.mpr hk, hkn]

theorem weight_of_gt {n k : ℕ} (hn : 2 ≤ n) (hkn : n < k) :
    weight n k = ((n - 1 : ℕ) : ℝ) ^ 2 / ((k - 1 : ℕ) : ℝ) ^ 2 := by
  simp [weight, show ¬k < 2 by omega, not_le.mpr hkn]

theorem weight_nonneg (n k : ℕ) : 0 ≤ weight n k := by
  unfold weight
  split_ifs <;> positivity

theorem weight_le_one {n : ℕ} (hn : 2 ≤ n) (k : ℕ) : weight n k ≤ 1 := by
  unfold weight
  split_ifs with hk hkn
  · norm_num
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    apply (div_le_one (sq_pos_of_pos hnpos)).mpr
    gcongr
  · have hkpos : (0 : ℝ) < (k - 1 : ℕ) := by
      exact_mod_cast (show 0 < k - 1 by omega)
    apply (div_le_one (sq_pos_of_pos hkpos)).mpr
    gcongr
    exact_mod_cast (show n ≤ k by omega)

@[simp] theorem weight_diagonal {n : ℕ} (hn : 2 ≤ n) : weight n n = 1 := by
  rw [weight_of_le hn le_rfl]
  exact div_self (pow_ne_zero _ (by exact_mod_cast (show n ≠ 0 by omega)))

/-- The inverse-square high-frequency majorant, with a uniform constant. -/
theorem weight_tail_le {n k : ℕ} (hn : 2 ≤ n) (hkn : n < k) :
    weight n k ≤ 4 * (n : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
  have hk : 2 ≤ k := by omega
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkm0 : (0 : ℝ) < (k - 1 : ℕ) := by
    exact_mod_cast (show 0 < k - 1 by omega)
  have hnm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simp only [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  have hkm : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    simp only [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_one]
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hratio : ((n - 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ) ≤ 2 * n / k := by
    apply (div_le_div_iff₀ hkm0 hk0).mpr
    rw [hnm, hkm]
    nlinarith [mul_nonneg hn0 (show 0 ≤ (k : ℝ) - 2 by linarith)]
  rw [weight_of_gt hn hkn, ← div_pow]
  calc
    (((n - 1 : ℕ) : ℝ) / ((k - 1 : ℕ) : ℝ)) ^ 2 ≤ (2 * n / k) ^ 2 := by
      exact (sq_le_sq₀ (by positivity) (by positivity)).mpr hratio
    _ = 4 * (n : ℝ) ^ 2 / (k : ℝ) ^ 2 := by ring

/-- A finite normalized cosine kernel for any real weights. -/
def finiteKernel (n N : ℕ) (a : ℕ → ℝ) (s : ℝ) : ℝ :=
  (∑ k ∈ Finset.range N, a k * Real.cos ((k : ℝ) * s / n)) / n

@[simp] theorem finiteKernel_empty (n : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    finiteKernel n 0 a s = 0 := by
  simp [finiteKernel]

theorem finiteKernel_even (n N : ℕ) (a : ℕ → ℝ) (s : ℝ) :
    finiteKernel n N a (-s) = finiteKernel n N a s := by
  simp [finiteKernel, mul_neg, neg_div, Real.cos_neg]

theorem finiteKernel_at_zero (n N : ℕ) (a : ℕ → ℝ) :
    finiteKernel n N a 0 = (∑ k ∈ Finset.range N, a k) / n := by
  simp [finiteKernel]

/-- Uniform low-frequency Lipschitz control. The quadratic cutoff dependence is
sufficient for the finite-cutoff replacement of the continuous limiting kernel. -/
theorem finiteKernel_lipschitz {n N : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha0 : ∀ k ∈ Finset.range N, 0 ≤ a k)
    (ha1 : ∀ k ∈ Finset.range N, a k ≤ 1) (s t : ℝ) :
    |finiteKernel n N a s - finiteKernel n N a t| ≤
      ((N : ℝ) / n) ^ 2 * |s - t| := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm (k : ℕ) (hk : k ∈ Finset.range N) :
      |a k * Real.cos ((k : ℝ) * s / n) - a k * Real.cos ((k : ℝ) * t / n)| ≤
        ((N : ℝ) / n) * |s - t| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (ha0 k hk)]
    calc
      a k * |Real.cos ((k : ℝ) * s / n) - Real.cos ((k : ℝ) * t / n)| ≤
          |Real.cos ((k : ℝ) * s / n) - Real.cos ((k : ℝ) * t / n)| :=
        mul_le_of_le_one_left (abs_nonneg _) (ha1 k hk)
      _ ≤ |(k : ℝ) * s / n - (k : ℝ) * t / n| := Real.abs_cos_sub_cos_le _ _
      _ = ((k : ℝ) / n) * |s - t| := by
        rw [show (k : ℝ) * s / n - (k : ℝ) * t / n = (k / n) * (s - t) by ring]
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ k / n)]
      _ ≤ ((N : ℝ) / n) * |s - t| := by
        gcongr
        exact_mod_cast (Finset.mem_range.mp hk).le
  unfold finiteKernel
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos hn0]
  calc
    |∑ k ∈ Finset.range N,
        (a k * Real.cos ((k : ℝ) * s / n) - a k * Real.cos ((k : ℝ) * t / n))| / n ≤
        (∑ k ∈ Finset.range N,
          |a k * Real.cos ((k : ℝ) * s / n) - a k * Real.cos ((k : ℝ) * t / n)|) / n := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _k ∈ Finset.range N, ((N : ℝ) / n) * |s - t|) / n := by
      gcongr with k hk
      exact hterm k hk
    _ = ((N : ℝ) / n) ^ 2 * |s - t| := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- Specialization to the manuscript's actual piecewise weights. -/
theorem weightedKernel_lipschitz {n : ℕ} (hn : 2 ≤ n) (N : ℕ) (s t : ℝ) :
    |finiteKernel n N (weight n) s - finiteKernel n N (weight n) t| ≤
      ((N : ℝ) / n) ^ 2 * |s - t| := by
  exact finiteKernel_lipschitz (by omega) (weight n)
    (fun k _ => weight_nonneg n k) (fun k _ => weight_le_one hn k) s t

/-- A finite truncation is bounded uniformly in its spatial argument. -/
theorem finiteKernel_abs_le {n N : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ k ∈ Finset.range N, |a k| ≤ 1) (s : ℝ) :
    |finiteKernel n N a s| ≤ (N : ℝ) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold finiteKernel
  rw [abs_div, abs_of_pos hn0]
  calc
    |∑ k ∈ Finset.range N, a k * Real.cos ((k : ℝ) * s / n)| / n ≤
        (∑ k ∈ Finset.range N, |a k * Real.cos ((k : ℝ) * s / n)|) / n := by
      gcongr
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ (∑ _k ∈ Finset.range N, (1 : ℝ)) / n := by
      gcongr with k hk
      rw [abs_mul]
      calc
        |a k| * |Real.cos ((k : ℝ) * s / n)| ≤ 1 * 1 :=
          mul_le_mul (ha k hk) (Real.abs_cos_le_one _) (abs_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    _ = (N : ℝ) / n := by simp

/-- At frequency cutoff `M*n`, the Lipschitz constant is independent of `n`. -/
theorem weightedKernel_scaled_cutoff {n : ℕ} (hn : 2 ≤ n) (M : ℕ) (s t : ℝ) :
    |finiteKernel n (M * n) (weight n) s - finiteKernel n (M * n) (weight n) t| ≤
      (M : ℝ) ^ 2 * |s - t| := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simpa [Nat.cast_mul, hn0] using weightedKernel_lipschitz hn (M * n) s t

end

end Erdos1045.KernelWeights
