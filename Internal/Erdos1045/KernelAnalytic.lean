import Erdos1045.KernelSecondDifference
import Erdos1045.KernelFrequencyTail

open scoped BigOperators

namespace Erdos1045.KernelWeights

noncomputable section

def kernel (n : ℕ) (t : ℝ) : ℝ := ∑' k, weight n k * Real.cos ((k : ℝ) * t)

theorem kernel_even (n : ℕ) (t : ℝ) : kernel n (-t) = kernel n t := by
  simp [kernel, mul_neg, Real.cos_neg]

theorem kernel_reflection (n : ℕ) (t : ℝ) :
    kernel n (2 * Real.pi - t) = kernel n t := by
  unfold kernel
  apply tsum_congr
  intro k
  rw [show (k : ℝ) * (2 * Real.pi - t) = -((k : ℝ) * t) + k * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi, Real.cos_neg]

theorem kernel_periodic (n : ℕ) (t : ℝ) :
    kernel n (t + 2 * Real.pi) = kernel n t := by
  unfold kernel
  apply tsum_congr
  intro k
  rw [mul_add, Real.cos_add_nat_mul_two_pi]

theorem summable_mul_cos {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (phase : ℕ → ℝ) :
    Summable (fun k => a k * Real.cos (phase k)) := by
  apply ha.of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem norm_tsum_mul_cos_le {a : ℕ → ℝ} (ha : Summable (fun k => |a k|)) (phase : ℕ → ℝ) :
    |∑' k, a k * Real.cos (phase k)| ≤ ∑' k, |a k| := by
  apply (show ‖∑' k, a k * Real.cos (phase k)‖ ≤ ∑' k, |a k| from ?_)
  apply tsum_of_norm_bounded ha.hasSum
  intro k
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem summable_weight_cos {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    Summable (fun k => weight n k * Real.cos ((k : ℝ) * t)) := by
  apply summable_mul_cos
  simpa only [abs_of_nonneg (weight_nonneg n _)] using summable_weight hn

theorem abs_kernel_le {n : ℕ} (hn : 2 ≤ n) (t : ℝ) : |kernel n t| ≤ 2 * (n : ℝ) := by
  have ha : Summable (fun k => |weight n k|) := by
    simpa only [abs_of_nonneg (weight_nonneg n _)] using summable_weight hn
  have h := norm_tsum_mul_cos_le ha (fun k => (k : ℝ) * t)
  simp only [abs_of_nonneg (weight_nonneg n _)] at h
  exact h.trans (tsum_weight_le hn)

/-- Second-order Abel summation, proved here for arbitrary absolutely summable
real coefficients with the two initial zero terms. -/
theorem cosine_secondDiff_identity {a : ℕ → ℝ}
    (ha : Summable (fun k => |a k|)) (ha0 : a 0 = 0) (ha1 : a 1 = 0) (t : ℝ) :
    (∑' k, secondDiff a k * Real.cos (((k : ℝ) + 1) * t)) =
      (2 * Real.cos t - 2) * ∑' k, a k * Real.cos ((k : ℝ) * t) := by
  have haShift1 := (summable_nat_add_iff 1).mpr ha
  have haShift2 := (summable_nat_add_iff 2).mpr ha
  have hA := summable_mul_cos haShift2 (fun k => ((k : ℝ) + 1) * t)
  have hB := summable_mul_cos haShift1 (fun k => ((k : ℝ) + 1) * t)
  have hC := summable_mul_cos ha (fun k => ((k : ℝ) + 1) * t)
  have hminus := summable_mul_cos ha (fun k => (k : ℝ) * t - t)
  have hplus := summable_mul_cos ha (fun k => (k : ℝ) * t + t)
  have hbase := summable_mul_cos ha (fun k => (k : ℝ) * t)
  have hAeq : (∑' k, a (k + 2) * Real.cos (((k : ℝ) + 1) * t)) =
      ∑' k, a k * Real.cos ((k : ℝ) * t - t) := by
    have h := hminus.sum_add_tsum_nat_add 2
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, ha0, ha1, zero_mul, zero_add] at h
    convert h using 1
    apply tsum_congr
    intro k
    congr 2
    push_cast
    ring
  have hBeq : (∑' k, a (k + 1) * Real.cos (((k : ℝ) + 1) * t)) =
      ∑' k, a k * Real.cos ((k : ℝ) * t) := by
    have h := hbase.sum_add_tsum_nat_add 1
    simpa [ha0] using h
  have hCeq : (∑' k, a k * Real.cos (((k : ℝ) + 1) * t)) =
      ∑' k, a k * Real.cos ((k : ℝ) * t + t) := by
    apply tsum_congr
    intro k
    congr 2
    ring
  have hpair : (∑' k, a k * Real.cos ((k : ℝ) * t - t)) +
      (∑' k, a k * Real.cos ((k : ℝ) * t + t)) =
      (2 * Real.cos t) * ∑' k, a k * Real.cos ((k : ℝ) * t) := by
    rw [← hminus.tsum_add hplus, ← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [Real.cos_sub, Real.cos_add]
    ring
  have hsplit : (∑' k, secondDiff a k * Real.cos (((k : ℝ) + 1) * t)) =
      (∑' k, a (k + 2) * Real.cos (((k : ℝ) + 1) * t)) -
      2 * (∑' k, a (k + 1) * Real.cos (((k : ℝ) + 1) * t)) +
      (∑' k, a k * Real.cos (((k : ℝ) + 1) * t)) := by
    rw [← tsum_mul_left, ← hA.tsum_sub (hB.mul_left 2), ← (hA.sub (hB.mul_left 2)).tsum_add hC]
    apply tsum_congr
    intro k
    dsimp [secondDiff]
    ring
  rw [hsplit, hAeq, hBeq, hCeq]
  linarith

theorem kernel_abel_bound {n : ℕ} (hn : 2 ≤ n) (t : ℝ) :
    2 * (1 - Real.cos t) * |kernel n t| ≤ 12 / (n : ℝ) := by
  have ha : Summable (fun k => |weight n k|) := by
    simpa only [abs_of_nonneg (weight_nonneg n _)] using summable_weight hn
  have hid := cosine_secondDiff_identity ha (weight_zero n) (weight_one n) t
  have hnorm := norm_tsum_mul_cos_le (summable_abs_weight_secondDiff hn)
    (fun k => ((k : ℝ) + 1) * t)
  rw [hid, abs_mul] at hnorm
  have hsign : 2 * Real.cos t - 2 ≤ 0 := by have := Real.cos_le_one t; linarith
  rw [abs_of_nonpos hsign] at hnorm
  change -(2 * Real.cos t - 2) * |kernel n t| ≤ _ at hnorm
  have hbound := tsum_abs_weight_secondDiff_le hn
  nlinarith

/-- Spatial decay on a principal angle interval; arbitrary angles can be reduced
to this interval using the ordinary periodicity of the cosine kernel. -/
theorem kernel_spatial_bound {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : |t| ≤ Real.pi) :
    |kernel n t| * (1 + (n : ℝ) ^ 2 * t ^ 2) ≤
      (2 + 3 * Real.pi ^ 2) * (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hab := kernel_abel_bound hn t
  have hcos := Real.cos_le_one_sub_mul_cos_sq ht
  have hK := abs_nonneg (kernel n t)
  have hscaled : (4 / Real.pi ^ 2) * t ^ 2 * |kernel n t| ≤ 12 / (n : ℝ) := by
    have hp := mul_le_mul_of_nonneg_right hcos hK
    ring_nf at hab hp ⊢
    linarith
  have hmul := mul_le_mul_of_nonneg_left hscaled (show 0 ≤ Real.pi ^ 2 * n / 4 by positivity)
  have hdecay : (n : ℝ) * t ^ 2 * |kernel n t| ≤ 3 * Real.pi ^ 2 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp at hmul
    nlinarith
  have hdecay2 := mul_le_mul_of_nonneg_left hdecay hn0.le
  have hplain := abs_kernel_le hn t
  nlinarith

theorem kernel_reflected_spatial_bound {n : ℕ} (hn : 2 ≤ n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht2 : t ≤ 2 * Real.pi) :
    |kernel n t| * (1 + (n : ℝ) ^ 2 * (min t (2 * Real.pi - t)) ^ 2) ≤
      (2 + 3 * Real.pi ^ 2) * (n : ℝ) := by
  by_cases ht : t ≤ Real.pi
  · rw [min_eq_left (by linarith)]
    exact kernel_spatial_bound hn (by rwa [abs_of_nonneg ht0])
  · rw [min_eq_right (by linarith)]
    have harg : |2 * Real.pi - t| ≤ Real.pi := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    simpa only [kernel_reflection] using kernel_spatial_bound hn harg

def normalizedKernel (n : ℕ) (s : ℝ) : ℝ := kernel n (s / n) / n

theorem normalizedKernel_reflection {n : ℕ} (hn : 0 < n) (s : ℝ) :
    normalizedKernel n (2 * Real.pi * n - s) = normalizedKernel n s := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold normalizedKernel
  rw [show (2 * Real.pi * n - s) / (n : ℝ) = 2 * Real.pi - s / n by field_simp]
  rw [kernel_reflection]

theorem normalizedKernel_truncation {n M : ℕ} (hn : 2 ≤ n) (hM : 2 ≤ M) (s : ℝ) :
    |normalizedKernel n s - finiteKernel n (M * n) (weight n) s| ≤ 2 / (M : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let f : ℕ → ℝ := fun k => weight n k * Real.cos ((k : ℝ) * s / n)
  have hf : Summable f := by
    simpa only [f, mul_div_assoc] using summable_weight_cos hn (s / n)
  have hfull : (∑ k ∈ Finset.range (M * n), f k) + (∑' k, f (k + M * n)) =
      kernel n (s / n) := by
    simpa only [kernel, f, mul_div_assoc] using hf.sum_add_tsum_nat_add (M * n)
  have heq : normalizedKernel n s - finiteKernel n (M * n) (weight n) s =
      (∑' k, f (k + M * n)) / n := by
    unfold normalizedKernel finiteKernel
    rw [← hfull]
    dsimp [f]
    ring
  rw [heq, abs_div, abs_of_pos hn0]
  have hw : Summable (fun k => weight n (k + M * n)) :=
    (summable_nat_add_iff (M * n)).mpr (summable_weight hn)
  have hnorm : |∑' k, f (k + M * n)| ≤ ∑' k, weight n (k + M * n) := by
    apply (show ‖∑' k, f (k + M * n)‖ ≤ ∑' k, weight n (k + M * n) from ?_)
    apply tsum_of_norm_bounded hw.hasSum
    intro k
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (weight_nonneg n _)]
    exact mul_le_of_le_one_right (weight_nonneg n _) (Real.abs_cos_le_one _)
  exact (div_le_div_of_nonneg_right hnorm hn0.le).trans (normalized_frequency_tail_le hn hM)

/-- The direct finite-cutoff modulus replaces convergence to a continuous kernel. -/
theorem normalizedKernel_modulus {n M : ℕ} (hn : 2 ≤ n) (hM : 2 ≤ M) (s t : ℝ) :
    |normalizedKernel n s - normalizedKernel n t| ≤
      (M : ℝ) ^ 2 * |s - t| + 4 / (M : ℝ) := by
  let fs := finiteKernel n (M * n) (weight n) s
  let ft := finiteKernel n (M * n) (weight n) t
  have hs := normalizedKernel_truncation hn hM s
  have ht := normalizedKernel_truncation hn hM t
  have hf := weightedKernel_scaled_cutoff hn M s t
  change |normalizedKernel n s - fs| ≤ _ at hs
  change |normalizedKernel n t - ft| ≤ _ at ht
  change |fs - ft| ≤ _ at hf
  rw [abs_sub_comm (normalizedKernel n t) ft] at ht
  calc
    |normalizedKernel n s - normalizedKernel n t| ≤
        |normalizedKernel n s - fs| + |fs - ft| + |ft - normalizedKernel n t| := by
      have h1 := abs_sub_le (normalizedKernel n s) fs (normalizedKernel n t)
      have h2 := abs_sub_le fs ft (normalizedKernel n t)
      linarith
    _ ≤ 2 / (M : ℝ) + (M : ℝ) ^ 2 * |s - t| + 2 / (M : ℝ) :=
      add_le_add (add_le_add hs hf) ht
    _ = (M : ℝ) ^ 2 * |s - t| + 4 / (M : ℝ) := by ring

theorem normalizedKernel_spatial_bound {n : ℕ} (hn : 2 ≤ n) {s : ℝ}
    (hs : |s / (n : ℝ)| ≤ Real.pi) :
    |normalizedKernel n s| * (1 + s ^ 2) ≤ 2 + 3 * Real.pi ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := div_le_div_of_nonneg_right (kernel_spatial_bound hn hs) hn0.le
  unfold normalizedKernel
  rw [abs_div, abs_of_pos hn0]
  convert h using 1 <;> first | rfl | field_simp

end

end Erdos1045.KernelWeights
