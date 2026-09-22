import Erdos1045.FaberMatrix
import Erdos1045.KernelWeights
import Mathlib.Algebra.BigOperators.Intervals

namespace Erdos1045.FaberFourier

open scoped BigOperators
noncomputable section

def cappedFrequency (n m : ℕ) : ℕ := min m (n - 1)

def crossWeight (n m : ℕ) : ℝ :=
  (cappedFrequency n m : ℝ) * ((cappedFrequency n m : ℝ) + 1) / n

def powerSum {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) : ℂ := ∑ j, character k (θ j)

theorem capped_frequency_sum {n : ℕ} (hn : 0 < n) (m : ℕ) :
    2 * (∑ k ∈ Finset.range n, if k ≤ m then (k : ℝ) else 0) =
      (cappedFrequency n m : ℝ) * ((cappedFrequency n m : ℝ) + 1) := by
  have hset : (Finset.range n).filter (fun k => k ≤ m) =
      Finset.range (min n (m + 1)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hmin : min n (m + 1) = cappedFrequency n m + 1 := by
    unfold cappedFrequency
    omega
  rw [← Finset.sum_filter, hset, hmin]
  have hnat : (∑ k ∈ Finset.range (cappedFrequency n m + 1), k) * 2 =
      cappedFrequency n m * (cappedFrequency n m + 1) := by
    simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two (cappedFrequency n m + 1)
  have hreal : (∑ k ∈ Finset.range (cappedFrequency n m + 1), (k : ℝ)) * 2 =
      (cappedFrequency n m : ℝ) * ((cappedFrequency n m : ℝ) + 1) := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) hnat
    simpa only [Nat.cast_mul, Nat.cast_sum, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using h
  linarith

theorem crossWeight_eq_sum {n : ℕ} (hn : 0 < n) (m : ℕ) :
    crossWeight n m = (2 / (n : ℝ)) *
      (∑ k ∈ Finset.range n, if k ≤ m then (k : ℝ) else 0) := by
  rw [crossWeight, ← capped_frequency_sum hn m]
  ring

/-- The exact coefficient-square identity tying the first-order term to
the kernel of Section 5.2. -/
theorem crossWeight_sq_div {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) :
    crossWeight n m ^ 2 / (m : ℝ) ^ 2 = KernelWeights.weight n (m + 1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  by_cases hmn : m + 1 ≤ n
  · have hs : cappedFrequency n m = m := by unfold cappedFrequency; omega
    rw [KernelWeights.weight_of_le (by omega) hmn]
    simp only [crossWeight, hs, Nat.cast_add, Nat.cast_one]
    field_simp
  · have hs : cappedFrequency n m = n - 1 := by unfold cappedFrequency; omega
    rw [KernelWeights.weight_of_gt hn (by omega)]
    simp only [crossWeight, hs, Nat.add_sub_cancel,
      Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
    field_simp
    ring

theorem crossWeight_nonneg (n m : ℕ) : 0 ≤ crossWeight n m := by
  unfold crossWeight
  positivity

theorem crossWeight_le {n : ℕ} (hn : 0 < n) (m : ℕ) : crossWeight n m ≤ n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (cappedFrequency n m : ℝ) ≤ n := by
    exact_mod_cast (show cappedFrequency n m ≤ n by unfold cappedFrequency; omega)
  have hs1 : (cappedFrequency n m : ℝ) + 1 ≤ n := by
    exact_mod_cast (show cappedFrequency n m + 1 ≤ n by unfold cappedFrequency; omega)
  unfold crossWeight
  apply (div_le_iff₀ hn').2
  exact mul_le_mul hs hs1 (by positivity) (by positivity)

theorem character_add (k m : ℕ) (t : ℝ) :
    character (k + m) t = character k t * character m t := by
  unfold character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_powerSum_le {n : ℕ} (θ : Fin n → ℝ) (k : ℕ) : ‖powerSum θ k‖ ≤ n := by
  unfold powerSum
  calc
    _ ≤ ∑ j, ‖character k (θ j)‖ := norm_sum_le _ _
    _ = n := by simp [norm_character]

end

end Erdos1045.FaberFourier
