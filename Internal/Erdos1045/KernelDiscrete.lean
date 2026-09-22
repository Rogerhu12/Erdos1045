import Erdos1045.KernelAlong
import Erdos1045.KernelRegular

open scoped BigOperators Topology
open Filter

namespace Erdos1045.KernelWeights

noncomputable section
open CyclicAngles

def lagKernelEnergy {n : ℕ} (a : Angles n) (m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, kernel n (window a m i)) / (n : ℝ) ^ 2

def angularKernelEnergy {n : ℕ} (a : Angles n) : ℝ :=
  ∑ m ∈ Finset.range n, lagKernelEnergy a m

theorem lagKernelEnergy_zero {n : ℕ} (a : Angles n) (hn : 0 < n) :
    lagKernelEnergy a 0 = kernel n 0 / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp [lagKernelEnergy, window, pow_two]
  field_simp

theorem lagKernelEnergy_succ {n : ℕ} (a : Angles n) (hn : 0 < n) (q : ℕ) :
    lagKernelEnergy a (q + 1) = rowEnergy n (angleRows a q) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold lagKernelEnergy rowEnergy angleRows normalizedKernel
  simp only [mul_div_cancel_left₀ _ hn0]
  rw [← Finset.sum_div, div_div, pow_two]

theorem lagKernelEnergy_complement {n m : ℕ} (a : Angles n) (hm : m ≤ n) :
    lagKernelEnergy a (n - m) = lagKernelEnergy a m := by
  have hshift := sum_shift_of_drift (n := n)
    (fun i => kernel n (window a (n - m) i)) 0
    (fun i => by rw [window_period]; simp) m
  simp only [mul_zero, add_zero] at hshift
  unfold lagKernelEnergy
  congr 1
  rw [← hshift]
  apply Finset.sum_congr rfl
  intro i hi
  rw [window_complement a hm, kernel_reflection]

theorem sum_fold_odd (f : ℕ → ℝ) (m : ℕ)
    (hs : ∀ k, k ≤ 2 * m + 1 → f (2 * m + 1 - k) = f k) :
    (∑ k ∈ Finset.range (2 * m + 1), f k) =
      f 0 + 2 * ∑ k ∈ Finset.range m, f (k + 1) := by
  have htail : (∑ k ∈ Finset.range m, f (m + k + 1)) = ∑ k ∈ Finset.range m, f (k + 1) := by
    calc
      (∑ k ∈ Finset.range m, f (m + k + 1)) =
          ∑ k ∈ Finset.range m, f (m - 1 - k + 1) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkm := Finset.mem_range.mp hk
        have h := hs (m - 1 - k + 1) (by omega)
        simpa only [show 2 * m + 1 - (m - 1 - k + 1) = m + k + 1 by omega] using h
      _ = ∑ k ∈ Finset.range m, f (k + 1) := Finset.sum_range_reflect (fun k => f (k + 1)) m
  rw [Finset.sum_range_succ', show 2 * m = m + m by omega, Finset.sum_range_add]
  rw [htail]
  ring

theorem angularKernelEnergy_odd (m : ℕ) (a : Angles (2 * m + 1)) :
    angularKernelEnergy a = kernel (2 * m + 1) 0 / (2 * m + 1 : ℕ) +
      2 * triangularEnergy (2 * m + 1) (angleRows a) := by
  rw [angularKernelEnergy, sum_fold_odd _ m (fun k hk => lagKernelEnergy_complement a hk),
    lagKernelEnergy_zero a (by omega), triangularEnergy_odd]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  exact lagKernelEnergy_succ a (by omega) q

theorem angularKernelEnergy_pair_form {n : ℕ} (a : Angles n) :
    angularKernelEnergy a =
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, kernel n (a.angle i - a.angle j)) / (n : ℝ) ^ 2 := by
  unfold angularKernelEnergy lagKernelEnergy
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hper (j : ℕ) : kernel n (a.angle ((j + n : ℕ) : ℤ) - a.angle i) =
      kernel n (a.angle j - a.angle i) + 0 := by
    rw [Nat.cast_add, a.period]
    rw [show a.angle j + 2 * Real.pi - a.angle i = a.angle j - a.angle i + 2 * Real.pi by ring,
      kernel_periodic]
    ring
  have hshift := sum_shift_of_drift (n := n)
    (fun j : ℕ => kernel n (a.angle j - a.angle i)) 0 hper i
  simp only [mul_zero, add_zero] at hshift
  calc
    (∑ j ∈ Finset.range n, kernel n (window a j i)) =
        ∑ j ∈ Finset.range n, kernel n (a.angle ((j + i : ℕ) : ℤ) - a.angle i) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [window, Nat.cast_add]
      rw [add_comm (j : ℤ) (i : ℤ)]
    _ = ∑ j ∈ Finset.range n, kernel n (a.angle j - a.angle i) := hshift
    _ = ∑ j ∈ Finset.range n, kernel n (a.angle i - a.angle j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [show a.angle j - a.angle i = -(a.angle i - a.angle j) by ring, kernel_even]

def regularGridEnergy (n : ℕ) : ℝ :=
  (∑ j ∈ Finset.range n, kernel n (2 * Real.pi * j / n)) / n

theorem regularGridEnergy_odd (m : ℕ) :
    regularGridEnergy (2 * m + 1) = kernel (2 * m + 1) 0 / (2 * m + 1 : ℕ) +
      2 * triangularEnergy (2 * m + 1) regularRows := by
  let n := 2 * m + 1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by dsimp [n]; omega)
  let f : ℕ → ℝ := fun k => kernel n (2 * Real.pi * k / n) / n
  have hsym (k : ℕ) (hk : k ≤ 2 * m + 1) : f (2 * m + 1 - k) = f k := by
    dsimp [f]
    have harg : 2 * Real.pi * ((n - k : ℕ) : ℝ) / n = 2 * Real.pi - 2 * Real.pi * k / n := by
      rw [Nat.cast_sub hk]
      field_simp
      rfl
    change kernel n (2 * Real.pi * ((n - k : ℕ) : ℝ) / n) / n = _
    rw [harg, kernel_reflection]
  have h := sum_fold_odd f m hsym
  unfold regularGridEnergy
  rw [Finset.sum_div]
  change (∑ j ∈ Finset.range (2 * m + 1), f j) = _
  rw [h, triangularEnergy_odd]
  have hf0 : f 0 = kernel n 0 / n := by simp [f]
  rw [hf0]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  change f (q + 1) = rowEnergy (2 * m + 1) (fun _ => 2 * Real.pi * ((q : ℝ) + 1))
  rw [rowEnergy_constant (by omega)]
  simp [f, normalizedKernel, n]

theorem angularKernelEnergy_of_odd {n : ℕ} (hn : Odd n) (a : Angles n) :
    angularKernelEnergy a = kernel n 0 / n + 2 * triangularEnergy n (angleRows a) := by
  obtain ⟨m, hm⟩ := hn
  have heq : n = 2 * m + 1 := by omega
  subst n
  exact angularKernelEnergy_odd m a

theorem regularGridEnergy_of_odd {n : ℕ} (hn : Odd n) :
    regularGridEnergy n = kernel n 0 / n + 2 * triangularEnergy n regularRows := by
  obtain ⟨m, hm⟩ := hn
  have heq : n = 2 * m + 1 := by omega
  subst n
  exact regularGridEnergy_odd m

end

end Erdos1045.KernelWeights
