import EventualExact.CosecantPotential
import EventualExact.CotangentForce
import Erdos1045.CyclicAngles

/-! Quantitative cosecant energy on actual increasing periodic angle lifts.
The nonnegative quantities discarded below are deficits at fixed cyclic lag,
not individual interaction energies. -/

namespace Erdos1045.EventualExact.CyclicCosecant

open scoped BigOperators
open CyclicAngles CosecantPotential
noncomputable section

def lagEnergy {n : ℕ} (a : Angles n) (m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, potential (window a m i)) -
    n * potential (2 * Real.pi * m / n)

def energyDifference {n : ℕ} (a : Angles n) : ℝ :=
  ∑ m ∈ Finset.Ico 1 n, lagEnergy a m

def relativeGaps {n : ℕ} (a : Angles n) : Fin n → ℝ := fun i => relativeGap a i

theorem relativeGaps_pos {n : ℕ} (a : Angles n) (hn : 0 < n) (i : Fin n) :
    0 < relativeGaps a i := by
  unfold relativeGaps relativeGap
  exact div_pos (window_pos a (by norm_num) i) (by positivity)

theorem lagEnergy_nonneg {n m : ℕ} (a : Angles n) (hm0 : 0 < m) (hm : m < n) :
    0 ≤ lagEnergy a m := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum := sum_window a m
  have hrem := Finset.sum_nonneg (s := Finset.range n)
    (fun i _ => remainder_nonneg (reference_mem_arc hm0 hm) (window_mem_arc a hm0 hm i))
  simp only [remainder, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at hrem
  have heq : (n : ℝ) * (2 * Real.pi * m / n) = 2 * Real.pi * m := by field_simp
  rw [heq] at hrem
  simpa [lagEnergy] using hrem

theorem lag_one_ge_gapDefect {n : ℕ} (a : Angles n) (hn : 1 < n) :
    (4 / (3 * (2 * Real.pi / n) ^ 2)) * totalGapDefect (relativeGaps a) ≤
      lagEnergy a 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum := sum_window a 1
  have hs := reference_mem_arc (by norm_num : 0 < (1 : ℕ)) hn
  have hrem := Finset.sum_le_sum (s := Finset.range n)
    (fun i _ => remainder_ge_gapDefect hs (window_mem_arc a (by norm_num) hn i))
  simp only [remainder, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at hrem
  have heq : (n : ℝ) * (2 * Real.pi * (1 : ℕ) / n) = 2 * Real.pi := by
    field_simp
    norm_num
  simp only [Nat.cast_one, mul_one] at hrem heq
  rw [heq] at hrem
  have hdef : totalGapDefect (relativeGaps a) =
      ∑ i ∈ Finset.range n, gapDefect (relativeGap a i) := by
    simp only [totalGapDefect, relativeGaps]
    rw [← Finset.sum_range (fun i : ℕ => gapDefect (relativeGap a i))]
  rw [hdef]
  simpa [relativeGap, lagEnergy] using hrem

theorem lag_complement {n m : ℕ} (a : Angles n) (hm : m ≤ n) :
    lagEnergy a (n - m) = lagEnergy a m := by
  have hwindow (i : ℕ) : window a (n - m) i = 2 * Real.pi - window a m (i + n - m) := by
    have heq : (i : ℤ) + (n - m : ℕ) = (i + n - m : ℕ) := by omega
    have hend : ((i + n - m : ℕ) : ℤ) + (m : ℤ) = (i : ℤ) + n := by omega
    simp only [window, heq, hend, a.period]
    ring
  have hf (i : ℕ) : potential (window a m (i + n)) = potential (window a m i) := by
    rw [window_period]
  have hsum := sum_shift_of_drift (fun i => potential (window a m i)) 0
    (fun i => by simpa using hf i) (n - m)
  have harg : 2 * Real.pi * (n - m : ℕ) / n = 2 * Real.pi - 2 * Real.pi * m / n := by
    by_cases hn : n = 0
    · subst n
      have hp := a.period 0
      simp only [Nat.cast_zero, add_zero] at hp
      linarith [Real.pi_pos]
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      rw [Nat.cast_sub hm]
      field_simp
  unfold lagEnergy
  simp_rw [hwindow, CosecantPotential.potential_complement]
  have hidx (i : ℕ) : i + n - m = i + (n - m) := by omega
  simp_rw [hidx]
  rw [hsum, harg, CosecantPotential.potential_complement]
  simp

/-- Retaining the two neighboring lags gives a quantitative gap estimate. -/
theorem energyDifference_ge_gapDefect {n : ℕ} (a : Angles n) (hn : 3 ≤ n) :
    (8 / (3 * (2 * Real.pi / n) ^ 2)) * totalGapDefect (relativeGaps a) ≤
      energyDifference a := by
  have h₁ : 1 ∈ Finset.Ico 1 n := by simp; omega
  have h₂ : n - 1 ∈ Finset.Ico 1 n := by simp; omega
  have hne : (1 : ℕ) ≠ n - 1 := by omega
  have hsub : {1, n - 1} ⊆ Finset.Ico 1 n := by
    intro m hm
    rcases Finset.mem_insert.mp hm with h | h
    · simpa [h] using h₁
    · simpa only [Finset.mem_singleton.mp h] using h₂
  have hsum : lagEnergy a 1 + lagEnergy a (n - 1) ≤
      ∑ m ∈ Finset.Ico 1 n, lagEnergy a m := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun m hm _ => lagEnergy_nonneg a (by have := (Finset.mem_Ico.mp hm).1; omega)
        (Finset.mem_Ico.mp hm).2)
    simpa [hne] using h
  rw [lag_complement a (by omega : 1 ≤ n)] at hsum
  have hgap := lag_one_ge_gapDefect a (by omega)
  unfold energyDifference
  have heq : (8 / (3 * (2 * Real.pi / n) ^ 2)) * totalGapDefect (relativeGaps a) =
      2 * ((4 / (3 * (2 * Real.pi / n) ^ 2)) * totalGapDefect (relativeGaps a)) := by ring
  rw [heq]
  linarith

theorem gapDefect_le_energyDifference {n : ℕ} (a : Angles n) (hn : 3 ≤ n) :
    totalGapDefect (relativeGaps a) ≤
      (3 * Real.pi ^ 2 / (2 * (n : ℝ) ^ 2)) * energyDifference a := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h := energyDifference_ge_gapDefect a hn
  have hp : 0 < 3 * Real.pi ^ 2 / (2 * (n : ℝ) ^ 2) := by positivity
  have hmul := mul_le_mul_of_nonneg_left h hp.le
  have hc : (3 * Real.pi ^ 2 / (2 * (n : ℝ) ^ 2)) *
      (8 / (3 * (2 * Real.pi / n) ^ 2)) = 1 := by
    field_simp
    ring
  simpa only [← mul_assoc, hc, one_mul] using hmul

end
end Erdos1045.EventualExact.CyclicCosecant
