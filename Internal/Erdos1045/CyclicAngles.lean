import Erdos1045.CirclePotential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Ordered angles and the finite gap-energy inequality

The angles are an actual increasing periodic lift. Window sum identities are
proved from that periodicity. The energy is the cyclic sum of the ordinary
circle potential; it is not a new unspecified functional.
-/

namespace Erdos1045.CyclicAngles

open scoped BigOperators
open CirclePotential
noncomputable section

structure Angles (n : ℕ) where
  angle : ℤ → ℝ
  increasing : StrictMono angle
  period : ∀ i : ℤ, angle (i + n) = angle i + 2 * Real.pi

def window {n : ℕ} (a : Angles n) (m i : ℕ) : ℝ :=
  a.angle ((i : ℤ) + m) - a.angle i

def relativeGap {n : ℕ} (a : Angles n) (i : ℕ) : ℝ :=
  window a 1 i / (2 * Real.pi / n)

def lagEnergy {n : ℕ} (a : Angles n) (m : ℕ) : ℝ :=
  (∑ i ∈ Finset.range n, potential (window a m i)) -
    n * potential (2 * Real.pi * m / n)

def energy {n : ℕ} (a : Angles n) : ℝ :=
  (∑ m ∈ Finset.Ico 1 n, lagEnergy a m) / 2

theorem window_pos {n : ℕ} (a : Angles n) {m : ℕ} (hm : 0 < m) (i : ℕ) :
    0 < window a m i := by
  apply sub_pos.mpr
  apply a.increasing
  omega

theorem window_lt_two_pi {n : ℕ} (a : Angles n) {m : ℕ} (hm : m < n) (i : ℕ) :
    window a m i < 2 * Real.pi := by
  have h := a.increasing (show (i : ℤ) + m < (i : ℤ) + n by omega)
  rw [a.period] at h
  dsimp [window]
  linarith

theorem window_period {n : ℕ} (a : Angles n) (m i : ℕ) :
    window a m (i + n) = window a m i := by
  simp only [window, Nat.cast_add]
  rw [show (i : ℤ) + n + m = ((i : ℤ) + m) + n by ring, a.period, a.period]
  ring

/-- Summation over one period, including a possible affine drift. -/
theorem sum_shift_of_drift {n : ℕ} (f : ℕ → ℝ) (c : ℝ)
    (hf : ∀ i, f (i + n) = f i + c) (m : ℕ) :
    (∑ i ∈ Finset.range n, f (i + m)) = (∑ i ∈ Finset.range n, f i) + m * c := by
  have h₁ := Finset.sum_range_add f n m
  have h₂ := Finset.sum_range_add f m n
  have htail : (∑ i ∈ Finset.range m, f (n + i)) =
      (∑ i ∈ Finset.range m, f i) + m * c := by
    simp_rw [Nat.add_comm n, hf]
    simp [Finset.sum_add_distrib]
  rw [htail] at h₁
  rw [Nat.add_comm m n] at h₂
  have hswap : (∑ i ∈ Finset.range n, f (m + i)) =
      ∑ i ∈ Finset.range n, f (i + m) := by simp [Nat.add_comm]
  rw [hswap] at h₂
  linarith

theorem sum_window {n : ℕ} (a : Angles n) (m : ℕ) :
    (∑ i ∈ Finset.range n, window a m i) = 2 * Real.pi * m := by
  have h := sum_shift_of_drift (fun i : ℕ => a.angle i) (2 * Real.pi)
    (fun i => by simpa using a.period (i : ℤ)) m
  simp only [window, ← Nat.cast_add, Finset.sum_sub_distrib]
  linarith

theorem reference_mem_arc {n m : ℕ} (hm0 : 0 < m) (hm : m < n) :
    2 * Real.pi * m / n ∈ arc := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (hm0.trans hm)
  have hm' : (m : ℝ) < n := by exact_mod_cast hm
  constructor
  · positivity
  · apply (div_lt_iff₀ hn).mpr
    nlinarith [Real.pi_pos]

theorem window_mem_arc {n m : ℕ} (a : Angles n) (hm0 : 0 < m) (hm : m < n) (i : ℕ) :
    window a m i ∈ arc := ⟨window_pos a hm0 i, window_lt_two_pi a hm i⟩

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
    2 * LogDefect.total (Finset.range n) (relativeGap a) ≤ lagEnergy a 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum := sum_window a 1
  have hs := reference_mem_arc (by norm_num : 0 < (1 : ℕ)) hn
  have hrem := Finset.sum_le_sum (s := Finset.range n)
    (fun i _ => remainder_ge_logDefect hs (window_mem_arc a (by norm_num) hn i))
  simp only [remainder, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hsum] at hrem
  have heq : (n : ℝ) * (2 * Real.pi * (1 : ℕ) / n) = 2 * Real.pi := by field_simp; norm_num
  simp only [Nat.cast_one, mul_one] at hrem
  simp only [Nat.cast_one, mul_one] at heq
  rw [heq] at hrem
  simpa [LogDefect.total, relativeGap, lagEnergy] using hrem

theorem potential_complement (t : ℝ) : potential (2 * Real.pi - t) = potential t := by
  simp only [potential]
  rw [show (2 * Real.pi - t) / 2 = Real.pi - t / 2 by ring,
    Real.sin_pi_sub]

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
  simp_rw [hwindow, potential_complement]
  have hidx (i : ℕ) : i + n - m = i + (n - m) := by omega
  simp_rw [hidx]
  rw [hsum, harg, potential_complement]
  simp

/-- Lemma 2.3, proved by retaining the two adjacent directed lags. -/
theorem energy_ge_gapDefect {n : ℕ} (a : Angles n) (hn : 3 ≤ n) :
    2 * LogDefect.total (Finset.range n) (relativeGap a) ≤ energy a := by
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
  unfold energy
  linarith

end
end Erdos1045.CyclicAngles
