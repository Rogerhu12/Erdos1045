import Erdos1045.CyclicAngles
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace Erdos1045.CyclicAngles

open scoped BigOperators Topology
open Filter
noncomputable section

theorem relativeGap_pos {n : ℕ} (a : Angles n) (hn : 0 < n) (i : ℕ) :
    0 < relativeGap a i := by
  exact div_pos (window_pos a (by norm_num) i) (by positivity)

theorem relativeGap_period {n : ℕ} (a : Angles n) (i : ℕ) :
    relativeGap a (i + n) = relativeGap a i := by rw [relativeGap, window_period]; rfl

theorem periodic_mod {β : Type*} {n : ℕ} (f : ℕ → β)
    (hf : ∀ i, f (i + n) = f i) (i : ℕ) : f i = f (i % n) := by
  have hmul (k j : ℕ) : f (j + k * n) = f j := by
    induction k with
    | zero => simp
    | succ k ih => simpa [Nat.succ_mul, ← Nat.add_assoc, hf] using ih
  calc
    f i = f (i % n + (i / n) * n) := by rw [Nat.mul_comm (i / n), Nat.mod_add_div]
    _ = f (i % n) := hmul _ _

theorem gap_bounds_of_energy_le {n : ℕ} (a : Angles n) (hn : 3 ≤ n)
    {C : ℝ} (hC : energy a ≤ C) (i : ℕ) :
    Real.exp (-C / 2 - 1) ≤ relativeGap a i ∧ relativeGap a i ≤ C + 2 := by
  have hg := energy_ge_gapDefect a hn
  have htotal : LogDefect.total (Finset.range n) (relativeGap a) ≤ C / 2 := by linarith
  have hb := LogDefect.coordinate_bounds_of_total_le (Finset.range n) (relativeGap a)
    (fun j _ => relativeGap_pos a (by omega) j) htotal
    (Finset.mem_range.mpr (Nat.mod_lt i (by omega : 0 < n)))
  rw [periodic_mod (relativeGap a) (relativeGap_period a) i]
  simpa only [neg_div, show (2 : ℝ) * (C / 2) + 2 = C + 2 by ring] using hb

theorem gap_deviation_of_energy_le {n : ℕ} (a : Angles n) (hn : 3 ≤ n)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : energy a ≤ C) :
    LogDefect.deviation (Finset.range n) (relativeGap a) ≤ (2 * C + 6) * C / 2 := by
  have hg := energy_ge_gapDefect a hn
  have htotal : LogDefect.total (Finset.range n) (relativeGap a) ≤ C / 2 := by linarith
  have hb := LogDefect.deviation_le_mul_total (Finset.range n) (relativeGap a)
    (fun j _ => relativeGap_pos a (by omega) j) htotal
  have hm := mul_le_mul_of_nonneg_left htotal (show 0 ≤ 4 * (C / 2) + 6 by positivity)
  nlinarith

theorem window_sum_gaps {n : ℕ} (a : Angles n) (m i : ℕ) :
    window a m i = ∑ j ∈ Finset.range m, window a 1 (i + j) := by
  induction m with
  | zero => simp [window]
  | succ m ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [window, Nat.cast_add, Nat.cast_succ]
      rw [show (i : ℤ) + ((m : ℤ) + 1) = (i : ℤ) + m + 1 by ring]
      ring

theorem window_bounds_of_gap_bounds {n : ℕ} (a : Angles n) (hn : 0 < n)
    {lo hi : ℝ} (hl : ∀ i, lo ≤ relativeGap a i) (hu : ∀ i, relativeGap a i ≤ hi)
    (m i : ℕ) :
    (2 * Real.pi / n) * m * lo ≤ window a m i ∧
      window a m i ≤ (2 * Real.pi / n) * m * hi := by
  have hscale : 0 < 2 * Real.pi / (n : ℝ) := by positivity
  have hlo (j : ℕ) : (2 * Real.pi / n) * lo ≤ window a 1 j := by
    have h := (le_div_iff₀ hscale).mp (hl j)
    simpa [mul_comm] using h
  have hhi (j : ℕ) : window a 1 j ≤ (2 * Real.pi / n) * hi := by
    have h := (div_le_iff₀ hscale).mp (hu j)
    simpa [mul_comm] using h
  rw [window_sum_gaps]
  constructor
  · have h := Finset.sum_le_sum (s := Finset.range m) (fun j _ => hlo (i + j))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  · have h := Finset.sum_le_sum (s := Finset.range m) (fun j _ => hhi (i + j))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem scaled_window_error {n : ℕ} (a : Angles n) (hn : 0 < n) (m i : ℕ) :
    (n : ℝ) * window a m i - 2 * Real.pi * m =
      2 * Real.pi * (∑ j ∈ Finset.range m, (relativeGap a (i + j) - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  have hterm (j : ℕ) : relativeGap a (i + j) =
      ((n : ℝ) / (2 * Real.pi)) * window a 1 (i + j) := by
    unfold relativeGap
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← window_sum_gaps]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp

theorem finite_cauchy_sum (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ s, f i) ^ 2 ≤ s.card * ∑ i ∈ s, (f i) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) f
  simpa using h

theorem sum_window_error_sq {n : ℕ} (a : Angles n) (hn : 0 < n) (m : ℕ) :
    (∑ i ∈ Finset.range n, ((n : ℝ) * window a m i - 2 * Real.pi * m) ^ 2) ≤
      4 * Real.pi ^ 2 * m ^ 2 * LogDefect.deviation (Finset.range n) (relativeGap a) := by
  have hpoint (i : ℕ) : ((n : ℝ) * window a m i - 2 * Real.pi * m) ^ 2 ≤
      4 * Real.pi ^ 2 * m * ∑ j ∈ Finset.range m, (relativeGap a (i + j) - 1) ^ 2 := by
    rw [scaled_window_error a hn]
    have hcs := finite_cauchy_sum (Finset.range m) (fun j => relativeGap a (i + j) - 1)
    simp only [Finset.card_range] at hcs
    nlinarith [mul_le_mul_of_nonneg_left hcs (show 0 ≤ 4 * Real.pi ^ 2 by positivity)]
  have hsum := Finset.sum_le_sum (s := Finset.range n) (fun i _ => hpoint i)
  have hperiod (i : ℕ) : (relativeGap a (i + n) - 1) ^ 2 = (relativeGap a i - 1) ^ 2 := by
    rw [relativeGap_period]
  have hshift (j : ℕ) : (∑ i ∈ Finset.range n, (relativeGap a (i + j) - 1) ^ 2) =
      LogDefect.deviation (Finset.range n) (relativeGap a) := by
    have h := sum_shift_of_drift (fun i => (relativeGap a i - 1) ^ 2) 0
      (fun i => by simpa using hperiod i) j
    simpa [LogDefect.deviation] using h
  simp only [← Finset.mul_sum] at hsum
  rw [Finset.sum_comm] at hsum
  simp_rw [hshift] at hsum
  simpa [mul_assoc, pow_two, mul_comm, mul_left_comm] using hsum

/-- The averaged L1 error of any fixed window is controlled by its L2 error. -/
theorem mean_window_error_sq {n : ℕ} (a : Angles n) (hn : 0 < n) (m : ℕ) :
    ((∑ i ∈ Finset.range n, |(n : ℝ) * window a m i - 2 * Real.pi * m|) / n) ^ 2 ≤
      (4 * Real.pi ^ 2 * m ^ 2 / n) * LogDefect.deviation (Finset.range n) (relativeGap a) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcs := finite_cauchy_sum (Finset.range n)
    (fun i => |(n : ℝ) * window a m i - 2 * Real.pi * m|)
  simp only [sq_abs, Finset.card_range] at hcs
  have hwin := sum_window_error_sq a hn m
  have hmul := mul_le_mul_of_nonneg_left hwin hn0.le
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hn0)).mpr
  have hid : (4 * Real.pi ^ 2 * m ^ 2 / (n : ℝ) *
      LogDefect.deviation (Finset.range n) (relativeGap a)) * (n : ℝ) ^ 2 =
      n * (4 * Real.pi ^ 2 * m ^ 2 * LogDefect.deviation (Finset.range n) (relativeGap a)) := by
    field_simp
  rw [hid]
  linarith

end
end Erdos1045.CyclicAngles
