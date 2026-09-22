import EventualExact.ForwardIntervalCover
import Mathlib.Algebra.BigOperators.Intervals

/-! A finite one-sided maximal average and its truncated weak estimate. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.ForwardMaximal

open ForwardIntervals

def average (f : ℕ → ℝ) (j k : ℕ) : ℝ := (∑ r ∈ Finset.Ico j (j + k), f r) / k

def maximal {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) (j : ℕ) : ℝ :=
  (Finset.range n).sup' (Finset.nonempty_range_iff.mpr hn.ne') (fun k => average f j (k + 1))

theorem exists_maximal_window {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) (j : ℕ) :
    ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ average f j k = maximal hn f j := by
  obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' (Finset.nonempty_range_iff.mpr hn.ne')
    (fun k => average f j (k + 1))
  exact ⟨k + 1, by omega, by have := Finset.mem_range.mp hk; omega, he.symm⟩

theorem average_le_maximal {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) (j : ℕ)
    {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) : average f j k ≤ maximal hn f j := by
  have he := Finset.le_sup' (fun r => average f j (r + 1))
    (Finset.mem_range.mpr (show k - 1 < n by omega))
  simpa only [Nat.sub_add_cancel hk, maximal] using he

theorem maximal_nonneg {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (j : ℕ) :
    0 ≤ maximal hn f j := by
  obtain ⟨k, hk, _, he⟩ := exists_maximal_window hn f j
  rw [← he, average]
  exact div_nonneg (Finset.sum_nonneg (fun r _ => hf r)) (Nat.cast_nonneg _)

theorem sum_two_periods {n : ℕ} (f : ℕ → ℝ) (hf : Function.Periodic f n) :
    (∑ j ∈ Finset.range (2 * n), f j) = 2 * ∑ j ∈ Finset.range n, f j := by
  rw [two_mul, Finset.sum_range_add]
  have he : (∑ j ∈ Finset.range n, f (n + j)) = ∑ j ∈ Finset.range n, f j := by
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Nat.add_comm] using hf j
  rw [he]
  ring

def truncate (f : ℕ → ℝ) (t : ℝ) (j : ℕ) : ℝ := if t ≤ 2 * f j then f j else 0

theorem truncate_nonneg (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) (t : ℝ) (j : ℕ) :
    0 ≤ truncate f t j := by
  unfold truncate
  split
  · exact hf j
  · exact le_rfl

theorem le_half_add_truncate (f : ℕ → ℝ) {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    f j ≤ t / 2 + truncate f t j := by
  unfold truncate
  split <;> linarith

/-- The truncation estimate needed for strong L2 control. This is proved from
actual window averages; no maximal-operator inequality is an input. -/
theorem truncated_weak_bound {n : ℕ} (hn : 0 < n) (f : ℕ → ℝ)
    (hperiod : Function.Periodic f n) (hf : ∀ j, 0 ≤ f j) {t : ℝ} (ht : 0 ≤ t) :
    t * ((Finset.range n).filter (fun j => t ≤ maximal hn f j)).card ≤
      4 * ∑ j ∈ Finset.range n, truncate f t j := by
  classical
  let S := (Finset.range n).filter (fun j => t ≤ maximal hn f j)
  choose length hpos hlength hmax using exists_maximal_window hn f
  have hlarge (j : ℕ) (hj : j ∈ S) :
      (t / 2) * length j ≤ ∑ k ∈ interval length j, truncate f t k := by
    have htj := (Finset.mem_filter.mp hj).2
    rw [← hmax j, average] at htj
    have hlenR : (0 : ℝ) < length j := by exact_mod_cast hpos j
    have htlen := (le_div_iff₀ hlenR).mp htj
    have hsplit := Finset.sum_le_sum (s := Finset.Ico j (j + length j))
      (fun k _ => le_half_add_truncate f ht k)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico,
      Nat.add_sub_cancel_left, nsmul_eq_mul] at hsplit
    change _ ≤ ∑ k ∈ Finset.Ico j (j + length j), truncate f t k
    linarith
  have hb := weak_bound S length (truncate f t) (Finset.filter_subset _ _)
    (fun j _ => hpos j) (fun j _ => hlength j) (truncate_nonneg f hf t)
    (by positivity : 0 ≤ t / 2) hlarge
  have hp : Function.Periodic (truncate f t) n := by intro j; simp only [truncate, hperiod j]
  rw [sum_two_periods _ hp] at hb
  change t * S.card ≤ _
  linarith

end Erdos1045.EventualExact.ForwardMaximal
