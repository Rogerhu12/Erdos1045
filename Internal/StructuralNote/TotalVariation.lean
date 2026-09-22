import EventualExact.QuarticWindowBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The two total-variation estimates required in (9.20). The numerators and
denominators here are the actual cyclic differences, rather than formal Fourier
variables. No sparsity or bound on the largest individual increment is assumed. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.TotalVariation

open Erdos1045 Erdos1045.EventualExact QuarticWindowBound ForwardMaximal

def variation (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  ∑ j ∈ Finset.range n, incrementNorm u j

def window (u : ℕ → ℂ) (j k : ℕ) : ℝ :=
  ∑ r ∈ Finset.range k, incrementNorm u (j + r)

theorem variation_nonneg (n : ℕ) (u : ℕ → ℂ) : 0 ≤ variation n u :=
  Finset.sum_nonneg (fun j _ => incrementNorm_nonneg u j)

theorem window_nonneg (u : ℕ → ℂ) (j k : ℕ) : 0 ≤ window u j k :=
  Finset.sum_nonneg (fun _ _ => incrementNorm_nonneg u _)

theorem window_le_variation {n k : ℕ} (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (j : ℕ) (hk : k ≤ n) : window u j k ≤ variation n u := by
  calc
    _ ≤ ∑ r ∈ Finset.range n, incrementNorm u (j + r) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
        (fun r _ _ => incrementNorm_nonneg u _)
    _ = _ := periodic_sum_shift (incrementNorm u) (incrementNorm_periodic u hu) j

theorem sum_windows {n : ℕ} (u : ℕ → ℂ) (hu : Function.Periodic u n) (k : ℕ) :
    (∑ j ∈ Finset.range n, window u j k) = (k : ℝ) * variation n u := by
  unfold window
  rw [Finset.sum_comm]
  have hs (r : ℕ) : (∑ j ∈ Finset.range n, incrementNorm u (j + r)) = variation n u := by
    simpa only [Nat.add_comm, variation] using
      periodic_sum_shift (incrementNorm u) (incrementNorm_periodic u hu) r
  simp_rw [hs]
  simp

theorem sum_window_squares {n k : ℕ} (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hk : k ≤ n) :
    (∑ j ∈ Finset.range n, window u j k ^ 2) ≤ (k : ℝ) * variation n u ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, variation n u * window u j k := by
      apply Finset.sum_le_sum
      intro j _
      have ha := window_nonneg u j k
      have hb := window_le_variation u hu j hk
      nlinarith
    _ = _ := by rw [← Finset.mul_sum, sum_windows u hu k]; ring

theorem sum_averages {n k : ℕ} (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hk : 0 < k) :
    (∑ j ∈ Finset.range n, average (incrementNorm u) j k) = variation n u := by
  simp only [average_eq]
  change (∑ j ∈ Finset.range n, window u j k / (k : ℝ)) = _
  rw [← Finset.sum_div, sum_windows u hu k]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem sum_average_squares {n k : ℕ} (u : ℕ → ℂ) (hu : Function.Periodic u n)
    (hk : 0 < k) (hkn : k ≤ n) :
    (∑ j ∈ Finset.range n, average (incrementNorm u) j k ^ 2) ≤
      variation n u ^ 2 / k := by
  simp only [average_eq, div_pow]
  change (∑ j ∈ Finset.range n, window u j k ^ 2 / (k : ℝ) ^ 2) ≤ _
  rw [← Finset.sum_div]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    _ ≤ ((k : ℝ) * variation n u ^ 2) / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (sum_window_squares u hu hkn) (sq_nonneg _)
    _ = _ := by field_simp

theorem short_offset_norm_sum {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hs : 2 * k ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    (∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j k‖) ≤ (n : ℝ) / 4 * variation n u := by
  calc
    _ ≤ ∑ j ∈ Finset.range n, (n : ℝ) / 4 * average (incrementNorm u) j k :=
      Finset.sum_le_sum (fun j _ => short_pairRatio_bound hn hk hs u j)
    _ = _ := by rw [← Finset.mul_sum, sum_averages u hu hk]

theorem short_offset_square_sum {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hs : 2 * k ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    (∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j k‖ ^ 2) ≤
      (n : ℝ) ^ 2 / (16 * k) * variation n u ^ 2 := by
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        ((n : ℝ) / 4 * average (incrementNorm u) j k) ^ 2 :=
      Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _)
        (short_pairRatio_bound hn hk hs u j) 2)
    _ = ((n : ℝ) / 4) ^ 2 *
        ∑ j ∈ Finset.range n, average (incrementNorm u) j k ^ 2 := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ ((n : ℝ) / 4) ^ 2 * (variation n u ^ 2 / k) :=
      mul_le_mul_of_nonneg_left (sum_average_squares u hu hk (by omega)) (sq_nonneg _)
    _ = _ := by ring

theorem offset_power_sum_reverse {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) (p : ℕ) :
    (∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j k‖ ^ p) =
      ∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j (n - k)‖ ^ p := by
  have hp := AntipodalLog.pairRatio_periodic hn u hu (n - k)
  calc
    _ = ∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u (k + j) (n - k)‖ ^ p := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.add_comm k j, pairRatio_reverse hn hk u hu j]
    _ = _ := periodic_sum_shift (n := n) (fun j => ‖LocalDFT.pairRatio n u j (n - k)‖ ^ p)
      (fun j => congrArg (fun x : ℂ => ‖x‖ ^ p) (hp j)) k

theorem offset_norm_sum {n k : ℕ} (hn : 0 < n) (hk : 0 < k) (hkn : k < n)
    (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    (∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j k‖) ≤ (n : ℝ) / 4 * variation n u := by
  by_cases hs : 2 * k ≤ n
  · exact short_offset_norm_sum hn hk hs u hu
  · have he := offset_power_sum_reverse hn hkn.le u hu 1
    simp only [pow_one] at he
    rw [he]
    exact short_offset_norm_sum hn (by omega) (by omega) u hu

def pairNormSum (n : ℕ) (u : ℕ → ℂ) : ℝ :=
  (∑ k ∈ Finset.Ico 1 n, ∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j k‖) / 2

theorem pairNormSum_le {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    pairNormSum n u ≤ (n : ℝ) ^ 2 / 8 * variation n u := by
  have hs := Finset.sum_le_sum (s := Finset.Ico 1 n) (fun k hk =>
    offset_norm_sum hn (by have := (Finset.mem_Ico.mp hk).1; omega)
      (Finset.mem_Ico.mp hk).2 u hu)
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hs
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
  rw [hcast] at hs
  dsimp [pairNormSum]
  have ht := variation_nonneg n u
  have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem energyA_le_harmonic {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    LocalDFT.energyA n u ≤ (n : ℝ) ^ 2 / 16 * variation n u ^ 2 *
      ∑ k ∈ Finset.Ico 1 n, (k : ℝ)⁻¹ := by
  let G (k : ℕ) := ∑ j ∈ Finset.range n, ‖LocalDFT.pairRatio n u j k‖ ^ 2
  let B (k : ℕ) := (n : ℝ) ^ 2 / (16 * k) * variation n u ^ 2
  have hB (k : ℕ) : 0 ≤ B k := by dsimp [B]; positivity
  have hp (k : ℕ) (hk : k ∈ Finset.Ico 1 n) : G k ≤ B k + B (n - k) := by
    obtain ⟨hk1, hkn⟩ := Finset.mem_Ico.mp hk
    by_cases hs : 2 * k ≤ n
    · exact (short_offset_square_sum hn (by omega) hs u hu).trans
        (le_add_of_nonneg_right (hB _))
    · have he : G k = G (n - k) := offset_power_sum_reverse hn hkn.le u hu 2
      rw [he]
      exact (short_offset_square_sum hn (by omega) (by omega) u hu).trans
        (le_add_of_nonneg_left (hB _))
  have hreflect : (∑ k ∈ Finset.Ico 1 n, B (n - k)) = ∑ k ∈ Finset.Ico 1 n, B k := by
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] using
      Finset.sum_Ico_reflect B 1 (m := n) (n := n) (by omega)
  have hall := Finset.sum_le_sum hp
  rw [Finset.sum_add_distrib, hreflect] at hall
  have herase : (Finset.range n).erase 0 = Finset.Ico 1 n := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
    omega
  have henergy : LocalDFT.energyA n u = (∑ k ∈ Finset.Ico 1 n, G k) / 2 := by
    simp only [LocalDFT.energyA, Complex.normSq_eq_norm_sq, herase, G]
  rw [henergy]
  calc
    _ ≤ ∑ k ∈ Finset.Ico 1 n, B k := by linarith
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [B]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

theorem energyA_le_log {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ) (hu : Function.Periodic u n) :
    LocalDFT.energyA n u ≤ (n : ℝ) ^ 2 / 16 * variation n u ^ 2 * (1 + Real.log n) := by
  have hH : (∑ k ∈ Finset.Ico 1 n, (k : ℝ)⁻¹) ≤ (harmonic n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      have h := Finset.mem_Ico.mp hk
      exact Finset.mem_Icc.mpr ⟨h.1, h.2.le⟩
    · intro k _ _
      positivity
  exact (energyA_le_harmonic hn u hu).trans
    (mul_le_mul_of_nonneg_left (hH.trans (harmonic_le_one_add_log n)) (by positivity))

end StructuralNote.TotalVariation
