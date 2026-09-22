import StructuralNote.ExplicitThresholdFunctions
import StructuralNote.ActualRadialGradient
import Mathlib.NumberTheory.Harmonic.Bounds

/-! Explicit Fourier head and tail control for the radial first derivative. -/

namespace StructuralNote.ExplicitGradientThreshold

open Erdos1045 Erdos1045.EventualExact LocalGradient
open Erdos1045.ExplicitThreshold
noncomputable section

def headCutoff (C ε : ℝ) : ℕ := ⌈32 * |C| / ε ^ 2⌉₊ + 1

def pairTolerance (C ε : ℝ) : ℝ := min (1 / 2) (ε / (4 * headCutoff C ε))

theorem headCutoff_pos (C ε : ℝ) : 0 < headCutoff C ε := by
  unfold headCutoff
  omega

theorem pairTolerance_pos {C ε : ℝ} (hε : 0 < ε) : 0 < pairTolerance C ε := by
  unfold pairTolerance
  exact lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num)
    (by exact_mod_cast headCutoff_pos C ε)))

theorem harmonic_le_cast {K : ℕ} (hK : 0 < K) : (harmonic K : ℝ) ≤ K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  exact (harmonic_le_one_add_log K).trans
    (by linarith only [Real.log_le_sub_one_of_pos hKR])

theorem tail_small {C ε : ℝ} (hε : 0 < ε) :
    2 * Real.sqrt (2 * |C|) * Real.sqrt (1 / (headCutoff C ε : ℝ)) < ε / 2 := by
  have hK : (0 : ℝ) < headCutoff C ε := by exact_mod_cast headCutoff_pos C ε
  have hceil := Nat.le_ceil (32 * |C| / ε ^ 2)
  have hbound : 32 * |C| / ε ^ 2 < (headCutoff C ε : ℝ) := by
    simp only [headCutoff, Nat.cast_add, Nat.cast_one]
    linarith only [hceil]
  have hnum := (div_lt_iff₀ (sq_pos_of_pos hε)).mp hbound
  have hden : 32 * |C| / (headCutoff C ε : ℝ) < ε ^ 2 :=
    (div_lt_iff₀ hK).mpr (by nlinarith only [hnum])
  have hs := Real.sq_sqrt (show 0 ≤ 2 * |C| by positivity)
  have ht := Real.sq_sqrt (show 0 ≤ 1 / (headCutoff C ε : ℝ) by positivity)
  have heq : (2 * Real.sqrt (2 * |C|) * Real.sqrt (1 / (headCutoff C ε : ℝ))) ^ 2 =
      8 * |C| / (headCutoff C ε : ℝ) := by
    rw [mul_pow, mul_pow, hs, ht]
    ring
  have hsq : (2 * Real.sqrt (2 * |C|) * Real.sqrt (1 / (headCutoff C ε : ℝ))) ^ 2 <
      (ε / 2) ^ 2 := by
    rw [heq]
    calc
      8 * |C| / (headCutoff C ε : ℝ) = (32 * |C| / (headCutoff C ε : ℝ)) / 4 := by ring
      _ < ε ^ 2 / 4 := div_lt_div_of_pos_right hden (by norm_num)
      _ = (ε / 2) ^ 2 := by ring
  exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq

/-- Every dimension uses the same explicit head cutoff and pairwise tolerance. -/
theorem gradient_small {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n) {η C ε : ℝ} (hε : 0 < ε) (hη : 0 ≤ η)
    (hsmall : η ≤ pairTolerance C ε)
    (hp : ∀ i : Fin n, ∀ h ∈ Finset.Ico 1 n, ‖LocalDFT.pairRatio n u i h‖ ≤ η)
    (hE : LocalDFT.energyA n u ≤ C) : gradientError n u < ε := by
  have hK : 0 < headCutoff C ε := headCutoff_pos C ε
  have hKR : (0 : ℝ) < headCutoff C ε := by exact_mod_cast hK
  have hηhalf := hsmall.trans (min_le_left _ _)
  have hηratio := hsmall.trans (min_le_right _ _)
  have hnear : 2 * η * (harmonic (headCutoff C ε) : ℝ) ≤ ε / 2 := by
    have hh := mul_le_mul_of_nonneg_left (harmonic_le_cast hK) (by positivity : 0 ≤ 2 * η)
    have hb := (le_div_iff₀ (mul_pos (by norm_num) hKR)).mp hηratio
    nlinarith only [hh, hb]
  have hb := gradientError_bound hn hK u hu hη hηhalf hp
  have he : LocalDFT.energyA n u ≤ |C| := hE.trans (le_abs_self C)
  have hr := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_right hr
    (Real.sqrt_nonneg (1 / (headCutoff C ε : ℝ)))
  linarith only [hb, hnear, hm, tail_small (C := C) hε]

end
end StructuralNote.ExplicitGradientThreshold
