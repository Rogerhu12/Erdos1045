import EventualExact.SchurSpectrum
import Erdos1045.LocalObjective
import Erdos1045.CircleGapQuantitative
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Antipodal cancellation and a quartic remainder for the actual pair logarithms. -/

noncomputable section
open scoped BigOperators

namespace Erdos1045.EventualExact.AntipodalLog

open Complex FourierMultiplier SchurSpectrum

theorem one_add_ne_zero {z : ℂ} (hz : ‖z‖ < 1) : 1 + z ≠ 0 := by
  intro he
  have : z = -1 := by linear_combination he
  simp [this] at hz

theorem scalar_quartic {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    |Real.log ‖1 - z ^ 2‖ + (z ^ 2).re| ≤ ‖z‖ ^ 4 := by
  have hz0 := norm_nonneg z
  have hz2 : ‖-(z ^ 2)‖ ≤ 1 / 2 := by
    rw [norm_neg, norm_pow]
    nlinarith
  have ht := Complex.norm_log_one_add_sub_self_le (lt_of_le_of_lt hz2 (by norm_num))
  have hre := (Complex.abs_re_le_norm (Complex.log (1 + -(z ^ 2)) - -(z ^ 2))).trans ht
  have hinv : (1 - ‖-(z ^ 2)‖)⁻¹ ≤ 2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (show 1 / 2 ≤ 1 - ‖-(z ^ 2)‖ by linarith)
  have hb := mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖-(z ^ 2)‖)
  simp only [sub_neg_eq_add, Complex.add_re, Complex.log_re,
    ← sub_eq_add_neg, norm_neg, norm_pow] at hre hb
  nlinarith [sq_nonneg (‖z‖ ^ 2)]

theorem antipodal_log_identity {z : ℂ} (hz : ‖z‖ < 1) :
    Real.log ‖1 + z‖ + Real.log ‖1 - z‖ = Real.log ‖1 - z ^ 2‖ := by
  have hp := norm_ne_zero_iff.mpr (one_add_ne_zero hz)
  have hm := norm_ne_zero_iff.mpr (one_add_ne_zero (z := -z) (by simpa using hz))
  rw [← Real.log_mul hp (by simpa only [sub_eq_add_neg] using hm), ← norm_mul]
  congr 2
  ring

theorem sum_antipodal_log {ι : Type*} [Fintype ι] (e : Equiv.Perm ι)
    (ρ : ι → ℂ) (hanti : ∀ i, ρ (e i) = -ρ i) (hsmall : ∀ i, ‖ρ i‖ < 1) :
    (∑ i, Real.log ‖1 + ρ i‖) = (∑ i, Real.log ‖1 - (ρ i) ^ 2‖) / 2 := by
  have he : (∑ i, Real.log ‖1 - ρ i‖) = ∑ i, Real.log ‖1 + ρ i‖ := by
    simpa only [hanti, ← sub_eq_add_neg] using Equiv.sum_comp e (fun i => Real.log ‖1 + ρ i‖)
  have hs : (∑ i, Real.log ‖1 + ρ i‖) + (∑ i, Real.log ‖1 - ρ i‖) =
      ∑ i, Real.log ‖1 - (ρ i) ^ 2‖ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => antipodal_log_identity (hsmall i))
  linarith

theorem sum_quartic_bound {ι : Type*} [Fintype ι] (e : Equiv.Perm ι)
    (ρ : ι → ℂ) (hanti : ∀ i, ρ (e i) = -ρ i) (hsmall : ∀ i, ‖ρ i‖ ≤ 1 / 2) :
    |(∑ i, Real.log ‖1 + ρ i‖) + (∑ i, ((ρ i) ^ 2).re) / 2| ≤
      (∑ i, ‖ρ i‖ ^ 4) / 2 := by
  rw [sum_antipodal_log e ρ hanti (fun i => lt_of_le_of_lt (hsmall i) (by norm_num)),
    ← add_div, ← Finset.sum_add_distrib, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => scalar_quartic (hsmall i))

theorem pairRatio_half_period {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u m) (j h : ℕ) :
    LocalDFT.pairRatio (2 * m) u (j + m) h = -LocalDFT.pairRatio (2 * m) u j h := by
  have hw := root_halfTurn hm
  simp only [LocalDFT.pairRatio]
  rw [show j + m + h = (j + h) + m by omega, hu (j + h), hu j,
    pow_add _ (j + h) m, pow_add _ j m, hw]
  simp only [mul_neg_one]
  rw [neg_sub_neg, ← neg_sub (LocalPhase.regularRoot (2 * m) ^ (j + h))
    (LocalPhase.regularRoot (2 * m) ^ j), div_neg]

theorem pairRatio_periodic {n : ℕ} (hn : 0 < n) (u : ℕ → ℂ)
    (hu : Function.Periodic u n) (h : ℕ) :
    Function.Periodic (fun j => LocalDFT.pairRatio n u j h) n := by
  intro j
  simp only [LocalDFT.pairRatio]
  rw [show j + n + h = (j + h) + n by omega, hu (j + h), hu j,
    pow_add _ (j + h) n, pow_add _ j n, LocalDFT.regularRoot_pow hn]
  simp

theorem pairRatio_halfTurn {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u m) (j : Fin (2 * m)) (h : ℕ) :
    LocalDFT.pairRatio (2 * m) u (halfTurn hm j) h =
      -LocalDFT.pairRatio (2 * m) u j h := by
  have hun : Function.Periodic u (2 * m) := by
    intro j
    rw [two_mul, ← Nat.add_assoc, hu, hu]
  have hp := pairRatio_periodic (by omega) u hun h
  change LocalDFT.pairRatio (2 * m) u ((j.val + m) % (2 * m)) h = _
  rw [← CyclicAngles.periodic_mod (fun k => LocalDFT.pairRatio (2 * m) u k h) hp,
    pairRatio_half_period hm u hu]

theorem pair_sum_quartic {m : ℕ} (hm : 0 < m) (u : ℕ → ℂ)
    (hu : Function.Periodic u m) (h : ℕ)
    (hsmall : ∀ j, ‖LocalDFT.pairRatio (2 * m) u j h‖ ≤ 1 / 2) :
    |(∑ j ∈ Finset.range (2 * m), Real.log ‖1 + LocalDFT.pairRatio (2 * m) u j h‖) +
      (∑ j ∈ Finset.range (2 * m), (LocalDFT.pairRatio (2 * m) u j h ^ 2).re) / 2| ≤
      (∑ j ∈ Finset.range (2 * m), ‖LocalDFT.pairRatio (2 * m) u j h‖ ^ 4) / 2 := by
  let e : Equiv.Perm (Fin (2 * m)) :=
    Equiv.ofBijective (halfTurn hm) (SchurLift.halfTurn_involutive hm).bijective
  have he := sum_quartic_bound e (fun j => LocalDFT.pairRatio (2 * m) u j h)
    (fun j => pairRatio_halfTurn hm u hu j h) (fun j => hsmall j)
  rw [← Fin.sum_univ_eq_sum_range (fun j => Real.log ‖1 + LocalDFT.pairRatio (2 * m) u j h‖),
    ← Fin.sum_univ_eq_sum_range (fun j => (LocalDFT.pairRatio (2 * m) u j h ^ 2).re),
    ← Fin.sum_univ_eq_sum_range (fun j => ‖LocalDFT.pairRatio (2 * m) u j h‖ ^ 4)]
  exact he

end Erdos1045.EventualExact.AntipodalLog
