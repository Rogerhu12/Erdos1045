import EventualExact.AntipodalLogRemainder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The relative, cubic Lipschitz estimate for the quartic logarithmic remainder
in §9.5. An absolute quartic bound for two individual configurations would not
give this estimate. The result applies to actual complex chord quotients. -/

noncomputable section
open scoped BigOperators

namespace StructuralNote.RelativeLogRemainder

open Erdos1045.EventualExact

def complexRemainder (z : ℂ) : ℂ := Complex.log (1 - z ^ 2) + z ^ 2

def remainder (z : ℂ) : ℝ := Real.log ‖1 - z ^ 2‖ + (z ^ 2).re

theorem real_part (z : ℂ) : (complexRemainder z).re = remainder z := by
  simp [complexRemainder, remainder, Complex.log_re]

theorem slitPlane_of_small {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    1 - z ^ 2 ∈ Complex.slitPlane := by
  have hh : ‖-(z ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow]
    nlinarith [norm_nonneg z]
  simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh

theorem denominator_lower {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    (3 : ℝ) / 4 ≤ ‖1 - z ^ 2‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (z ^ 2)
  rw [norm_one, norm_pow] at h
  nlinarith [norm_nonneg z]

theorem remainder_hasDerivAt {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    HasDerivAt complexRemainder (-2 * z ^ 3 / (1 - z ^ 2)) z := by
  have hp := (hasDerivAt_id z).pow 2
  have hf := ((hp.const_sub 1).clog (slitPlane_of_small hz)).add hp
  have hden := Complex.slitPlane_ne_zero (slitPlane_of_small hz)
  apply hf.congr_deriv
  dsimp
  field_simp
  ring

theorem derivative_bound {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 2)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖-2 * z ^ 3 / (1 - z ^ 2)‖ ≤ 3 * r ^ 3 := by
  have hd := denominator_lower (hz.trans hrsmall)
  have hdpos : 0 < ‖1 - z ^ 2‖ := by linarith
  rw [norm_div, norm_mul, norm_pow]
  norm_num only [norm_neg, Complex.norm_ofNat]
  apply (div_le_iff₀ hdpos).2
  have hpow := pow_le_pow_left₀ (norm_nonneg z) hz 3
  have hr3 := pow_nonneg hr 3
  have hh := mul_nonneg (pow_nonneg hr 3) (sub_nonneg.mpr hd)
  nlinarith

theorem complex_remainder_difference {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 2)
    {z w : ℂ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖complexRemainder z - complexRemainder w‖ ≤ 3 * r ^ 3 * ‖z - w‖ := by
  have hc : Convex ℝ (Metric.closedBall (0 : ℂ) r) := convex_closedBall _ _
  apply hc.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f' := fun x : ℂ => -2 * x ^ 3 / (1 - x ^ 2))
  · intro x hx
    have hx' : ‖x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    exact (remainder_hasDerivAt (hx'.trans hrsmall)).hasDerivWithinAt
  · intro x hx
    apply derivative_bound hr hrsmall
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hz

theorem remainder_difference {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 2)
    {z w : ℂ} (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    |remainder z - remainder w| ≤ 3 * r ^ 3 * ‖z - w‖ := by
  have ha := Complex.abs_re_le_norm (complexRemainder z - complexRemainder w)
  simp only [Complex.sub_re, real_part] at ha
  exact ha.trans (complex_remainder_difference hr hrsmall hz hw)

theorem sum_remainder_difference {ι : Type*} [Fintype ι] {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 2) (ρ τ : ι → ℂ)
    (hρ : ∀ i, ‖ρ i‖ ≤ r) (hτ : ∀ i, ‖τ i‖ ≤ r) :
    |(∑ i, remainder (ρ i)) - (∑ i, remainder (τ i))| ≤
      3 * r ^ 3 * ∑ i, ‖ρ i - τ i‖ := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun i _ => remainder_difference hr hrsmall (hρ i) (hτ i)))

def pairedRemainder {ι : Type*} [Fintype ι] (ρ : ι → ℂ) : ℝ :=
  (∑ i, Real.log ‖1 + ρ i‖) + (∑ i, ((ρ i) ^ 2).re) / 2

theorem pairedRemainder_eq {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) (ρ : ι → ℂ) (hanti : ∀ i, ρ (e i) = -ρ i)
    (hsmall : ∀ i, ‖ρ i‖ ≤ 1 / 2) :
    pairedRemainder ρ = (∑ i, remainder (ρ i)) / 2 := by
  rw [pairedRemainder, AntipodalLog.sum_antipodal_log e ρ hanti
    (fun i => lt_of_le_of_lt (hsmall i) (by norm_num)), ← add_div]
  simp only [remainder, Finset.sum_add_distrib]

/-- A relative O(r³) estimate, exploiting the same pairing in both configurations. -/
theorem paired_remainder_difference {ι : Type*} [Fintype ι]
    (e : Equiv.Perm ι) {r : ℝ} (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 2)
    (ρ τ : ι → ℂ) (hρanti : ∀ i, ρ (e i) = -ρ i) (hτanti : ∀ i, τ (e i) = -τ i)
    (hρ : ∀ i, ‖ρ i‖ ≤ r) (hτ : ∀ i, ‖τ i‖ ≤ r) :
    |pairedRemainder ρ - pairedRemainder τ| ≤
      (3 / 2 : ℝ) * r ^ 3 * ∑ i, ‖ρ i - τ i‖ := by
  rw [pairedRemainder_eq e ρ hρanti (fun i => (hρ i).trans hrsmall),
    pairedRemainder_eq e τ hτanti (fun i => (hτ i).trans hrsmall),
    ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hh := div_le_div_of_nonneg_right
    (sum_remainder_difference hr hrsmall ρ τ hρ hτ) (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ (3 * r ^ 3 * ∑ i, ‖ρ i - τ i‖) / 2 := hh
    _ = _ := by ring

end StructuralNote.RelativeLogRemainder
