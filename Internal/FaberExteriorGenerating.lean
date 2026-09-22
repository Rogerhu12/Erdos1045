import ConvexFaber
import FaberKernelGenerating
import LaurentExteriorCalculus
import Erdos1045.ClosedGenerating

/-! Full exterior and Fourier versions of the actual Faber generating identity.
These have the same signs, normalization and complete index range as the old
FaberIdentities.generating and generating_summable fields. -/

namespace ExteriorReduction

open Complex Set Metric
open Erdos1045.ExteriorBoundary Erdos1045.ExteriorClassical
noncomputable section

theorem model_faber_generating_hasSum {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0)
    {w : ℂ} (hw : w ∈ exteriorDisk) :
    HasSum (fun k => modelFaberValue q A x k * w⁻¹ ^ k)
      (w * deriv (fun v => A + v * q v⁻¹) w / (A + w * q w⁻¹ - x)) := by
  have hq0 : q 0 ≠ 0 := by simpa using hne 0 (by simp)
  have hs := FaberKernel.kernel_generating_hasSum hq hq0 A x hne
    (inv_mem_disk_of_exterior hw)
  change HasSum _ (geometricKernel q A x w⁻¹) at hs
  rwa [geometricKernel_eq_exterior_derivative hq A x hw] at hs

theorem model_faber_fourier_generating {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0)
    (r : ℝ) (hr : 1 < r) (t : ℝ) :
    Erdos1045.FaberFourier.series
      (fun k => ((1 / r : ℝ) : ℂ) ^ k * modelFaberValue q A x k) t =
      ((r : ℂ) * unit t) * deriv (fun v => A + v * q v⁻¹) ((r : ℂ) * unit t) /
        (A + ((r : ℂ) * unit t) * q (((r : ℂ) * unit t)⁻¹) - x) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hw : (r : ℂ) * unit t ∈ exteriorDisk := by
    simpa [exteriorDisk, norm_mul, norm_unit, abs_of_pos hr0] using hr
  rw [← (model_faber_generating_hasSum hq A x hne hw).tsum_eq]
  unfold Erdos1045.FaberFourier.series
  apply tsum_congr
  intro k
  rw [character_eq_unit_inv_pow]
  push_cast
  simp only [one_div, mul_inv_rev, mul_pow]
  ring

theorem model_faber_generating_summable {q : ℂ → ℂ}
    (hq : AnalyticOnNhd ℂ q (ball 0 1)) (A x : ℂ)
    (hne : ∀ z ∈ ball (0 : ℂ) 1, q z + (A - x) * z ≠ 0)
    (r : ℝ) (hr : 1 < r) :
    Summable (fun k => ‖((1 / r : ℝ) : ℂ) ^ k * modelFaberValue q A x k‖) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hq0 : q 0 ≠ 0 := by simpa using hne 0 (by simp)
  have hz : ((1 / r : ℝ) : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hr0)]
    exact (div_lt_one hr0).mpr hr
  simpa only [modelFaberValue, mul_comm] using
    FaberKernel.kernel_generating_norm_summable hq hq0 A x hne hz

#print axioms model_faber_fourier_generating
#print axioms model_faber_generating_summable

end
end ExteriorReduction
