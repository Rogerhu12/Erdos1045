import Erdos1045.RegularComparison
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Closing the scalar sine expansion

The cubic sine remainder is the standard estimate in mathlib. The logarithmic
limit follows by squeezing between `1 - 1/t` and `t - 1` for `log t`.
-/

namespace Erdos1045.ClosedSeries

open Filter
open scoped Topology
noncomputable section

theorem sine_cubic_ratio_tendsto :
    Tendsto (fun x : ℝ => (x - Real.sin x) / x ^ 3) (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlo : Tendsto (fun x : ℝ => 1 / 6 - x ^ 2 / 100) (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
    simpa using ((hx.pow 2).div_const 100).const_sub (1 / 6 : ℝ)
  have hhi : Tendsto (fun x : ℝ => 1 / 6 + x ^ 2 / 100) (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
    simpa using ((hx.pow 2).div_const 100).const_add (1 / 6 : ℝ)
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x ∧ x ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x hxp hx1
    exact ⟨hxp, hx1.le⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [hsmall] with x hx
    have h := (abs_le.mp (Real.sin_bound (x := x) (by simpa only [abs_of_pos hx.1] using hx.2))).2
    rw [abs_of_pos hx.1] at h
    apply (le_div_iff₀ (pow_pos hx.1 3)).2
    nlinarith
  · filter_upwards [hsmall] with x hx
    have h := (abs_le.mp (Real.sin_bound (x := x) (by simpa only [abs_of_pos hx.1] using hx.2))).1
    rw [abs_of_pos hx.1] at h
    apply (div_le_iff₀ (pow_pos hx.1 3)).2
    nlinarith

theorem sine_reciprocal_ratio_tendsto :
    Tendsto (fun x : ℝ => x / Real.sin x) (𝓝[>] 0) (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => Real.sin x / x) (𝓝[>] 0) (𝓝 1) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero_right
  simpa only [inv_div, inv_one] using h.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

theorem log_sine_ratio_tendsto :
    Tendsto (fun x : ℝ => Real.log (x / Real.sin x) / x ^ 2)
      (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
  have hu : Tendsto (fun x : ℝ => ((x - Real.sin x) / x ^ 3) * (x / Real.sin x))
      (𝓝[>] 0) (𝓝 (1 / 6 : ℝ)) := by
    simpa using sine_cubic_ratio_tendsto.mul sine_reciprocal_ratio_tendsto
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x ∧ x ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with x hxp hx1
    exact ⟨hxp, hx1.le⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' sine_cubic_ratio_tendsto hu
  · filter_upwards [hsmall] with x hx
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_gt_three])
    have hl := div_le_div_of_nonneg_right
      (Real.one_sub_inv_le_log_of_pos (div_pos hx.1 hs)) (sq_nonneg x)
    convert hl using 1
    field_simp [hx.1.ne', hs.ne']
  · filter_upwards [hsmall] with x hx
    have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith [Real.pi_gt_three])
    have hl := div_le_div_of_nonneg_right
      (Real.log_le_sub_one_of_pos (div_pos hx.1 hs)) (sq_nonneg x)
    convert hl using 1
    field_simp [hx.1.ne', hs.ne']

theorem sineExpansion : HullGeometry.ClassicalSineExpansion :=
  ⟨log_sine_ratio_tendsto⟩

end
end Erdos1045.ClosedSeries
