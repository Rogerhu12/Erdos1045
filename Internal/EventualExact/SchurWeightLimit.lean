import EventualExact.SchurWeights
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual Schur weight at each fixed positive odd frequency. -/

namespace Erdos1045.EventualExact.SchurWeights

open Filter
open scoped Topology
noncomputable section

theorem weight_eq_sinc {n p : ℕ} (hp : Active n p) :
    weight n p = (1 - ((p : ℝ) + 1) / n) / ((p : ℝ) + 1) *
      Real.sinc (Real.pi / n) ^ 2 /
      (Real.sinc (((p : ℝ) - 1) * Real.pi / n) *
        Real.sinc (((p : ℝ) + 1) * Real.pi / n)) := by
  rcases active_bounds hp with ⟨hn, hp1, _, _⟩
  have ha : Real.pi / n ≠ 0 := by positivity
  have hb : ((p : ℝ) - 1) * Real.pi / n ≠ 0 := by positivity
  have hc : ((p : ℝ) + 1) * Real.pi / n ≠ 0 := by positivity
  rw [weight, if_pos hp, Real.sinc_of_ne_zero ha, Real.sinc_of_ne_zero hb,
    Real.sinc_of_ne_zero hc]
  field_simp [hn.ne', hp1.ne']
  ring

theorem weight_tendsto_fixed {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    Tendsto (fun n : ℕ => weight n p) atTop (𝓝 (1 / ((p : ℝ) + 1))) := by
  have hc (c : ℝ) : Tendsto (fun n : ℕ => c / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat c
  have hs (c : ℝ) : Tendsto (fun n : ℕ => Real.sinc (c / (n : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.sinc_zero] using
      Real.continuous_sinc.continuousAt.tendsto.comp (hc c)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hlim := (((hone.sub (hc ((p : ℝ) + 1))).div_const ((p : ℝ) + 1)).mul
    ((hs Real.pi).pow 2)).div ((hs (((p : ℝ) - 1) * Real.pi)).mul
      (hs (((p : ℝ) + 1) * Real.pi))) (by norm_num : (1 : ℝ) * 1 ≠ 0)
  have hlim' : Tendsto (fun n : ℕ => (1 - ((p : ℝ) + 1) / n) / ((p : ℝ) + 1) *
      Real.sinc (Real.pi / n) ^ 2 / (Real.sinc (((p : ℝ) - 1) * Real.pi / n) *
      Real.sinc (((p : ℝ) + 1) * Real.pi / n))) atTop (𝓝 (1 / ((p : ℝ) + 1))) := by
    simp only [sub_zero, one_pow, mul_one, div_one] at hlim
    convert hlim using 1; rfl
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop (p + 3)] with n hn
  exact (weight_eq_sinc ⟨hp, hp3, hn⟩).symm

end
end Erdos1045.EventualExact.SchurWeights
