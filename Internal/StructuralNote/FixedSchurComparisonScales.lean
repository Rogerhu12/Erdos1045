import StructuralNote.FixedSchurNearWordAngular

/-! Numerical powers in the common-parameter comparison and finite improvement. -/

namespace StructuralNote.FixedSchurComparisonScales

open Filter
open scoped Topology

theorem inverse_cube_bound {n D : ℝ} (hn : 1 ≤ n) (hD : 0 ≤ D) :
    D / n ^ 3 ≤ D / (n ^ 2 * Real.sqrt n) := by
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hsqrt : Real.sqrt n ≤ n := (Real.sqrt_le_iff).2 ⟨hnpos.le, by nlinarith⟩
  apply div_le_div_of_nonneg_left hD (mul_pos (sq_pos_of_pos hnpos) (Real.sqrt_pos.2 hnpos))
  calc
    _ ≤ n ^ 2 * n := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg n)
    _ = _ := by ring

theorem angle_l2_bound {n B x : ℝ} (hn : 0 < n) (hB : 0 ≤ B)
    (hx : x ≤ 16 * Real.pi ^ 2 * B ^ 2 / n ^ 5) :
    Real.sqrt x ≤ 4 * Real.pi * B / (n ^ 2 * Real.sqrt n) := by
  apply (Real.sqrt_le_iff).2
  refine ⟨by positivity, hx.trans_eq ?_⟩
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  simp only [div_pow, mul_pow, hsq]
  field_simp
  ring

theorem eventually_error_smaller_than_gain {η : ℝ} (hη : 0 < η) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop,
      C / ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ)) < η / (2 * m : ℝ) ^ 2 := by
  have hreal : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  have hlim : Tendsto (fun m : ℕ => C / Real.sqrt (2 * m : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hreal)).const_mul C
  filter_upwards [hlim.eventually (gt_mem_nhds hη), eventually_ge_atTop 1] with m hsmall hm
  have hn : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  have h := div_lt_div_of_pos_right hsmall (sq_pos_of_pos hn)
  exact (show C / ((2 * m : ℝ) ^ 2 * Real.sqrt (2 * m : ℝ)) =
      (C / Real.sqrt (2 * m : ℝ)) / (2 * m : ℝ) ^ 2 by ring).trans_lt h

end StructuralNote.FixedSchurComparisonScales
