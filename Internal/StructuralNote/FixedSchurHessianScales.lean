import StructuralNote.HessianErrorLimits

/-! Uniform vanishing coefficients for the fixed-Schur Hessian estimate. -/

namespace StructuralNote.FixedSchurHessianScales

open Filter CommonDomainRadius HessianErrorLimits
open scoped Topology

theorem logOrder_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => (logOrder n : ℝ) / Real.sqrt n) atTop (𝓝 0) := by
  have ht := logOrder_log_div_power_tendsto (p := 1 / 2) (by norm_num)
  simp only [← Real.sqrt_eq_rpow] at ht
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity)) ?_ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hnum : (logOrder n : ℝ) ≤ (logOrder n : ℝ) * (1 + Real.log n) := by
    nlinarith only [mul_nonneg (Nat.cast_nonneg (logOrder n) : (0 : ℝ) ≤ logOrder n) hlog]
  exact div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)

theorem eventually_logOrder_le_sqrt : ∀ᶠ m : ℕ in atTop,
    (logOrder (2 * m) : ℝ) ≤ Real.sqrt (2 * m : ℝ) := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have ht := (logOrder_div_sqrt_tendsto.comp hnat).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [ht, eventually_ge_atTop 1] with m hm hn
  simp only [Function.comp_def, Nat.cast_mul, Nat.cast_ofNat] at hm
  have hp : (0 : ℝ) < 2 * m := by exact_mod_cast (show 0 < 2 * m by omega)
  exact (div_le_one (Real.sqrt_pos.2 hp)).1 hm.le

theorem constant_div_sqrt_tendsto (C : ℝ) :
    Tendsto (fun m : ℕ => C / Real.sqrt (2 * m : ℝ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun m : ℕ => (2 * m : ℝ)) atTop atTop := by
    simpa only [Function.comp_def] using
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
  simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hreal)).const_mul C

theorem log_ratio_le_inv_sqrt {n L : ℝ} (hn : 0 < n) (hL : L ≤ Real.sqrt n) :
    L / n ≤ 1 / Real.sqrt n := by
  have he : Real.sqrt n / n = 1 / Real.sqrt n := by
    have hs := Real.sq_sqrt hn.le
    have hp := Real.sqrt_pos.2 hn
    field_simp
    nlinarith only [hs]
  exact (div_le_div_of_nonneg_right hL hn.le).trans_eq he

theorem inverse_le_inverse_sqrt {n : ℝ} (hn : 1 ≤ n) :
    1 / n ≤ 1 / Real.sqrt n := by
  have hp : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hs : Real.sqrt n ≤ n := (Real.sqrt_le_iff).2 ⟨hp.le, by nlinarith⟩
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hp) hs

end StructuralNote.FixedSchurHessianScales
