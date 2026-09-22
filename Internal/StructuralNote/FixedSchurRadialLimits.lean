import StructuralNote.FixedSchurRadialAlgebra

/-! Uniform numerical slack between the radial leading coefficient and ten. -/

namespace StructuralNote.FixedSchurRadialLimits

open Filter Erdos1045 Erdos1045.EventualExact
open FixedSchurDomainSmallness HessianErrorLimits CommonDomainRadius
open scoped Topology

noncomputable section

def error (n : ℕ) : ℝ :=
  8 * radius n + 416 * ((logOrder n : ℝ) / n) *
    ((logOrder n : ℝ) * (1 + Real.log n) / n)

theorem error_tendsto : Tendsto error atTop (𝓝 0) := by
  unfold error
  have hR : Tendsto (fun n : ℕ => radius n) atTop (𝓝 0) := by
    simpa only [radius, mul_div_assoc, mul_zero] using
      logOrder_div_tendsto.const_mul 4096
  have hlog : Tendsto
      (fun n : ℕ => (logOrder n : ℝ) * (1 + Real.log n) / n) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (logOrder_log_div_power_tendsto (p := 1) (by norm_num))
  simpa only [mul_zero, add_zero] using
    (hR.const_mul 8).add ((logOrder_div_tendsto.const_mul 416).mul hlog)

theorem eventual_radial_coefficient :
    ∀ᶠ m : ℕ in atTop, Real.pi ^ 2 + error (2 * m) ≤ 10 := by
  have hnat : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    tendsto_atTop_mono (fun m => by omega : ∀ m : ℕ, m ≤ 2 * m) tendsto_id
  have hslack : (0 : ℝ) < 10 - Real.pi ^ 2 := by
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  filter_upwards [(error_tendsto.comp hnat).eventually (gt_mem_nhds hslack)] with m hm
  dsimp only [Function.comp_def] at hm
  linarith

theorem sqrt_log_le_one_add_log {n : ℕ} (hn : 1 ≤ n) :
    Real.sqrt (Real.log (n : ℝ)) ≤ 1 + Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  apply (Real.sqrt_le_iff).2
  exact ⟨by linarith, by nlinarith [sq_nonneg (Real.log (n : ℝ))]⟩

theorem numeric_bound {n : ℕ} (hn : 2 ≤ n) :
    (Real.pi / n) ^ 2 + FixedSchurData.epsilon n * radius n +
      FixedSchurData.epsilon n * (13 * (logOrder n : ℝ)) *
        (4 * (logOrder n : ℝ) * Real.sqrt (Real.log n) / (n : ℝ) ^ 2) ≤
      (Real.pi ^ 2 + error n) / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hε := FixedSchurDomainBounds.epsilon_le hn
  have hR := radius_nonneg (show 0 < n by omega)
  have hs := sqrt_log_le_one_add_log (show 1 ≤ n by omega)
  have hfirst := mul_le_mul_of_nonneg_right hε hR
  have hsecond : FixedSchurData.epsilon n * (13 * (logOrder n : ℝ)) *
      (4 * (logOrder n : ℝ) * Real.sqrt (Real.log n) / (n : ℝ) ^ 2) ≤
      (8 / (n : ℝ) ^ 2) * (13 * (logOrder n : ℝ)) *
        (4 * (logOrder n : ℝ) * (1 + Real.log n) / (n : ℝ) ^ 2) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hε (by positivity)
    · exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (by positivity)) (sq_nonneg _)
    · positivity
    · positivity
  calc
    _ ≤ (Real.pi / n) ^ 2 + (8 / (n : ℝ) ^ 2) * radius n +
        (8 / (n : ℝ) ^ 2) * (13 * (logOrder n : ℝ)) *
          (4 * (logOrder n : ℝ) * (1 + Real.log n) / (n : ℝ) ^ 2) := by
      linarith
    _ = (Real.pi ^ 2 + error n) / (n : ℝ) ^ 2 := by
      unfold error
      field_simp
      ring

end
end StructuralNote.FixedSchurRadialLimits
