import StructuralNote.FixedDualClassificationKernelUniformDivergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Uniform convergence of the actual grid kernel to the conditional cosine-series limit. -/

namespace StructuralNote.FixedDualClassificationKernelUniformConvergence

open Real Finset Filter Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationKernelUniformFold
open FixedDualClassificationKernelUniformSeries FixedDualClassificationMultiplierLimit
open FixedDualClassificationOddSpectrum
open scoped Topology BigOperators
noncomputable section

def coefficientError (n P : ℕ) : ℝ :=
  ∑ k ∈ range P, |SchurWeights.weight n (2 * k + 1) - 2 * kernelCoefficient (k : ℤ)|

theorem coefficientError_tendsto (P : ℕ) :
    Tendsto (fun n => coefficientError n P) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (range P) (fun k _ =>
    ((positive_multiplier_tendsto k).sub_const (2 * kernelCoefficient (k : ℤ))).abs)
  simpa only [coefficientError, sub_self, abs_zero, sum_const_zero] using h

theorem head_error_le (n P : ℕ) (t : ℝ) :
    |(∑ k ∈ range P, SchurWeights.weight n (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t)) -
      seriesPartial P t| ≤ coefficientError n P := by
  unfold seriesPartial coefficientError
  rw [← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro k _
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _)

theorem uniform_grid_series_limit {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ r : ℕ, ∀ t : ℝ,
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) → η ≤ |sin t| →
      |finiteKernel (2 * m) t - seriesLimit t| < ε := by
  obtain ⟨P, hP, htail⟩ := ((eventually_gt_atTop 0).and
    ((tail_bound_tendsto η).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)))).exists
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((coefficientError_tendsto P).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 3)))
  refine ⟨max N (2 * P), fun m hm r t hgrid ht => ?_⟩
  have ht0 : sin t ≠ 0 := abs_pos.mp (hη.trans_le ht)
  have hfin := grid_kernel_tail (m := m) (r := r) hP (by omega) hgrid ht0
  have hden : 1 / (((P : ℝ) + 1) * |sin t|) ≤ 1 / (((P : ℝ) + 1) * η) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ht (by positivity))
  have hser := series_limit_tail_uniform hP hη ht
  have hhead := head_error_le (2 * m) P t
  have herr := hN (2 * m) (by omega)
  have h1 := norm_sub_le_norm_sub_add_norm_sub (finiteKernel (2 * m) t)
    (∑ k ∈ range P, SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t))
    (seriesLimit t)
  have h2 := norm_sub_le_norm_sub_add_norm_sub
    (∑ k ∈ range P, SchurWeights.weight (2 * m) (2 * k + 1) * cos ((2 * k + 1 : ℕ) * t))
    (seriesPartial P t) (seriesLimit t)
  simp only [Real.norm_eq_abs] at h1 h2
  rw [abs_sub_comm (seriesPartial P t) (seriesLimit t)] at h2
  linarith

theorem series_tendstoUniformlyOn {η : ℝ} (hη : 0 < η) :
    TendstoUniformlyOn seriesPartial seriesLimit atTop {t : ℝ | η ≤ |sin t|} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [eventually_gt_atTop 0,
    (tail_bound_tendsto η).eventually (gt_mem_nhds hε)] with P hP htail t ht
  rw [Real.dist_eq]
  exact (series_limit_tail_uniform hP hη ht).trans_lt htail

theorem seriesPartial_continuous (P : ℕ) : Continuous (seriesPartial P) := by
  unfold seriesPartial
  fun_prop

theorem seriesLimit_continuousAt {t : ℝ} (ht : sin t ≠ 0) : ContinuousAt seriesLimit t := by
  have hη : 0 < |sin t| / 2 := half_pos (abs_pos.mpr ht)
  have hc := (series_tendstoUniformlyOn hη).continuousOn
    (Filter.Eventually.frequently (Filter.Eventually.of_forall
      (fun P => (seriesPartial_continuous P).continuousOn)))
  apply hc.continuousAt
  have hcont : Tendsto (fun x : ℝ => |sin x|) (𝓝 t) (𝓝 |sin t|) :=
    (continuous_abs.comp continuous_sin).continuousAt
  exact hcont.eventually (le_mem_nhds (by linarith : |sin t| / 2 < |sin t|))

end
end StructuralNote.FixedDualClassificationKernelUniformConvergence
