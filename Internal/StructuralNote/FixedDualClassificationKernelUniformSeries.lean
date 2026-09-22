import StructuralNote.FixedDualClassificationKernelUniformAbel
import StructuralNote.FixedDualClassificationMultiplierLimit
import Mathlib.Topology.MetricSpace.Cauchy

/-! Convergence and uniform tails of the conditionally convergent odd cosine series. -/

namespace StructuralNote.FixedDualClassificationKernelUniformSeries

open Real Finset Filter Erdos1045.EventualExact
open FixedDualClassificationKernelUniformAbel FixedDualClassificationOddSpectrum
open scoped Topology BigOperators
noncomputable section

def seriesPartial (P : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range P, (2 * kernelCoefficient (k : ℤ)) * cos ((2 * k + 1 : ℕ) * t)

theorem coefficient_pos_formula {k : ℕ} (hk : 0 < k) :
    2 * kernelCoefficient (k : ℤ) = 1 / (2 * ((k : ℝ) + 1)) := by
  simp only [kernelCoefficient, naturalKernelCoefficient, if_neg hk.ne']
  field_simp
  norm_num

theorem series_partial_tail {u v : ℕ} (hu : 0 < u) (huv : u ≤ v) {t : ℝ}
    (ht : sin t ≠ 0) :
    |seriesPartial v t - seriesPartial u t| ≤ 1 / (((u : ℝ) + 1) * |sin t|) := by
  have he := sum_range_add_sum_Ico
    (fun k => (2 * kernelCoefficient (k : ℤ)) * cos ((2 * k + 1 : ℕ) * t)) huv
  rw [seriesPartial, seriesPartial, ← he, add_sub_cancel_left]
  rcases huv.eq_or_lt with rfl | huv
  · simp only [Ico_self, sum_empty, abs_zero]
    positivity
  have hb := abel_bound huv (fun k => 2 * kernelCoefficient (k : ℤ))
    (fun k => cos ((2 * k + 1 : ℕ) * t))
    (fun k hk => by rw [coefficient_pos_formula (by have := (mem_Ico.mp hk).1; omega)]; positivity)
    (fun k hk => by
      rw [coefficient_pos_formula (by have := (mem_Ico.mp hk).1; omega),
        coefficient_pos_formula (by have := (mem_Ico.mp hk).1; omega)]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      linarith)
    (fun k _ => odd_cosine_partial_bound k ht)
  rw [coefficient_pos_formula hu] at hb
  calc
    _ ≤ 2 * (1 / (2 * |sin t|)) * (1 / (2 * ((u : ℝ) + 1))) := hb
    _ ≤ 1 / (((u : ℝ) + 1) * |sin t|) := by
      have ha : 0 < |sin t| := abs_pos.mpr ht
      have he : 2 * (1 / (2 * |sin t|)) * (1 / (2 * ((u : ℝ) + 1))) =
          (1 / (((u : ℝ) + 1) * |sin t|)) / 2 := by field_simp
      rw [he]
      linarith [show 0 ≤ 1 / (((u : ℝ) + 1) * |sin t|) by positivity]

theorem tail_bound_tendsto (η : ℝ) :
    Tendsto (fun P : ℕ => 1 / (((P : ℝ) + 1) * η)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const η
  simpa only [zero_div, div_div] using h

theorem series_cauchy {t : ℝ} (ht : sin t ≠ 0) : CauchySeq (fun P => seriesPartial P t) := by
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨P, hP, htail⟩ := ((eventually_gt_atTop 0).and
    ((tail_bound_tendsto |sin t|).eventually (gt_mem_nhds hε))).exists
  refine ⟨P, fun v hv => ?_⟩
  rw [Real.dist_eq]
  exact (series_partial_tail hP hv ht).trans_lt htail

def seriesLimit (t : ℝ) : ℝ :=
  if ht : sin t ≠ 0 then Classical.choose (cauchySeq_tendsto_of_complete (series_cauchy ht)) else 0

theorem series_tendsto {t : ℝ} (ht : sin t ≠ 0) :
    Tendsto (fun P => seriesPartial P t) atTop (𝓝 (seriesLimit t)) := by
  rw [seriesLimit, dif_pos ht]
  exact Classical.choose_spec (cauchySeq_tendsto_of_complete (series_cauchy ht))

theorem series_limit_tail {u : ℕ} (hu : 0 < u) {t : ℝ} (ht : sin t ≠ 0) :
    |seriesLimit t - seriesPartial u t| ≤ 1 / (((u : ℝ) + 1) * |sin t|) := by
  apply le_of_tendsto ((series_tendsto ht).sub_const (seriesPartial u t)).abs
  filter_upwards [eventually_ge_atTop u] with v hv
  exact series_partial_tail hu hv ht

theorem series_limit_tail_uniform {u : ℕ} (hu : 0 < u) {t η : ℝ}
    (hη : 0 < η) (ht : η ≤ |sin t|) :
    |seriesLimit t - seriesPartial u t| ≤ 1 / (((u : ℝ) + 1) * η) := by
  have ht0 : sin t ≠ 0 := abs_pos.mp (hη.trans_le ht)
  exact (series_limit_tail hu ht0).trans
    (one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left ht (by positivity)))

end
end StructuralNote.FixedDualClassificationKernelUniformSeries
