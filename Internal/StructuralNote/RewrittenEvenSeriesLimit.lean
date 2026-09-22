import StructuralNote.RewrittenBalancedEnergyLimit
import StructuralNote.StrongBoxComparison

/-! The genuine diameter maximum has the balanced spectral-series limit.
Evaluation of that series to logarithms and pi is a separate endpoint. -/

namespace StructuralNote.RewrittenEvenSeriesLimit

open Real Filter Erdos1045.EventualExact
open RewrittenBalancedEnergyLimit StrongBoxComparison SinglePressureEstimate
open scoped Topology
noncomputable section

def logMaximum (m : ℕ) : ℝ :=
  Real.log (M (2 * m) / (2 * m : ℝ) ^ (2 * m))

theorem logMaximum_sub_boxMaximum_tendsto :
    Tendsto (fun m => logMaximum m - boxMaximum m) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have ht : Tendsto (fun m : ℕ =>
      (comparisonConstant + 1000000) / (2 * m : ℝ) ^ 2) atTop (𝓝 0) := by
    have h := ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).pow 2).const_mul
      ((comparisonConstant + 1000000) / 4)
    convert h using 1
    · funext m
      ring
    · ring
  apply squeeze_zero' (Filter.Eventually.of_forall (fun m => norm_nonneg _)) ?_ ht
  obtain ⟨m₀, h₀⟩ := eventual_even_box_absolute_error
  filter_upwards [eventually_ge_atTop m₀] with m hm
  obtain ⟨hmp, hbound⟩ := h₀ m hm
  simpa only [Real.norm_eq_abs, logMaximum, boxMaximum, dif_pos hmp,
    Nat.cast_mul, Nat.cast_ofNat] using hbound

theorem even_log_maximum_tendsto : Tendsto logMaximum atTop (𝓝 limitEnergy) := by
  have h := logMaximum_sub_boxMaximum_tendsto.add boxMaximum_tendsto
  simpa only [sub_add_cancel, zero_add] using h

/-- A limit of the actual supremum, with no sampling or analytic premise. -/
theorem even_normalized_maximum_series_tendsto :
    Tendsto (fun m : ℕ => M (2 * m) / (2 * m : ℝ) ^ (2 * m))
      atTop (𝓝 (Real.exp limitEnergy)) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp even_log_maximum_tendsto
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  dsimp only [Function.comp_apply, logMaximum]
  exact Real.exp_log (div_pos (M_positive (by omega)) (pow_pos (by positivity) _))

end
end StructuralNote.RewrittenEvenSeriesLimit
