import StructuralNote.FixedDualClassificationKernelUniformIdentification
import StructuralNote.FixedDualClassificationKernelSignsPropagation

/-! Actual finite-kernel convergence away from the singular endpoints and at sampled fixed angles. -/

namespace StructuralNote.FixedDualClassificationKernelUniformFinal

open Real Filter Set Erdos1045.EventualExact
open FixedDualPrimitive FixedDualClassificationKernel FixedDualClassificationKernelSignsPropagation
open FixedDualClassificationKernelUniformConvergence FixedDualClassificationKernelUniformIdentification
open scoped Topology
noncomputable section

theorem uniform_grid_kernel {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ r : ℕ, ∀ t ∈ Set.Ioo 0 Real.pi,
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) → η ≤ |sin t| →
      |finiteKernel (2 * m) t - kernel t| < ε := by
  obtain ⟨N, hN⟩ := uniform_grid_series_limit hη hε
  refine ⟨N, fun m hm r t ht hg hs => ?_⟩
  rw [← seriesLimit_eq_kernel ht]
  exact hN m hm r t hg hs

theorem sine_lower_on_compact {δ t : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi / 2)
    (ht : t ∈ Set.Icc δ (Real.pi - δ)) : sin δ ≤ |sin t| := by
  have ht0 : 0 < t := hδ.trans_le ht.1
  have htπ : t < Real.pi := by linarith [ht.2]
  rw [abs_of_pos (sin_pos_of_pos_of_lt_pi ht0 htπ)]
  by_cases hhalf : t ≤ Real.pi / 2
  · exact sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) hhalf ht.1
  · have h := sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos] : -(Real.pi / 2) ≤ δ)
      (show Real.pi - t ≤ Real.pi / 2 by linarith) (show δ ≤ Real.pi - t by linarith [ht.2])
    simpa only [sin_pi_sub] using h

theorem uniform_grid_kernel_on_compact {δ ε : ℝ} (hδ : 0 < δ)
    (hδπ : δ ≤ Real.pi / 2) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ r : ℕ, ∀ t ∈ Set.Icc δ (Real.pi - δ),
      (2 * m : ℕ) * t = (r : ℝ) * (2 * Real.pi) →
      |finiteKernel (2 * m) t - kernel t| < ε := by
  have hsin := sin_pos_of_pos_of_lt_pi hδ (by linarith [pi_pos])
  obtain ⟨N, hN⟩ := uniform_grid_kernel hsin hε
  refine ⟨N, fun m hm r t ht hg => ?_⟩
  exact hN m hm r t ⟨hδ.trans_le ht.1, by linarith [ht.2]⟩ hg
    (sine_lower_on_compact hδ hδπ ht)

theorem grid_kernel_tendsto {r : ℕ → ℕ} {t : ℕ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 Real.pi) (ht : Tendsto t atTop (𝓝 θ))
    (hgrid : ∀ᶠ m : ℕ in atTop, (2 * m : ℕ) * t m = (r m : ℝ) * (2 * Real.pi)) :
    Tendsto (fun m => finiteKernel (2 * m) (t m)) atTop (𝓝 (kernel θ)) := by
  have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have heta : 0 < sin θ / 2 := half_pos hs
  have hinterior := ht.eventually (isOpen_Ioo.mem_nhds hθ)
  have hsin : ∀ᶠ m in atTop, sin θ / 2 ≤ |sin (t m)| := by
    have hc := ((continuous_abs.comp continuous_sin).continuousAt.tendsto.comp ht)
    apply hc.eventually
    dsimp only [Function.comp_apply]
    rw [abs_of_pos hs]
    exact le_mem_nhds (by linarith)
  have hzero : Tendsto (fun m => finiteKernel (2 * m) (t m) - kernel (t m)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := uniform_grid_kernel heta hε
    filter_upwards [eventually_ge_atTop N, hinterior, hsin, hgrid] with m hm hti hsi hgi
    rw [Real.dist_eq, sub_zero]
    exact hN m hm (r m) (t m) hti hgi hsi
  have h := hzero.add ((kernel_continuousAt hθ).tendsto.comp ht)
  simpa only [Function.comp_apply, zero_add, sub_add_cancel] using h

def sampleIndex (m : ℕ) (θ : ℝ) : ℕ := ⌊(θ / Real.pi) * (m : ℝ)⌋₊

def sampleAngle (m : ℕ) (θ : ℝ) : ℝ :=
  (sampleIndex m θ : ℝ) * (2 * Real.pi / (2 * m : ℕ))

theorem sampleAngle_tendsto {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun m : ℕ => sampleAngle m θ) atTop (𝓝 θ) := by
  have h := ((tendsto_nat_floor_mul_div_atTop (div_nonneg hθ pi_pos.le)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)).mul_const Real.pi
  rw [div_mul_cancel₀ _ pi_pos.ne'] at h
  convert h using 1
  funext m
  unfold sampleAngle sampleIndex
  dsimp only [Function.comp_apply]
  push_cast
  ring

theorem sampleAngle_grid {m : ℕ} (hm : 0 < m) (θ : ℝ) :
    (2 * m : ℕ) * sampleAngle m θ = (sampleIndex m θ : ℝ) * (2 * Real.pi) := by
  have hn : ((2 * m : ℕ) : ℝ) ≠ 0 := by positivity
  unfold sampleAngle
  field_simp

theorem sampled_kernel_tendsto {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    Tendsto (fun m : ℕ => gridKernel m (sampleIndex m θ)) atTop (𝓝 (kernel θ)) := by
  exact grid_kernel_tendsto hθ (sampleAngle_tendsto hθ.1.le)
    ((eventually_gt_atTop 0).mono (fun m hm => sampleAngle_grid hm θ))

end
end StructuralNote.FixedDualClassificationKernelUniformFinal
