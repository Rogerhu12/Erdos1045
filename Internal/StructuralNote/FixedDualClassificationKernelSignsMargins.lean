import StructuralNote.FixedDualClassificationKernelSignsTransfer

/-! A fixed negative margin on the cross-interaction interval, from a single negative anchor. -/

namespace StructuralNote.FixedDualClassificationKernelSignsMargins

open Real Filter Set Erdos1045.EventualExact
open FixedDualPrimitive FixedDualClassificationKernelSignsPropagation
open FixedDualClassificationKernelUniformFinal FixedDualClassificationKernelSignsTransfer
open FixedDualClassificationRecurrenceWronskian
open scoped Topology
noncomputable section

theorem eventually_negative_margin_on_interval {θ α β : ℝ}
    (hθ : 0 < θ) (hθα : θ < α) (hαβ : α ≤ β) (hβ : β < Real.pi / 2)
    (hK : kernel θ < 0) : ∃ c : ℝ, 0 < c ∧ ∀ᶠ m : ℕ in atTop,
      ∀ r : ℕ, α ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
        (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ β → gridKernel m r ≤ -c := by
  have hcβ : 0 < cos β := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], hβ⟩
  refine ⟨-(kernel θ / 2) * cos β, mul_pos (by linarith) hcβ, ?_⟩
  have hθπ : θ ∈ Set.Ioo 0 Real.pi := ⟨hθ, by linarith [pi_pos]⟩
  have hhalf : kernel θ < kernel θ / 2 := by linarith
  filter_upwards [eventually_gt_atTop 0,
    (sampled_kernel_tendsto hθπ).eventually (gt_mem_nhds hhalf)] with m hm hKm r hlo hhi
  have hsr := sampleIndex_le_of_lt_angle hm hθ.le (hθα.trans_le hlo)
  have hrm := index_le_middle_of_angle_lt hm (hhi.trans_lt hβ)
  have hKs : gridKernel m (sampleIndex m θ) < 0 := by linarith
  have hKr := negative_suffix hm hsr hrm hKs
  have hcr := grid_cosine_pos hm (r := r) (by omega)
  have hcs := grid_cosine_pos hm (r := sampleIndex m θ) (by omega)
  have hratio := ratio_antitone hm (R := (m - 1) / 2) (by omega) hsr hrm
  have hcross := (div_le_div_iff₀ hcr hcs).mp hratio
  change gridKernel m r * cos ((sampleIndex m θ : ℝ) * (2 * Real.pi / (2 * m : ℕ))) ≤
    gridKernel m (sampleIndex m θ) * cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) at hcross
  have hcos : cos β ≤ cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) :=
    cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [pi_pos]) hhi
  calc
    gridKernel m r ≤ gridKernel m r *
        cos ((sampleIndex m θ : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := by
      nlinarith [cos_le_one ((sampleIndex m θ : ℝ) * (2 * Real.pi / (2 * m : ℕ)))]
    _ ≤ gridKernel m (sampleIndex m θ) * cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) := hcross
    _ ≤ (kernel θ / 2) * cos ((r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) :=
      mul_le_mul_of_nonneg_right hKm.le hcr.le
    _ ≤ (kernel θ / 2) * cos β := mul_le_mul_of_nonpos_left hcos (by linarith)
    _ = _ := by ring

end
end StructuralNote.FixedDualClassificationKernelSignsMargins
