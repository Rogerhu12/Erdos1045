import StructuralNote.FixedDualPrimitive
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The endpoint-sensitive Rolle step used to avoid an extra spurious zero in
the Appendix A count. -/

namespace StructuralNote.FixedDualRolle

open Set Filter
open scoped Topology
noncomputable section

theorem critical_after_zero_of_negative_endpoint {f : ℝ → ℝ} {a e : ℝ}
    (hae : a < e) (hc : ContinuousOn f (Icc a e)) (ha : f a = 0) (he : f e < 0)
    (hd : ∀ᶠ x in 𝓝[<] e, 0 < deriv f x) :
    ∃ c ∈ Ioo a e, deriv f c = 0 := by
  obtain ⟨l, hl, hdl⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hae).mp hd
  have hmono : StrictMonoOn f (Icc l e) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hc.mono (Icc_subset_Icc hl.1 le_rfl))
    intro x hx
    rw [interior_Icc] at hx
    exact hdl hx
  have hfle : f l < f e := hmono ⟨le_rfl, hl.2.le⟩ ⟨hl.2.le, le_rfl⟩ hl.2
  have hfea : f e < f a := by simpa [ha] using he
  obtain ⟨w, hw, hwe⟩ := intermediate_value_Ioo' hl.1
    (hc.mono (Icc_subset_Icc le_rfl hl.2.le)) ⟨hfle, hfea⟩
  obtain ⟨c, hcw, hcz⟩ := exists_deriv_eq_zero (hw.2.trans hl.2)
    (hc.mono (Icc_subset_Icc hw.1.le le_rfl)) hwe
  exact ⟨c, ⟨hw.1.trans hcw.1, hcw.2⟩, hcz⟩

theorem critical_after_zero_of_positive_endpoint {f : ℝ → ℝ} {a e : ℝ}
    (hae : a < e) (hc : ContinuousOn f (Icc a e)) (ha : f a = 0) (he : 0 < f e)
    (hd : ∀ᶠ x in 𝓝[<] e, deriv f x < 0) :
    ∃ c ∈ Ioo a e, deriv f c = 0 := by
  have hdn : ∀ᶠ x in 𝓝[<] e, 0 < deriv (-f) x := by
    filter_upwards [hd] with x hx
    simpa only [deriv.neg, neg_pos] using hx
  obtain ⟨c, hc, hcz⟩ := critical_after_zero_of_negative_endpoint hae hc.neg
    (by simp [ha]) (by simpa using neg_neg_of_pos he) hdn
  exact ⟨c, hc, by simpa only [deriv.neg, neg_eq_zero] using hcz⟩

end
end StructuralNote.FixedDualRolle
