import StructuralNote.FixedDualClassificationKernelUniformFinal

/-! Transfer of finitely many continuous endpoint values to whole finite-kernel sign intervals. -/

namespace StructuralNote.FixedDualClassificationKernelSignsTransfer

open Real Filter Set Erdos1045.EventualExact
open FixedDualPrimitive FixedDualClassificationKernelSignsPropagation
open FixedDualClassificationKernelUniformFinal
open scoped Topology
noncomputable section

theorem index_le_middle_of_angle_lt {m r : ℕ} (hm : 0 < m)
    (hr : (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) < Real.pi / 2) : r ≤ (m - 1) / 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have he : (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) = (r : ℝ) * Real.pi / m := by
    push_cast
    ring
  rw [he] at hr
  have hh := (div_lt_iff₀ hmR).mp hr
  have hrR : 2 * (r : ℝ) < m := by nlinarith [pi_pos]
  have hrN : 2 * r < m := by exact_mod_cast hrR
  omega

theorem eventually_sampleIndex_le_middle {θ : ℝ} (hθ : θ ∈ Set.Ico 0 (Real.pi / 2)) :
    ∀ᶠ m : ℕ in atTop, sampleIndex m θ ≤ (m - 1) / 2 := by
  filter_upwards [eventually_gt_atTop 0,
    (sampleAngle_tendsto hθ.1).eventually (gt_mem_nhds hθ.2)] with m hm ht
  exact index_le_middle_of_angle_lt hm ht

theorem sampleAngle_le {m : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : 0 ≤ θ) :
    sampleAngle m θ ≤ θ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hf := Nat.floor_le (show 0 ≤ (θ / Real.pi) * (m : ℝ) by positivity)
  unfold sampleAngle sampleIndex
  rw [show (⌊θ / Real.pi * (m : ℝ)⌋₊ : ℝ) * (2 * Real.pi / (2 * m : ℕ)) =
    ((⌊θ / Real.pi * (m : ℝ)⌋₊ : ℝ) * Real.pi) / m by push_cast; ring]
  apply (div_le_iff₀ hmR).mpr
  have hh := mul_le_mul_of_nonneg_right hf pi_pos.le
  have he : θ / Real.pi * (m : ℝ) * Real.pi = θ * m := by field_simp
  rwa [he] at hh

theorem eventually_sampleIndex_strict_order {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop, sampleIndex m a < sampleIndex m b := by
  have hlim := (sampleAngle_tendsto (ha.trans hab.le)).sub (sampleAngle_tendsto ha)
  have hp := hlim.eventually (lt_mem_nhds (sub_pos.mpr hab))
  filter_upwards [eventually_gt_atTop 0, hp] with m hm hpos
  have hb : 0 < 2 * Real.pi / (2 * m : ℕ) := by positivity
  change 0 < (sampleIndex m b : ℝ) * (2 * Real.pi / (2 * m : ℕ)) -
    (sampleIndex m a : ℝ) * (2 * Real.pi / (2 * m : ℕ)) at hpos
  have hr : (sampleIndex m a : ℝ) < sampleIndex m b :=
    (mul_lt_mul_iff_left₀ hb).mp (sub_pos.mp hpos)
  exact_mod_cast hr

theorem le_sampleIndex_of_angle_le {m r : ℕ} (hm : 0 < m) {θ : ℝ}
    (hr : (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ θ) : r ≤ sampleIndex m θ := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply Nat.le_floor
  rw [show (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) = (r : ℝ) * Real.pi / m by push_cast; ring] at hr
  have hh := (div_le_iff₀ hmR).mp hr
  rw [show θ / Real.pi * (m : ℝ) = (θ * m) / Real.pi by ring]
  exact (le_div_iff₀ pi_pos).mpr hh

theorem sampleIndex_le_of_lt_angle {m r : ℕ} (hm : 0 < m) {θ : ℝ} (hθ : 0 ≤ θ)
    (hr : θ < (r : ℝ) * (2 * Real.pi / (2 * m : ℕ))) : sampleIndex m θ ≤ r := by
  have hs := (sampleAngle_le hm hθ).trans_lt hr
  have hb : 0 < 2 * Real.pi / (2 * m : ℕ) := by positivity
  have hi : (sampleIndex m θ : ℝ) < r := (mul_lt_mul_iff_left₀ hb).mp hs
  exact_mod_cast hi.le

theorem eventually_positive_prefix {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hK : 0 < kernel θ) : ∀ᶠ m : ℕ in atTop,
      (∀ r ≤ sampleIndex m θ, 0 < gridKernel m r) ∧
      (∀ r, r + 1 ≤ sampleIndex m θ → gridKernel m (r + 1) < gridKernel m r) := by
  have hfull : θ ∈ Set.Ioo 0 Real.pi := ⟨hθ.1, by linarith [hθ.2, pi_pos]⟩
  filter_upwards [eventually_gt_atTop 0,
    eventually_sampleIndex_le_middle ⟨hθ.1.le, hθ.2⟩,
    (sampled_kernel_tendsto hfull).eventually (lt_mem_nhds hK)] with m hm hmid hpos
  exact ⟨fun r hr => positive_prefix hm hr hmid hpos,
    fun r hr => positive_decreasing_step hm hr hmid hpos⟩

theorem eventually_negative_increasing_suffix {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (hb : b < Real.pi / 2)
    (hsec : kernel a < kernel b) (hneg : kernel b < 0) : ∀ᶠ m : ℕ in atTop,
      (∀ r, sampleIndex m b ≤ r → r ≤ (m - 1) / 2 → gridKernel m r < 0) ∧
      (∀ r, sampleIndex m b ≤ r → r + 1 ≤ (m - 1) / 2 →
        gridKernel m r < gridKernel m (r + 1)) := by
  have ha' : a ∈ Set.Ioo 0 Real.pi := ⟨ha, by linarith [pi_pos]⟩
  have hb' : b ∈ Set.Ioo 0 Real.pi := ⟨ha.trans hab, by linarith [pi_pos]⟩
  have hl := (sampled_kernel_tendsto hb').sub (sampled_kernel_tendsto ha')
  filter_upwards [eventually_gt_atTop 0, eventually_sampleIndex_strict_order ha.le hab,
    (sampled_kernel_tendsto hb').eventually (gt_mem_nhds hneg),
    hl.eventually (lt_mem_nhds (sub_pos.mpr hsec))] with m hm hord hn hp
  have hcmp : gridKernel m (sampleIndex m a) < gridKernel m (sampleIndex m b) := sub_pos.mp hp
  exact ⟨fun r hr hrm => negative_suffix hm hr hrm hn,
    fun r hr hrm => positive_secant_forces_increase hm hord hr hrm (hcmp.trans hn) hcmp⟩

theorem eventually_positive_decreasing_interval {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hK : 0 < kernel θ) : ∀ᶠ m : ℕ in atTop,
      (∀ r : ℕ, (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ θ → 0 < gridKernel m r) ∧
      (∀ r : ℕ, ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ θ →
        gridKernel m (r + 1) < gridKernel m r) := by
  filter_upwards [eventually_gt_atTop 0, eventually_positive_prefix hθ hK] with m hm hs
  exact ⟨fun r hr => hs.1 r (le_sampleIndex_of_angle_le hm hr),
    fun r hr => hs.2 r (le_sampleIndex_of_angle_le hm hr)⟩

theorem eventually_negative_increasing_interval {a b α β : ℝ}
    (ha : 0 < a) (hab : a < b) (hbα : b < α) (hαβ : α ≤ β) (hβ : β < Real.pi / 2)
    (hsec : kernel a < kernel b) (hneg : kernel b < 0) : ∀ᶠ m : ℕ in atTop,
      (∀ r : ℕ, α ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
        (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ β → gridKernel m r < 0) ∧
      (∀ r : ℕ, α ≤ (r : ℝ) * (2 * Real.pi / (2 * m : ℕ)) →
        ((r + 1 : ℕ) : ℝ) * (2 * Real.pi / (2 * m : ℕ)) ≤ β →
        gridKernel m r < gridKernel m (r + 1)) := by
  have hb : b < Real.pi / 2 := lt_of_lt_of_le hbα (hαβ.trans hβ.le)
  filter_upwards [eventually_gt_atTop 0,
    eventually_negative_increasing_suffix ha hab hb hsec hneg] with m hm hs
  constructor
  · intro r hlo hhi
    exact hs.1 r (sampleIndex_le_of_lt_angle hm (ha.trans hab).le (hbα.trans_le hlo))
      (index_le_middle_of_angle_lt hm (hhi.trans_lt hβ))
  · intro r hlo hhi
    exact hs.2 r (sampleIndex_le_of_lt_angle hm (ha.trans hab).le (hbα.trans_le hlo))
      (index_le_middle_of_angle_lt hm (hhi.trans_lt hβ))

end
end StructuralNote.FixedDualClassificationKernelSignsTransfer
