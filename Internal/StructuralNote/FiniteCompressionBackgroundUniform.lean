import StructuralNote.FiniteCompressionArcPartition
import StructuralNote.FiniteCompressionKernelGeometry
import StructuralNote.FixedDualClassificationFinite
import StructuralNote.SolTerminalActualGain

/-! The background drop from an explicit half-circle arc decomposition.
All kernel signs, monotonicity, and uniform margins are discharged. The
remaining data describe actual sites, exterior signs, and angular separations. -/

namespace StructuralNote.FiniteCompressionBackgroundUniform

open Real Filter Finset Erdos1045.EventualExact FourierMultiplier FiniteBox
open FiniteCompressionConvolutionBase FiniteCompressionArcPartition
open FiniteCompressionKernelGeometry FiniteCompressionRanked FiniteCompressionEnergy
open FixedDualClassificationFinite SolTerminalActualGain
open scoped Topology
noncomputable section

/-- One half-circle contains a fixed descending jump, an uncertain ascending
arc, and an uncertain descending arc. No variation bound is imposed inside
either uncertain arc. Indices are unwrapped natural numbers. -/
structure BackgroundArcs {m : ℕ} (hm : 0 < m) (b : Fin (2 * m) → ℝ) (j : ℕ) where
  start : ℕ
  jump : ℕ
  left₁ : ℕ
  right₁ : ℕ
  left₂ : ℕ
  right₂ : ℕ
  start_le : start ≤ jump
  jump_lt : jump < left₁
  first_nonempty : left₁ ≤ right₁
  separated : right₁ < left₂
  second_nonempty : left₂ ≤ right₂
  last_lt : right₂ < start + m
  outside : ∀ s ∈ Ico start (start + m), s ≠ jump →
    s ∉ Icc left₁ right₁ → s ∉ Icc left₂ right₂ →
    sequence hm b (s + 1) = sequence hm b s
  jump_left : sequence hm b jump = amplitude (2 * m)
  jump_right : sequence hm b (jump + 1) = -amplitude (2 * m)
  first_left : sequence hm b left₁ = -amplitude (2 * m)
  first_right : sequence hm b (right₁ + 1) = amplitude (2 * m)
  second_left : sequence hm b left₂ = amplitude (2 * m)
  second_right : sequence hm b (right₂ + 1) = -amplitude (2 * m)
  jump_le_site : jump ≤ j
  near_angle : compressionAngle m (j - jump) ≤ Real.pi / 12
  site_le_first : j ≤ left₁
  first_angle_lo : Real.pi / 4 ≤ compressionAngle m (left₁ - j)
  first_angle_hi : compressionAngle m (right₁ - j) ≤ 5 * Real.pi / 12
  second_le_antipode : right₂ ≤ j + m
  second_angle_lo : Real.pi / 4 ≤ compressionAngle m (j + m - right₂)
  second_angle_hi : compressionAngle m (j + m - left₂) ≤ 5 * Real.pi / 12

theorem eventually_background_drop : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (b : Fin (2 * m) → ℝ),
      b ∈ Q hm → ∀ j : ℕ, BackgroundArcs hm b j →
      c / (2 * m : ℕ) ≤ operator (2 * m) b (site hm j) -
        operator (2 * m) b (site hm (j + 1)) := by
  obtain ⟨δ, hδ, hevent⟩ := eventually_kernelAt_geometry
  refine ⟨8 * δ, by positivity, ?_⟩
  filter_upwards [hevent] with m hkernel hm b hb j arcs
  have hforward := hkernel.1 j arcs.left₁ arcs.right₁ arcs.site_le_first
    arcs.first_nonempty arcs.first_angle_lo arcs.first_angle_hi
  have hbackward := hkernel.2.1 j arcs.left₂ arcs.right₂ arcs.second_nonempty
    arcs.second_le_antipode arcs.second_angle_lo arcs.second_angle_hi
  have hnear := hkernel.2.2 j arcs.jump arcs.jump_le_site arcs.near_angle
  have hA := amplitude_ge_one (show 2 ≤ 2 * m by omega)
  have hg := operator_step_le hm b hb.1 (by linarith : 0 ≤ amplitude (2 * m)) hb.2
    arcs.start_le arcs.jump_lt arcs.first_nonempty arcs.separated arcs.second_nonempty
    arcs.last_lt arcs.outside arcs.jump_left arcs.jump_right arcs.first_left arcs.first_right
    arcs.second_left arcs.second_right hnear hforward.1 hbackward.1 hforward.2
    (hδ.le.trans hbackward.2)
  have hscale : 8 * δ / (2 * m : ℕ) ≤ 8 * amplitude (2 * m) * δ / (2 * m : ℕ) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hA hδ.le]
  linarith

theorem neg_mem_box {m : ℕ} (hm : 0 < m) {A : ℝ} {b : Fin (2 * m) → ℝ}
    (hb : b ∈ box hm A) : -b ∈ box hm A := by
  constructor
  · intro i
    simp only [Pi.neg_apply, hb.1 i]
  · intro i
    simpa only [Pi.neg_apply, abs_neg] using hb.2 i

theorem sub_patch_mem_box {m : ℕ} (hm : 0 < m) (A : ℝ)
    (E : Finset (Fin (2 * m))) (b : Fin (2 * m) → ℝ)
    (hb : b ∈ box hm A) (hE : ∀ i ∈ E, b i = A) : b - patch hm A E ∈ box hm A := by
  have hadd := add_patch_mem_box hm A E (-b) (neg_mem_box hm hb)
    (by intro i hi; simp only [Pi.neg_apply, hE i hi])
  have hneg := neg_mem_box hm hadd
  have he : -(-b + patch hm A E) = b - patch hm A E := by
    funext i
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
    ring
  rwa [he] at hneg

theorem word_background_mem_Q {m : ℕ} (hm : 0 < m) (s : SignPattern hm) (E : Finset ℕ)
    (hpos : ∀ x ∈ E, patternSign s (site hm x) = 1) :
    vertex (amplitude (2 * m)) s - patch hm (amplitude (2 * m)) (gridSites hm E) ∈ Q hm := by
  apply sub_patch_mem_box hm _ _ _ (vertex_mem_box (amplitude_pos (by omega)).le s)
  intro i hi
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hi
  change amplitude (2 * m) * patternSign s (site hm x) = amplitude (2 * m)
  rw [hpos x hx, mul_one]

/-- The exact predecessor-oriented interface needed by the terminal slide. -/
theorem eventually_background_predecessor_drop : ∃ c : ℝ, 0 < c ∧
    ∀ᶠ m : ℕ in atTop, ∀ (hm : 0 < m) (b : Fin (2 * m) → ℝ),
      b ∈ Q hm → ∀ k : ℕ, 0 < k → BackgroundArcs hm b (k - 1) →
      c / (2 * m : ℕ) ≤ operator (2 * m) b (site hm (k - 1)) -
        operator (2 * m) b (site hm k) := by
  obtain ⟨c, hc, hevent⟩ := eventually_background_drop
  refine ⟨c, hc, ?_⟩
  filter_upwards [hevent] with m h hm b hb k hk arcs
  simpa only [Nat.sub_add_cancel hk] using h hm b hb (k - 1) arcs

end
end StructuralNote.FiniteCompressionBackgroundUniform
