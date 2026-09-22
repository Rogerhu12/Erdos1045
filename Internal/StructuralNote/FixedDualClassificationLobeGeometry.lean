import StructuralNote.FixedDualClassificationArc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Fold any phase into the positive first quadrant. The condition used below
is exactly the fixed distance from the zeros of its cosine, expressed without
choosing a representative modulo a period. -/

namespace StructuralNote.FixedDualClassificationLobeGeometry

open Real Set
open FixedDualClassificationFunctional FixedDualClassificationArc
noncomputable section

theorem folded_cosine (φ : ℝ) : cos (arccos |cos φ|) = |cos φ| :=
  cos_arccos (by linarith [abs_nonneg (cos φ)])
    (abs_le.mpr ⟨neg_one_le_cos φ, cos_le_one φ⟩)

theorem folded_sine (φ : ℝ) : sin (arccos |cos φ|) = |sin φ| := by
  have hs := sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg |cos φ|) (arccos_le_pi |cos φ|)
  have hid := sin_sq_add_cos_sq (arccos |cos φ|)
  rw [folded_cosine, sq_abs] at hid
  nlinarith [sin_sq_add_cos_sq φ, sq_abs (sin φ), abs_nonneg (sin φ)]

theorem folded_angle_mem {φ : ℝ} (haway : sin (3 / 8 : ℝ) ≤ |cos φ|) :
    arccos |cos φ| ∈ Icc 0 (Real.pi / 2 - 3 / 8) := by
  refine ⟨arccos_nonneg _, ?_⟩
  have hbound : 0 ≤ Real.pi / 2 - 3 / 8 := by linarith [pi_gt_three]
  have hcos : cos (Real.pi / 2 - 3 / 8) ≤ cos (arccos |cos φ|) := by
    rw [cos_pi_div_two_sub, folded_cosine]
    exact haway
  by_contra! h
  have hc := strictAntiOn_cos ⟨hbound, by linarith [pi_pos]⟩
    ⟨arccos_nonneg _, arccos_le_pi _⟩ h
  linarith

theorem exists_folded_angle {φ : ℝ} (haway : sin (3 / 8 : ℝ) ≤ |cos φ|) :
    ∃ x ∈ Icc 0 (Real.pi / 2 - 3 / 8),
      cos x = |cos φ| ∧ sin x = |sin φ| :=
  ⟨arccos |cos φ|, folded_angle_mem haway, folded_cosine φ, folded_sine φ⟩

theorem cosine_ne_zero_of_away {φ : ℝ} (haway : sin (3 / 8 : ℝ) ≤ |cos φ|) :
    cos φ ≠ 0 := by
  have hs : 0 < sin (3 / 8 : ℝ) := sin_pos_of_pos_of_lt_pi (by norm_num)
    (by linarith [pi_gt_three])
  exact abs_pos.mp (hs.trans_le haway)

theorem positive_potential_of_phase {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) {r φ : ℝ}
    (hr : (24 : ℝ) / 25 ≤ r)
    (hc : cosineMoment f = r * cos φ) (hs : sineMoment f = r * sin φ)
    (haway : sin (3 / 8 : ℝ) ≤ |cos φ|) (hpos : 0 ≤ cos φ) :
    (1 : ℝ) / 50 < kernelPotential f := by
  apply profile_positive_arc hf hbox hr (folded_angle_mem haway)
  · rw [folded_cosine, abs_of_nonneg hpos]
    exact hc
  · rw [hs, abs_mul, abs_of_nonneg (show 0 ≤ r by linarith), folded_sine]

theorem negative_potential_of_phase {f : ℝ → ℝ} (hf : Measurable f)
    (hbox : ∀ u ∈ Icc 0 Real.pi, |f u| ≤ Real.pi / 2) {r φ : ℝ}
    (hr : (24 : ℝ) / 25 ≤ r)
    (hc : cosineMoment f = r * cos φ) (hs : sineMoment f = r * sin φ)
    (haway : sin (3 / 8 : ℝ) ≤ |cos φ|) (hneg : cos φ ≤ 0) :
    kernelPotential f < -(1 / 50 : ℝ) := by
  apply profile_negative_arc hf hbox hr (folded_angle_mem haway)
  · rw [hc, folded_cosine, abs_of_nonpos hneg]
    ring
  · rw [hs, abs_mul, abs_of_nonneg (show 0 ≤ r by linarith), folded_sine]

end
end StructuralNote.FixedDualClassificationLobeGeometry
