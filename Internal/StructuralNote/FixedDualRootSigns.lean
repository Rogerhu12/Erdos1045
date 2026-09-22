import StructuralNote.FixedDualRootGeometry

/-! Actual strict signs on every component complementary to the bracketed roots. -/

namespace StructuralNote.FixedDualRootSigns

open Real Set FixedDualPrimitive FixedDualArithmetic FixedDualTable FixedDualRootGeometry
noncomputable section

theorem witness_sign_constant {b a c t : ℝ}
    (hdom : Ioo a c ⊆ Ioo 0 (Real.pi / 2))
    (hz : ∀ u ∈ Ioo a c, witness b u ≠ 0) (ht : t ∈ Ioo a c) :
    (witness b t < 0 → ∀ u ∈ Ioo a c, witness b u < 0) ∧
    (0 < witness b t → ∀ u ∈ Ioo a c, 0 < witness b u) := by
  have hc : ContinuousOn (witness b) (Ioo a c) := by
    intro u hu
    exact (witness_hasDerivAt b (FixedDualWronskianRoots.interval_sine_cosine (hdom hu)).1.ne').continuousAt.continuousWithinAt
  constructor
  · intro hanchor u hu
    by_contra! hnonneg
    obtain ⟨v, hv, hvz⟩ := isPreconnected_Ioo.intermediate_value ht hu hc ⟨hanchor.le, hnonneg⟩
    exact hz v hv hvz
  · intro hanchor u hu
    by_contra! hnonpos
    obtain ⟨v, hv, hvz⟩ := isPreconnected_Ioo.intermediate_value hu ht hc ⟨hnonpos, hanchor.le⟩
    exact hz v hv hvz

set_option maxHeartbeats 2000000 in
theorem half_signs :
    (∀ u ∈ Ioo (0) (root 0), witness (1 / 2) u < 0) ∧
    (∀ u ∈ Ioo (root 0) (root 1), 0 < witness (1 / 2) u) ∧
    (∀ u ∈ Ioo (root 1) ((Real.pi / 2)), witness (1 / 2) u < 0) ∧
    (∀ u ∈ Ioo (0) (root 2), witness (-(1 / 2)) u < 0) ∧
    (∀ u ∈ Ioo (root 2) (root 3), 0 < witness (-(1 / 2)) u) ∧
    (∀ u ∈ Ioo (root 3) (root 4), witness (-(1 / 2)) u < 0) ∧
    (∀ u ∈ Ioo (root 4) ((Real.pi / 2)), 0 < witness (-(1 / 2)) u) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := half_positions
  obtain ⟨hexp, hexn⟩ := half_exhaustion
  have h0 := (certified_table ⟨0, by omega⟩).1
  have h1 := (certified_table ⟨1, by omega⟩).1
  have h2 := (certified_table ⟨2, by omega⟩).1
  have h3 := (certified_table ⟨3, by omega⟩).1
  have h4 := (certified_table ⟨4, by omega⟩).1
  norm_num [endpointSigns, rows, signedParameter, left, right] at h0 h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hdom : Ioo (0) (root 0) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (0) (root 0), witness (1 / 2) u ≠ 0 := by
      intro u hu huz
      rcases hexp u (hdom hu) huz with he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (6 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h0.1)
  · have hdom : Ioo (root 0) (root 1) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 0) (root 1), witness (1 / 2) u ≠ 0 := by
      intro u hu huz
      rcases hexp u (hdom hu) huz with he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (7 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).2 (by norm_num; exact h0.2)
  · have hdom : Ioo (root 1) ((Real.pi / 2)) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 1) ((Real.pi / 2)), witness (1 / 2) u ≠ 0 := by
      intro u hu huz
      rcases hexp u (hdom hu) huz with he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (80 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h1.2)
  · have hdom : Ioo (0) (root 2) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (0) (root 2), witness (-(1 / 2)) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (9 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h2.1)
  · have hdom : Ioo (root 2) (root 3) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 2) (root 3), witness (-(1 / 2)) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (10 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).2 (by norm_num; exact h2.2)
  · have hdom : Ioo (root 3) (root 4) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 3) (root 4), witness (-(1 / 2)) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (46 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h3.2)
  · have hdom : Ioo (root 4) ((Real.pi / 2)) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 4) ((Real.pi / 2)), witness (-(1 / 2)) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (138 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).2 (by norm_num; exact h4.2)

set_option maxHeartbeats 2000000 in
theorem one_signs :
    (∀ u ∈ Ioo (0) (root 5), witness 1 u < 0) ∧
    (∀ u ∈ Ioo (root 5) (root 6), 0 < witness 1 u) ∧
    (∀ u ∈ Ioo (root 6) ((Real.pi / 2)), witness 1 u < 0) ∧
    (∀ u ∈ Ioo (0) (root 7), witness (-1) u < 0) ∧
    (∀ u ∈ Ioo (root 7) (root 8), 0 < witness (-1) u) ∧
    (∀ u ∈ Ioo (root 8) (root 9), witness (-1) u < 0) ∧
    (∀ u ∈ Ioo (root 9) ((Real.pi / 2)), 0 < witness (-1) u) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := one_positions
  obtain ⟨hexp, hexn⟩ := one_exhaustion
  have h5 := (certified_table ⟨5, by omega⟩).1
  have h6 := (certified_table ⟨6, by omega⟩).1
  have h7 := (certified_table ⟨7, by omega⟩).1
  have h8 := (certified_table ⟨8, by omega⟩).1
  have h9 := (certified_table ⟨9, by omega⟩).1
  norm_num [endpointSigns, rows, signedParameter, left, right] at h5 h6 h7 h8 h9
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hdom : Ioo (0) (root 5) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (0) (root 5), witness 1 u ≠ 0 := by
      intro u hu huz
      rcases hexp u (hdom hu) huz with he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (6 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h5.1)
  · have hdom : Ioo (root 5) (root 6) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 5) (root 6), witness 1 u ≠ 0 := by
      intro u hu huz
      rcases hexp u (hdom hu) huz with he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (7 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).2 (by norm_num; exact h5.2)
  · have hdom : Ioo (root 6) ((Real.pi / 2)) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 6) ((Real.pi / 2)), witness 1 u ≠ 0 := by
      intro u hu huz
      rcases hexp u (hdom hu) huz with he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (88 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h6.2)
  · have hdom : Ioo (0) (root 7) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (0) (root 7), witness (-1) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (12 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h7.1)
  · have hdom : Ioo (root 7) (root 8) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 7) (root 8), witness (-1) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (13 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).2 (by norm_num; exact h7.2)
  · have hdom : Ioo (root 8) (root 9) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 8) (root 9), witness (-1) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (26 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).1 (by norm_num; exact h8.2)
  · have hdom : Ioo (root 9) ((Real.pi / 2)) ⊆ Ioo 0 (Real.pi / 2) := by
      intro u hu
      constructor <;> linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    have hnz : ∀ u ∈ Ioo (root 9) ((Real.pi / 2)), witness (-1) u ≠ 0 := by
      intro u hu huz
      rcases hexn u (hdom hu) huz with he | he | he
      all_goals linarith [hu.1, hu.2, p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three]
    exact (witness_sign_constant hdom hnz (t := (127 : ℝ) / 100)
      (by constructor <;> linarith [p0.1, p0.2, p1.1, p1.2, p2.1, p2.2, p3.1, p3.2, p4.1, p4.2, pi_gt_three])).2 (by norm_num; exact h9.2)

end
end StructuralNote.FixedDualRootSigns
