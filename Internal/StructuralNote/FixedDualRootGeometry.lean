import StructuralNote.FixedDualTable
import StructuralNote.FixedDualZeroCount

/-! Actual bracketed roots, and exhaustion of the roots for the two fixed witnesses. -/

namespace StructuralNote.FixedDualRootGeometry

open Real Set FixedDualPrimitive FixedDualArithmetic FixedDualTable FixedDualZeroCount
noncomputable section

def root (i : Fin 10) : ℝ := Classical.choose (table_root_exists i)

theorem root_position (i : Fin 10) :
    root i ∈ Ioo (left (rows i) : ℝ) (right (rows i) : ℝ) :=
  (Classical.choose_spec (table_root_exists i)).1

theorem root_zero (i : Fin 10) : witness (signedParameter (rows i)) (root i) = 0 :=
  (Classical.choose_spec (table_root_exists i)).2

theorem half_positions :
    root 0 ∈ Ioo (6 / 100) (7 / 100) ∧ root 1 ∈ Ioo (79 / 100) (80 / 100) ∧
    root 2 ∈ Ioo (9 / 100) (10 / 100) ∧ root 3 ∈ Ioo (45 / 100) (46 / 100) ∧
    root 4 ∈ Ioo (137 / 100) (138 / 100) := by
  have h0 := root_position ⟨0, by omega⟩
  have h1 := root_position ⟨1, by omega⟩
  have h2 := root_position ⟨2, by omega⟩
  have h3 := root_position ⟨3, by omega⟩
  have h4 := root_position ⟨4, by omega⟩
  norm_num [rows, left, right] at h0 h1 h2 h3 h4 ⊢
  exact ⟨h0, h1, h2, h3, h4⟩

theorem one_positions :
    root 5 ∈ Ioo (6 / 100) (7 / 100) ∧ root 6 ∈ Ioo (87 / 100) (88 / 100) ∧
    root 7 ∈ Ioo (12 / 100) (13 / 100) ∧ root 8 ∈ Ioo (25 / 100) (26 / 100) ∧
    root 9 ∈ Ioo (126 / 100) (127 / 100) := by
  have h5 := root_position ⟨5, by omega⟩
  have h6 := root_position ⟨6, by omega⟩
  have h7 := root_position ⟨7, by omega⟩
  have h8 := root_position ⟨8, by omega⟩
  have h9 := root_position ⟨9, by omega⟩
  norm_num [rows, left, right] at h5 h6 h7 h8 h9 ⊢
  exact ⟨h5, h6, h7, h8, h9⟩

theorem half_zeros :
    witness (1 / 2) (root 0) = 0 ∧ witness (1 / 2) (root 1) = 0 ∧
    witness (-(1 / 2)) (root 2) = 0 ∧ witness (-(1 / 2)) (root 3) = 0 ∧
    witness (-(1 / 2)) (root 4) = 0 := by
  have h0 := root_zero ⟨0, by omega⟩
  have h1 := root_zero ⟨1, by omega⟩
  have h2 := root_zero ⟨2, by omega⟩
  have h3 := root_zero ⟨3, by omega⟩
  have h4 := root_zero ⟨4, by omega⟩
  norm_num [rows, signedParameter] at h0 h1 h2 h3 h4 ⊢
  exact ⟨h0, h1, h2, h3, h4⟩

theorem one_zeros :
    witness 1 (root 5) = 0 ∧ witness 1 (root 6) = 0 ∧
    witness (-1) (root 7) = 0 ∧ witness (-1) (root 8) = 0 ∧ witness (-1) (root 9) = 0 := by
  have h5 := root_zero ⟨5, by omega⟩
  have h6 := root_zero ⟨6, by omega⟩
  have h7 := root_zero ⟨7, by omega⟩
  have h8 := root_zero ⟨8, by omega⟩
  have h9 := root_zero ⟨9, by omega⟩
  norm_num [rows, signedParameter] at h5 h6 h7 h8 h9 ⊢
  exact ⟨h5, h6, h7, h8, h9⟩

theorem half_exhaustion :
    (∀ u ∈ Ioo 0 (Real.pi / 2), witness (1 / 2) u = 0 → u = root 0 ∨ u = root 1) ∧
    (∀ u ∈ Ioo 0 (Real.pi / 2), witness (-(1 / 2)) u = 0 →
      u = root 2 ∨ u = root 3 ∨ u = root 4) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := half_positions
  obtain ⟨z0, z1, z2, z3, z4⟩ := half_zeros
  constructor
  · intro u hu hz
    exact positive_roots_exhaust (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith [p0.1]) (by linarith [p0.2, p1.1])
      (by linarith [p1.2, pi_gt_three]) z0 z1 hu hz
  · intro u hu hz
    exact negative_roots_exhaust (by norm_num : (0 : ℝ) < 1 / 2)
      (by linarith [p2.1]) (by linarith [p2.2, p3.1]) (by linarith [p3.2, p4.1])
      (by linarith [p4.2, pi_gt_three]) z2 z3 z4 hu hz

theorem one_exhaustion :
    (∀ u ∈ Ioo 0 (Real.pi / 2), witness 1 u = 0 → u = root 5 ∨ u = root 6) ∧
    (∀ u ∈ Ioo 0 (Real.pi / 2), witness (-1) u = 0 →
      u = root 7 ∨ u = root 8 ∨ u = root 9) := by
  obtain ⟨p5, p6, p7, p8, p9⟩ := one_positions
  obtain ⟨z5, z6, z7, z8, z9⟩ := one_zeros
  constructor
  · intro u hu hz
    exact positive_roots_exhaust (by norm_num : (0 : ℝ) < 1)
      (by linarith [p5.1]) (by linarith [p5.2, p6.1])
      (by linarith [p6.2, pi_gt_three]) z5 z6 hu hz
  · intro u hu hz
    exact negative_roots_exhaust (by norm_num : (0 : ℝ) < 1)
      (by linarith [p7.1]) (by linarith [p7.2, p8.1]) (by linarith [p8.2, p9.1])
      (by linarith [p9.2, pi_gt_three]) z7 z8 z9 hu hz

end
end StructuralNote.FixedDualRootGeometry
