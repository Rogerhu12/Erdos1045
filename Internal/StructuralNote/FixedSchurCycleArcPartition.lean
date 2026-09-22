import StructuralNote.FixedSchurCycleArcLengths

/-! The three simple arcs cover the nonleaf cycle and intersect only at their
prescribed branch endpoints. -/

namespace StructuralNote.FixedSchurCycleArcPartition

open Erdos1045.EventualExact FiniteBox SolThreeBlockWord
open FixedSchurWordDegrees FixedSchurThreeBlockDegrees FixedSchurCycleArcLengths
noncomputable section

theorem first_second_intersection {m a b c : ℕ}
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) (x : Fin (2 * m)) :
    (ArcSupport (by omega) ⟨m, by omega⟩ a x ∧
      ArcSupport (by omega) ⟨a, by omega⟩ b x) ↔ x = ⟨a, by omega⟩ := by
  rw [firstArc_support_bounds hp hs, secondArc_support_bounds hp hs, Fin.ext_iff]
  dsimp only
  omega

theorem second_third_intersection {m a b c : ℕ}
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) (x : Fin (2 * m)) :
    (ArcSupport (by omega) ⟨a, by omega⟩ b x ∧
      ArcSupport (by omega) ⟨m + a + b, by omega⟩ c x) ↔
      x = ⟨m + a + b, by omega⟩ := by
  rw [secondArc_support_bounds hp hs, thirdArc_support_bounds hp hs, Fin.ext_iff]
  dsimp only
  omega

theorem third_first_intersection {m a b c : ℕ}
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) (x : Fin (2 * m)) :
    (ArcSupport (by omega) ⟨m + a + b, by omega⟩ c x ∧
      ArcSupport (by omega) ⟨m, by omega⟩ a x) ↔ x = ⟨m, by omega⟩ := by
  rw [thirdArc_support_bounds hp hs, firstArc_support_bounds hp hs, Fin.ext_iff]
  dsimp only
  omega

theorem arcs_cover_nonleaves {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) (x : Fin (2 * m)) :
    (ArcSupport (by omega) ⟨m, by omega⟩ a x ∨
      ArcSupport (by omega) ⟨a, by omega⟩ b x ∨
      ArcSupport (by omega) ⟨m + a + b, by omega⟩ c x) ↔
      (neighbors (patternSign (threeBlockPattern (by omega) hp hs)) x).card ≠ 1 := by
  rw [firstArc_support_bounds hp hs, secondArc_support_bounds hp hs,
    thirdArc_support_bounds hp hs, ne_eq, leaf_iff hm hp hs]
  have hx := x.isLt
  omega

theorem arc_lengths_sum {m a b c : ℕ}
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    (2 * a - 1) + (2 * b - 1) + (2 * c - 1) = 2 * m - 3 := by omega

end
end StructuralNote.FixedSchurCycleArcPartition
