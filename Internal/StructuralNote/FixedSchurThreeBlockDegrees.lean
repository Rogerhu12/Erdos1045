import StructuralNote.FixedSchurWordDegrees
import StructuralNote.SolThreeBlockWord

/-! The three leaves and three degree-three vertices of a three-block word. -/

namespace StructuralNote.FixedSchurThreeBlockDegrees

open Erdos1045.EventualExact FiniteBox FourierMultiplier
open FixedSchurWordDegrees SolThreeBlockWord

noncomputable section

theorem previous_val {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    (previous j).val = if j.val = 0 then 2 * m - 1 else j.val - 1 := by
  simp only [previous, cyclicAdvance]
  by_cases hj : j.val = 0
  · simp [hj, Nat.mod_eq_of_lt (by omega : 2 * m - 1 < 2 * m)]
  · rw [if_neg hj]
    have he : j.val + (2 * m - 1) = (j.val - 1) + 2 * m := by omega
    rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem raw_formula {m a b c : ℕ} (hp : 0 < a ∧ 0 < b ∧ 0 < c)
    (hs : a + b + c = m) (j : Fin (2 * m)) :
    threeBlockRaw (m := m) a b j =
      if j.val < a then 1 else if j.val < a + b then -1 else
      if j.val < m then 1 else if j.val < m + a then -1 else
      if j.val < m + a + b then 1 else -1 := by
  unfold threeBlockRaw halfValue
  by_cases hj : j.val < m
  · rw [if_pos hj, Nat.mod_eq_of_lt hj]
    split_ifs <;> first | rfl | omega
  · rw [if_neg hj, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> norm_num <;> omega

theorem leaf_iff {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) (j : Fin (2 * m)) :
    (neighbors (patternSign (threeBlockPattern (by omega) hp hs)) j).card = 1 ↔
      j.val = 0 ∨ j.val = a + b ∨ j.val = m + a := by
  rw [degree_one_iff hm]
  simp only [patternSign_threeBlockPattern, raw_formula hp hs, previous_val (m := m) (by omega)]
  split_ifs <;> norm_num <;> omega

theorem branch_iff {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) (j : Fin (2 * m)) :
    (neighbors (patternSign (threeBlockPattern (by omega) hp hs)) j).card = 3 ↔
      j.val = a ∨ j.val = m ∨ j.val = m + a + b := by
  rw [degree_three_iff hm]
  simp only [patternSign_threeBlockPattern, raw_formula hp hs, previous_val (m := m) (by omega)]
  split_ifs <;> norm_num <;> omega

theorem leaves_eq {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    Finset.univ.filter (fun j =>
      (neighbors (patternSign (threeBlockPattern (by omega) hp hs)) j).card = 1) =
      {⟨0, by omega⟩, ⟨a + b, by omega⟩, ⟨m + a, by omega⟩} := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, leaf_iff hm hp hs,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

theorem branches_eq {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    Finset.univ.filter (fun j =>
      (neighbors (patternSign (threeBlockPattern (by omega) hp hs)) j).card = 3) =
      {⟨a, by omega⟩, ⟨m, by omega⟩, ⟨m + a + b, by omega⟩} := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, branch_iff hm hp hs,
    Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

theorem exactly_three_leaves {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    (Finset.univ.filter (fun j =>
      (neighbors (patternSign (threeBlockPattern (by omega) hp hs)) j).card = 1)).card = 3 := by
  classical
  rw [leaves_eq hm hp hs]
  have h₁ : (⟨0, by omega⟩ : Fin (2 * m)) ≠ ⟨a + b, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  have h₂ : (⟨0, by omega⟩ : Fin (2 * m)) ≠ ⟨m + a, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  have h₃ : (⟨a + b, by omega⟩ : Fin (2 * m)) ≠ ⟨m + a, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  simp [h₁, h₂, h₃]

theorem exactly_three_branches {m a b c : ℕ} (hm : 2 ≤ m)
    (hp : 0 < a ∧ 0 < b ∧ 0 < c) (hs : a + b + c = m) :
    (Finset.univ.filter (fun j =>
      (neighbors (patternSign (threeBlockPattern (by omega) hp hs)) j).card = 3)).card = 3 := by
  classical
  rw [branches_eq hm hp hs]
  have h₁ : (⟨a, by omega⟩ : Fin (2 * m)) ≠ ⟨m, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  have h₂ : (⟨a, by omega⟩ : Fin (2 * m)) ≠ ⟨m + a + b, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  have h₃ : (⟨m, by omega⟩ : Fin (2 * m)) ≠ ⟨m + a + b, by omega⟩ := by
    simp only [ne_eq, Fin.ext_iff]; omega
  simp [h₁, h₂, h₃]

end
end StructuralNote.FixedSchurThreeBlockDegrees
