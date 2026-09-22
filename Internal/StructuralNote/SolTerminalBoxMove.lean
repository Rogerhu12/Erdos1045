import StructuralNote.SolTerminalTranslate
import StructuralNote.SolWordFlips
import StructuralNote.FiniteCompressionEnergy

namespace StructuralNote.SolTerminalBoxMove

open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open StructuralNote.SolWordHamming StructuralNote.SolWordFlips
open StructuralNote.FiniteCompressionEnergy
open FourierMultiplier
noncomputable section

theorem halfTurn_mod_first {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) :
    (halfTurn hm j).val % m = j.val % m := by
  simp only [halfTurn]
  rw [Nat.mod_mod_of_dvd _ (by exact ⟨2, by omega⟩ : m ∣ 2 * m)]
  simp

theorem mod_eq_iff_first_or_half {m : ℕ} (hm : 0 < m) (j : Fin (2 * m)) (i : Fin m) :
    j.val % m = i.val ↔ j = first i ∨ halfTurn hm j = first i := by
  constructor
  · intro h
    by_cases hj : j.val < m
    · left
      apply Fin.ext
      simpa [first, Nat.mod_eq_of_lt hj] using h
    · right
      apply Fin.ext
      have hk : (halfTurn hm j).val < m := (halfTurn_lt_iff hm j).2 hj
      have hh := halfTurn_mod_first hm j
      rw [Nat.mod_eq_of_lt hk, h] at hh
      simpa [first] using hh
  · rintro (rfl | h)
    · simp [first, Nat.mod_eq_of_lt i.isLt]
    · have hh := halfTurn_mod_first hm j
      rw [h] at hh
      simpa [first, Nat.mod_eq_of_lt i.isLt] using hh.symm

theorem vertex_flip_eq_add_patch {m : ℕ} {hm : 0 < m} (A : ℝ)
    (s : SignPattern hm) (i : Fin m) (hi : patternSign s (first i) = -1) :
    vertex A (flip s i) = vertex A s + patch hm A {first i} := by
  funext j
  simp only [Pi.add_apply, patch_apply, Finset.mem_singleton, vertex, boxVertex,
    patternSign_flip]
  by_cases hmod : j.val % m = i.val
  · rw [if_pos hmod]
    rcases (mod_eq_iff_first_or_half hm j i).1 hmod with rfl | hh
    · have hne : halfTurn hm (first i) ≠ first i := by
        intro h
        have ht : (halfTurn hm (first i)).val < m := by rw [h]; exact i.isLt
        have hn := (halfTurn_lt_iff hm (first i)).1 ht
        exact hn (by simp [first, i.isLt])
      simp [hi, hne]
      ring
    · have hne : j ≠ first i := by
        intro h
        subst j
        have hinv := congrArg (halfTurn hm) hh
        rw [SchurLift.halfTurn_involutive hm] at hinv
        have ht : (halfTurn hm (first i)).val < m := by rw [← hinv]; exact i.isLt
        have hn := (halfTurn_lt_iff hm (first i)).1 ht
        exact hn (by simp [first, i.isLt])
      have hs := patternSign_antiperiodic s j
      rw [hh, hi] at hs
      simp [hne, hh, hs]
      have hs' : patternSign s j = 1 := by linarith
      rw [hs']
      ring
  · rw [if_neg hmod]
    have hn := not_or.mp (show ¬(j = first i ∨ halfTurn hm j = first i) from
      fun h => hmod ((mod_eq_iff_first_or_half hm j i).2 h))
    simp [hn.1, hn.2]

theorem vertex_flip_eq_sub_patch {m : ℕ} {hm : 0 < m} (A : ℝ)
    (s : SignPattern hm) (i : Fin m) (hi : patternSign s (first i) = 1) :
    vertex A (flip s i) = vertex A s - patch hm A {first i} := by
  have hneg : patternSign (flip s i) (first i) = -1 := by
    rw [patternSign_flip]
    simp only [first, Nat.mod_eq_of_lt i.isLt, ↓reduceIte]
    have hfi : (⟨i.val, by omega⟩ : Fin (2 * m)) = first i := Fin.ext rfl
    rw [hfi, hi]
  have h := vertex_flip_eq_add_patch A (flip s i) i hneg
  have hv : vertex A (flip (flip s i) i) = vertex A s := by
    funext j
    simp only [vertex, boxVertex, patternSign_flip]
    by_cases hji : j.val % m = i.val <;> simp [hji]
  rw [hv] at h
  exact eq_sub_of_add_eq h.symm

theorem vertex_flipTwo_eq_endpoint_patches {m : ℕ} {hm : 0 < m} (A : ℝ)
    (s : SignPattern hm) (left right : Fin m) (hne : left ≠ right)
    (hleft : patternSign s (first left) = -1)
    (hright : patternSign s (first right) = 1) :
    vertex A (flipTwo s left right) =
      vertex A s - patch hm A {first right} + patch hm A {first left} := by
  have hright' : patternSign (flip s left) (first right) = 1 := by
    rw [patternSign_flip]
    have hrl : right.val ≠ left.val := fun h => hne (Fin.ext h.symm)
    simp only [first, Nat.mod_eq_of_lt right.isLt, if_neg hrl]
    have hfr : (⟨right.val, by omega⟩ : Fin (2 * m)) = first right := Fin.ext rfl
    rw [hfr, hright]
  rw [flipTwo, vertex_flip_eq_sub_patch A (flip s left) right hright',
    vertex_flip_eq_add_patch A s left hleft]
  abel

def positiveSites {m : ℕ} {hm : 0 < m} (s : SignPattern hm) : Finset (Fin m) :=
  Finset.univ.filter fun i => patternSign s (first i) = 1

theorem positiveSites_flipTwo {m : ℕ} {hm : 0 < m} (s : SignPattern hm)
    (left right : Fin m) (hne : left ≠ right)
    (hleft : patternSign s (first left) = -1)
    (hright : patternSign s (first right) = 1) :
    positiveSites (flipTwo s left right) =
      insert left ((positiveSites s).erase right) := by
  ext j
  simp only [positiveSites, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_erase]
  by_cases hjr : j = right
  · subst j
    have hrl : right.val ≠ left.val := fun h => hne (Fin.ext h.symm)
    simp only [flipTwo, patternSign_flip, first, Nat.mod_eq_of_lt right.isLt,
      if_neg hrl]
    have hfr : (⟨right.val, by omega⟩ : Fin (2 * m)) = first right := Fin.ext rfl
    rw [hfr, hright]
    simp [Ne.symm hne]
    norm_num
  · by_cases hjl : j = left
    · subst j
      have hlr : left.val ≠ right.val := fun h => hne (Fin.ext h)
      simp only [flipTwo, patternSign_flip, first, Nat.mod_eq_of_lt left.isLt,
        if_neg hlr]
      have hfl : (⟨left.val, by omega⟩ : Fin (2 * m)) = first left := Fin.ext rfl
      rw [hfl, hleft]
      norm_num
    · have hjlv : j.val ≠ left.val := fun h => hjl (Fin.ext h)
      have hjrv : j.val ≠ right.val := fun h => hjr (Fin.ext h)
      simp [flipTwo, patternSign_flip, first, Nat.mod_eq_of_lt j.isLt,
        hjlv, hjrv, hjl, hjr]

theorem terminal_flip_hamming {m : ℕ} {hm : 0 < m} (s : SignPattern hm)
    (left right : Fin m) : hamming s (flipTwo s left right) ≤ 2 :=
  hamming_flipTwo_le_two s left right

theorem terminal_flip_outside {m : ℕ} {hm : 0 < m} (s : SignPattern hm)
    (left right j : Fin m) (hjl : j ≠ left) (hjr : j ≠ right) :
    patternSign (flipTwo s left right) (first j) = patternSign s (first j) := by
  simp [flipTwo, patternSign_flip, first, Nat.mod_eq_of_lt j.isLt,
    show j.val ≠ left.val by exact fun h => hjl (Fin.ext h),
    show j.val ≠ right.val by exact fun h => hjr (Fin.ext h)]

theorem terminal_flip_vertex_box {m : ℕ} {hm : 0 < m} (A : ℝ) (s : SignPattern hm)
    (left right : Fin m) : vertex A (flipTwo s left right) ∈ box hm |A| := by
  refine ⟨flipTwo_vertex_antiperiodic A s left right, ?_⟩
  intro i
  rcases patternSign_is_sign (flipTwo s left right) i with hi | hi <;>
    simp [vertex, boxVertex, hi]

/-- The two endpoint flips are the genuine antiperiodic box move associated
with replacing the right endpoint by the vacant predecessor of the left endpoint. -/
theorem terminal_endpoint_move {m : ℕ} {hm : 0 < m} (A : ℝ) (s : SignPattern hm)
    (left right : Fin m) :
    Antiperiodic hm (vertex A (flipTwo s left right)) ∧
      hamming s (flipTwo s left right) ≤ 2 :=
  ⟨flipTwo_vertex_antiperiodic A s left right, hamming_flipTwo_le_two s left right⟩

end
end StructuralNote.SolTerminalBoxMove
