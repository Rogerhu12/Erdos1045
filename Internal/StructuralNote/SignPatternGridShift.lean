import StructuralNote.SignPatternSymmetry
import StructuralNote.FixedDualClassificationGridPeriodicity
import Mathlib.Algebra.Order.Floor.Ring

/-! Integer translations of the unwrapped finite grid. -/

namespace StructuralNote.SignPatternGridShift

open Set
open Erdos1045.EventualExact
open Erdos1045.EventualExact.FiniteBox
open Erdos1045.EventualExact.FourierMultiplier
open StructuralNote.FiniteCompressionRanked
open StructuralNote.FixedDualClassificationStep
open StructuralNote.SignPatternSymmetry
open StructuralNote.SolWordHamming
noncomputable section

theorem finRotate_site_add {m : ℕ} (hm : 0 < m) (j : ℕ) :
    finRotate (2 * m) (site hm j) = site hm (j + 1) := by
  let : NeZero (2 * m) := ⟨by omega⟩
  apply Fin.ext
  simp only [site, finRotate_apply, Fin.val_add, Fin.val_one']
  calc
    (j % (2 * m) + 1 % (2 * m)) % (2 * m) =
        (j + 1) % (2 * m) := by
      rw [Nat.mod_add_mod, Nat.mod_eq_of_lt (show 1 < 2 * m by omega)]

theorem finRotate_pow_site {m : ℕ} (hm : 0 < m) (j k : ℕ) :
    ((finRotate (2 * m)) ^ k) (site hm j) = site hm (j + k) := by
  induction k generalizing j with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ]
      change ((finRotate (2 * m)) ^ k) (finRotate (2 * m) (site hm j)) = _
      rw [finRotate_site_add hm j, ih]
      congr 1
      omega

@[simp] theorem patternSign_rotatePattern_site {m : ℕ} {hm : 0 < m}
    (k j : ℕ) (s : SignPattern hm) :
    patternSign (rotatePattern k s) (site hm j) =
      patternSign s (site hm (j + k)) := by
  rw [patternSign_rotatePattern, finRotate_pow_site hm]

theorem cellMidpoint_add {m : ℕ} (hm : 0 < m) (j k : ℕ) :
    cellMidpoint (2 * m) (j + k) =
      cellMidpoint (2 * m) j + (k : ℝ) * (Real.pi / m) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold cellMidpoint
  push_cast
  field_simp [hmR]
  ring

theorem phase_normalization {m : ℕ} (hm : 0 < m) {α : ℝ}
    (hα : α ∈ Icc (-(Real.pi / 3)) (Real.pi / 3)) :
    ∃ k : ℕ, ∃ β : ℝ, β ∈ Ico 0 (Real.pi / m) ∧
      β = α + 2 * Real.pi - (k : ℝ) * (Real.pi / m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : 0 < Real.pi / m := div_pos Real.pi_pos hmR
  let x : ℝ := (α + 2 * Real.pi) / (Real.pi / m)
  have hx : 0 ≤ x := by
    dsimp [x]
    apply div_nonneg
    · linarith [hα.1, Real.pi_pos]
    · exact hd.le
  let k : ℕ := ⌊x⌋₊
  let β : ℝ := α + 2 * Real.pi - (k : ℝ) * (Real.pi / m)
  have hklo : (k : ℝ) ≤ x := by
    dsimp [k]
    exact_mod_cast (Nat.floor_le hx)
  have hkhi : x < (k : ℝ) + 1 := by
    dsimp [k]
    exact_mod_cast (Nat.lt_floor_add_one x)
  have hscale : (k : ℝ) * (Real.pi / m) ≤ α + 2 * Real.pi := by
    have := mul_le_mul_of_nonneg_right hklo hd.le
    dsimp [x] at this
    field_simp [hd.ne'] at this ⊢
    nlinarith
  have hscale' : α + 2 * Real.pi < ((k : ℝ) + 1) * (Real.pi / m) := by
    have := mul_lt_mul_of_pos_right hkhi hd
    dsimp [x] at this
    field_simp [hd.ne'] at this ⊢
    nlinarith
  refine ⟨k, β, ?_, rfl⟩
  constructor
  · dsimp [β]
    linarith
  · dsimp [β]
    linarith

end
end StructuralNote.SignPatternGridShift
