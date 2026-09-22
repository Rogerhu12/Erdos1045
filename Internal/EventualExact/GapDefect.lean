import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Scalar and finite-sum estimates for the spacing defect in §2.5.1.
The geometric force-to-defect inequality is not an assumption hidden in these
definitions: it will be a separate theorem about actual circle configurations. -/

namespace Erdos1045.EventualExact

open scoped BigOperators
noncomputable section

def gapDefect (r : ℝ) : ℝ := r⁻¹ ^ 2 + 2 * r - 3

theorem gapDefect_factorization {r : ℝ} (hr : r ≠ 0) :
    gapDefect r = (r - 1) ^ 2 * (2 * r + 1) / r ^ 2 := by
  unfold gapDefect
  field_simp
  ring

theorem gapDefect_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ gapDefect r := by
  rw [gapDefect_factorization hr.ne']
  positivity

theorem gapDefect_eq_zero_iff {r : ℝ} (hr : 0 < r) :
    gapDefect r = 0 ↔ r = 1 := by
  rw [gapDefect_factorization hr.ne']
  have hpos : 0 < 2 * r + 1 := by positivity
  simp only [div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff (by decide : 2 ≠ 0),
    sub_eq_zero, hpos.ne', hr.ne', or_false]

theorem half_le_gapDefect {r : ℝ} (hr : 2 ≤ r) : r / 2 ≤ gapDefect r := by
  unfold gapDefect
  nlinarith [sq_nonneg r⁻¹]

theorem gap_le_two_add_twice_defect {r : ℝ} (hr : 0 < r) :
    r ≤ 2 + 2 * gapDefect r := by
  by_cases h : r ≤ 2
  · linarith [gapDefect_nonneg hr]
  · linarith [half_le_gapDefect (le_of_lt (lt_of_not_ge h))]

theorem gap_square_le_defect {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b) :
    (r - 1) ^ 2 ≤ b / 2 * gapDefect r := by
  have hprod : gapDefect r * r ^ 2 = (r - 1) ^ 2 * (2 * r + 1) := by
    rw [gapDefect_factorization hr.ne']
    field_simp
  have hb : 0 < b := hr.trans_le hrb
  have hfactor : 2 * r ^ 2 ≤ b * (2 * r + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrb) (show 0 ≤ 2 * r + 1 by positivity)]
  have hmul := mul_le_mul_of_nonneg_left hfactor (sq_nonneg (r - 1))
  have hsum : (2 * (r - 1) ^ 2 - b * gapDefect r) * r ^ 2 ≤ 0 := by
    nlinarith [hprod]
  have hmain : 2 * (r - 1) ^ 2 - b * gapDefect r ≤ 0 :=
    nonpos_of_mul_nonpos_left hsum (sq_pos_of_pos hr)
  linarith

section Finite

variable {ι : Type*} [Fintype ι] (r : ι → ℝ)

def totalGapDefect : ℝ := ∑ i, gapDefect (r i)

def gapSquareSum : ℝ := ∑ i, (r i - 1) ^ 2

theorem totalGapDefect_nonneg (hr : ∀ i, 0 < r i) : 0 ≤ totalGapDefect r :=
  Finset.sum_nonneg fun i _ => gapDefect_nonneg (hr i)

theorem gapDefect_le_total (hr : ∀ i, 0 < r i) (i : ι) :
    gapDefect (r i) ≤ totalGapDefect r := by
  exact Finset.single_le_sum (fun j _ => gapDefect_nonneg (hr j)) (Finset.mem_univ i)

theorem gap_le_total_bound (hr : ∀ i, 0 < r i) (i : ι) :
    r i ≤ 2 + 2 * totalGapDefect r := by
  have h := gap_le_two_add_twice_defect (hr i)
  linarith [gapDefect_le_total r hr i]

theorem gapSquareSum_le_total {b : ℝ} (hr : ∀ i, 0 < r i)
    (hb : ∀ i, r i ≤ b) : gapSquareSum r ≤ b / 2 * totalGapDefect r := by
  calc
    gapSquareSum r ≤ ∑ i, b / 2 * gapDefect (r i) :=
      Finset.sum_le_sum fun i _ => gap_square_le_defect (hr i) (hb i)
    _ = b / 2 * totalGapDefect r := (Finset.mul_sum _ _ _).symm

theorem totalGapDefect_eq_zero_iff (hr : ∀ i, 0 < r i) :
    totalGapDefect r = 0 ↔ ∀ i, r i = 1 := by
  constructor
  · intro h i
    apply (gapDefect_eq_zero_iff (hr i)).mp
    have hi := gapDefect_le_total r hr i
    rw [h] at hi
    exact le_antisymm hi (gapDefect_nonneg (hr i))
  · intro h
    simp [totalGapDefect, gapDefect, h]
    ring

/-- The scalar conclusions of (2.21), once the actual force inequality is proved. -/
theorem gap_bounds_of_force_budget {T : ℝ} (hr : ∀ i, 0 < r i)
    (hbudget : totalGapDefect r ≤ (3 * Real.pi ^ 2 / 2) * T) :
    (∀ i, r i ≤ 2 + 3 * Real.pi ^ 2 * T) ∧
      gapSquareSum r ≤ (3 * Real.pi ^ 2 / 4) * (2 + 3 * Real.pi ^ 2 * T) * T := by
  have hT : 0 ≤ T := by
    have hp : 0 < 3 * Real.pi ^ 2 / 2 := by positivity
    exact nonneg_of_mul_nonneg_right ((totalGapDefect_nonneg r hr).trans hbudget) hp
  have hb (i : ι) : r i ≤ 2 + 3 * Real.pi ^ 2 * T := by
    have hi := gap_le_total_bound r hr i
    linarith
  refine ⟨hb, ?_⟩
  calc
    gapSquareSum r ≤ (2 + 3 * Real.pi ^ 2 * T) / 2 * totalGapDefect r :=
      gapSquareSum_le_total r hr hb
    _ ≤ (2 + 3 * Real.pi ^ 2 * T) / 2 * ((3 * Real.pi ^ 2 / 2) * T) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = (3 * Real.pi ^ 2 / 4) * (2 + 3 * Real.pi ^ 2 * T) * T := by ring

end Finite

end
end Erdos1045.EventualExact
