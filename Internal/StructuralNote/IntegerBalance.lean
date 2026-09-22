import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic

/-! The exact integer gap used in §10.1. This is independent of the unproved
finite-model classification and of the common-fiber comparison. -/

namespace StructuralNote.IntegerBalance

/-- A fixed-sum triple is balanced when its entries are the floor of the
average or the next integer. The fixed sum determines how many are larger. -/
def BalancedAt (k a b c : ℤ) : Prop :=
  (a = k ∨ a = k + 1) ∧ (b = k ∨ b = k + 1) ∧ (c = k ∨ c = k + 1)

theorem square_sub_self_nonneg (d : ℤ) : 0 ≤ d ^ 2 - d := by
  rcases le_or_gt d 0 with h | h
  · nlinarith [sq_nonneg d]
  · have : 1 ≤ d := h
    nlinarith [mul_nonneg (show 0 ≤ d by omega) (show 0 ≤ d - 1 by omega)]

theorem square_sub_self_gap {d : ℤ} (h : d ≠ 0 ∧ d ≠ 1) :
    2 ≤ d ^ 2 - d := by
  rcases le_or_gt d 0 with hd | hd
  · have : d ≤ -1 := by omega
    nlinarith [mul_nonneg (show 0 ≤ -d - 1 by omega) (show 0 ≤ -d by omega)]
  · have : 2 ≤ d := by omega
    nlinarith [mul_nonneg (show 0 ≤ d - 2 by omega) (show 0 ≤ d + 1 by omega)]

theorem square_sub_self_eq_zero_iff (d : ℤ) :
    d ^ 2 - d = 0 ↔ d = 0 ∨ d = 1 := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have := square_sub_self_gap hn
    omega
  · rintro (rfl | rfl) <;> norm_num

theorem square_sum_decomposition {k r a b c : ℤ} (hs : a + b + c = 3 * k + r) :
    a ^ 2 + b ^ 2 + c ^ 2 - (3 * k ^ 2 + 2 * k * r + r) =
      ((a - k) ^ 2 - (a - k)) + ((b - k) ^ 2 - (b - k)) +
      ((c - k) ^ 2 - (c - k)) := by
  linear_combination (2 * k + 1) * hs

theorem square_sum_minimum {k r a b c : ℤ} (hs : a + b + c = 3 * k + r) :
    3 * k ^ 2 + 2 * k * r + r ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have ha := square_sub_self_nonneg (a - k)
  have hb := square_sub_self_nonneg (b - k)
  have hc := square_sub_self_nonneg (c - k)
  have hd := square_sum_decomposition hs
  omega

theorem square_sum_eq_minimum_iff {k r a b c : ℤ}
    (hs : a + b + c = 3 * k + r) :
    a ^ 2 + b ^ 2 + c ^ 2 = 3 * k ^ 2 + 2 * k * r + r ↔ BalancedAt k a b c := by
  have hd := square_sum_decomposition hs
  have ha := square_sub_self_nonneg (a - k)
  have hb := square_sub_self_nonneg (b - k)
  have hc := square_sub_self_nonneg (c - k)
  constructor
  · intro he
    have hda : (a - k) ^ 2 - (a - k) = 0 := by omega
    have hdb : (b - k) ^ 2 - (b - k) = 0 := by omega
    have hdc : (c - k) ^ 2 - (c - k) = 0 := by omega
    rw [square_sub_self_eq_zero_iff] at hda hdb hdc
    dsimp [BalancedAt]
    omega
  · intro he
    obtain ⟨ha', hb', hc'⟩ := he
    have hda : (a - k) ^ 2 - (a - k) = 0 :=
      (square_sub_self_eq_zero_iff _).2 (by omega)
    have hdb : (b - k) ^ 2 - (b - k) = 0 :=
      (square_sub_self_eq_zero_iff _).2 (by omega)
    have hdc : (c - k) ^ 2 - (c - k) = 0 :=
      (square_sub_self_eq_zero_iff _).2 (by omega)
    omega

/-- Every nonbalanced integer triple loses at least two in the sum of squares. -/
theorem square_sum_gap {k r a b c : ℤ} (hs : a + b + c = 3 * k + r)
    (hne : ¬ BalancedAt k a b c) :
    3 * k ^ 2 + 2 * k * r + r + 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hd := square_sum_decomposition hs
  have ha := square_sub_self_nonneg (a - k)
  have hb := square_sub_self_nonneg (b - k)
  have hc := square_sub_self_nonneg (c - k)
  have hn : (a - k ≠ 0 ∧ a - k ≠ 1) ∨
      (b - k ≠ 0 ∧ b - k ≠ 1) ∨ (c - k ≠ 0 ∧ c - k ≠ 1) := by
    simp only [BalancedAt] at hne
    omega
  rcases hn with h | h | h
  · have := square_sub_self_gap h
    omega
  · have := square_sub_self_gap h
    omega
  · have := square_sub_self_gap h
    omega

theorem balanced_zero_remainder {k a b c : ℤ} (hs : a + b + c = 3 * k) :
    BalancedAt k a b c ↔ a = k ∧ b = k ∧ c = k := by
  dsimp [BalancedAt]
  omega

theorem balanced_one_remainder {k a b c : ℤ} (hs : a + b + c = 3 * k + 1) :
    BalancedAt k a b c ↔
      (a = k + 1 ∧ b = k ∧ c = k) ∨
      (a = k ∧ b = k + 1 ∧ c = k) ∨
      (a = k ∧ b = k ∧ c = k + 1) := by
  dsimp [BalancedAt]
  omega

theorem balanced_two_remainder {k a b c : ℤ} (hs : a + b + c = 3 * k + 2) :
    BalancedAt k a b c ↔
      (a = k ∧ b = k + 1 ∧ c = k + 1) ∨
      (a = k + 1 ∧ b = k ∧ c = k + 1) ∨
      (a = k + 1 ∧ b = k + 1 ∧ c = k) := by
  dsimp [BalancedAt]
  omega

/-- The three canonical cycle arcs have total length n-3. -/
theorem cycle_arc_sum (a b c : ℤ) :
    (2 * a - 1) + (2 * b - 1) + (2 * c - 1) = 2 * (a + b + c) - 3 := by
  ring

end StructuralNote.IntegerBalance
