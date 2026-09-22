import StructuralNote.RationalChart
import EventualExact.BoxLensLift
import Mathlib.NumberTheory.Niven

/-! The actual base-edge-gauge configuration (10.4), with `2m-1` real parameters.
The centers are finite centerPrefix sums, and the closure equation is their endpoint. -/

namespace StructuralNote.RationalConfiguration

open Erdos1045.EventualExact Complex RationalChart
open scoped BigOperators
noncomputable section

abbrev Variables (m : ℕ) := Fin (m - 1) ⊕ Fin m

def angleParameter {m : ℕ} (X : Variables m → ℝ) (j : Fin m) : ℝ :=
  if hj : j.val = 0 then 0 else X (.inl ⟨j.val - 1, by omega⟩)

def crossingParameter {m : ℕ} (X : Variables m → ℝ) (j : Fin m) : ℝ := X (.inr j)

def diameter {m : ℕ} (hm : 0 < m) (X : Variables m → ℝ) (j : ℕ) : ℂ :=
  LensClosure.unit (Real.pi / m * j) *
    rotation (angleParameter X ⟨j % m, Nat.mod_lt _ hm⟩)

def crossingUnit {m : ℕ} (X : Variables m → ℝ) (j : Fin m) : ℂ :=
  LensClosure.unit (LensClosure.midpoint m j) * rotation (crossingParameter X j)

def increment {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) (j : Fin m) : ℂ :=
  crossingIncrement (σ j) (diameter hm X j) (diameter hm X (j.val + 1)) (crossingUnit X j)

def centerPrefix {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) (r : ℕ) : ℂ :=
  ∑ j ∈ Finset.range r, if hj : j < m then increment hm σ X ⟨j, hj⟩ else 0

def closure {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) : ℂ :=
  ∑ j, increment hm σ X j

def point {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) (j : ℕ) : ℂ :=
  centerPrefix hm σ X (j % m) + diameter hm X j

def configuration {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) :
    Fin (2 * m) → ℂ := fun j => point hm σ X j

theorem variables_card {m : ℕ} (hm : 0 < m) : Fintype.card (Variables m) = 2 * m - 1 := by
  simp only [Variables, Fintype.card_sum, Fintype.card_fin]
  omega

@[simp] theorem diameter_zero {m : ℕ} (hm : 0 < m) (X : Variables m → ℝ) : diameter hm X 0 = 1 := by
  simp [diameter, angleParameter, LensClosure.unit]

theorem diameter_norm {m : ℕ} (hm : 0 < m) (X : Variables m → ℝ) (j : ℕ) :
    ‖diameter hm X j‖ = 1 := by
  simp only [diameter, norm_mul, LensClosure.norm_unit, rotation_norm, mul_one]

theorem crossingUnit_norm {m : ℕ} (X : Variables m → ℝ) (j : Fin m) : ‖crossingUnit X j‖ = 1 := by
  simp only [crossingUnit, norm_mul, LensClosure.norm_unit, rotation_norm, mul_one]

theorem diameter_shift {m : ℕ} (hm : 0 < m) (X : Variables m → ℝ) (j : ℕ) :
    diameter hm X (j + m) = -diameter hm X j := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : Real.pi / m * ((j : ℝ) + m) = Real.pi / m * j + Real.pi := by field_simp
  simp only [diameter, Nat.cast_add, he, Nat.add_mod_right, LensClosure.unit,
    Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
  ring

@[simp] theorem prefix_zero {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) :
    centerPrefix hm σ X 0 = 0 := by simp [centerPrefix]

theorem prefix_succ {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ)
    (j : Fin m) : centerPrefix hm σ X (j.val + 1) = centerPrefix hm σ X j + increment hm σ X j := by
  simp [centerPrefix, Finset.sum_range_succ, j.isLt]

theorem prefix_endpoint {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) :
    centerPrefix hm σ X m = closure hm σ X := by
  rw [centerPrefix, ← Fin.sum_univ_eq_sum_range]
  simp only [dif_pos, Fin.is_lt, closure]

theorem prefix_mod_of_closed {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ)
    (hc : closure hm σ X = 0) {j : ℕ} (hj : j ≤ m) :
    centerPrefix hm σ X (j % m) = centerPrefix hm σ X j := by
  rcases lt_or_eq_of_le hj with h | rfl
  · rw [Nat.mod_eq_of_lt h]
  · rw [Nat.mod_self, prefix_zero, prefix_endpoint, hc]

theorem point_shift {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) (j : ℕ) :
    point hm σ X (j + m) = centerPrefix hm σ X (j % m) - diameter hm X j := by
  rw [point, Nat.add_mod_right, diameter_shift]
  rfl

theorem point_periodic {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) :
    Function.Periodic (point hm σ X) (2 * m) := by
  intro j
  rw [show j + 2 * m = (j + m) + m by omega, point_shift,
    Nat.add_mod_right, diameter_shift]
  simp only [sub_neg_eq_add, point]

theorem point_matching_length {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : Variables m → ℝ) (j : ℕ) : ‖point hm σ X j - point hm σ X (j + m)‖ = 2 := by
  rw [point_shift]
  exact matching_length _ _ (diameter_norm hm X j)

theorem point_base_gauge {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) :
    point hm σ X 0 = 1 ∧ point hm σ X m = -1 := by
  constructor
  · simp [point]
  · simpa using point_shift hm σ X 0

theorem positive_crossing {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ)
    (hc : closure hm σ X = 0) (j : Fin m) (hσ : σ j = 1) :
    ‖point hm σ X (j.val + 1) - point hm σ X (j.val + m)‖ = 2 := by
  rw [point_shift, point, prefix_mod_of_closed hm σ X hc (by omega),
    Nat.mod_eq_of_lt j.isLt, prefix_succ]
  unfold increment
  rw [hσ]
  exact positive_crossing_length _ _ _ _ (crossingUnit_norm X j)

theorem negative_crossing {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ)
    (hc : closure hm σ X = 0) (j : Fin m) (hσ : σ j = -1) :
    ‖point hm σ X j - point hm σ X (j.val + 1 + m)‖ = 2 := by
  rw [point_shift, point, prefix_mod_of_closed hm σ X hc (j := j.val + 1) (by omega),
    Nat.mod_eq_of_lt j.isLt, prefix_succ]
  unfold increment
  rw [hσ]
  exact negative_crossing_length _ _ _ _ (crossingUnit_norm X j)

def node {m : ℕ} (hm : 0 < m) (j : ℕ) : Fin (2 * m) := ⟨j % (2 * m), Nat.mod_lt _ (by omega)⟩

theorem point_mod {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ) (X : Variables m → ℝ) (j : ℕ) :
    point hm σ X (j % (2 * m)) = point hm σ X j := by
  have h := (point_periodic hm σ X).nat_mul (j / (2 * m)) (j % (2 * m))
  simp only [Nat.cast_id] at h
  rw [Nat.mul_comm (j / (2 * m)) (2 * m), Nat.mod_add_div] at h
  exact h.symm

theorem configuration_node {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : Variables m → ℝ) (j : ℕ) : configuration hm σ X (node hm j) = point hm σ X j :=
  point_mod hm σ X j

theorem configuration_matching_length {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : Variables m → ℝ) (j : Fin (2 * m)) :
    ‖configuration hm σ X j - configuration hm σ X (FourierMultiplier.halfTurn hm j)‖ = 2 := by
  change ‖point hm σ X j - point hm σ X ((j.val + m) % (2 * m))‖ = 2
  rw [point_mod]
  exact point_matching_length hm σ X j

theorem configuration_positive_crossing {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : Variables m → ℝ) (hc : closure hm σ X = 0) (j : Fin m) (hσ : σ j = 1) :
    ‖configuration hm σ X (node hm (j.val + 1)) -
      configuration hm σ X (node hm (j.val + m))‖ = 2 := by
  simp only [configuration_node]
  exact positive_crossing hm σ X hc j hσ

theorem configuration_negative_crossing {m : ℕ} (hm : 0 < m) (σ : Fin m → ℝ)
    (X : Variables m → ℝ) (hc : closure hm σ X = 0) (j : Fin m) (hσ : σ j = -1) :
    ‖configuration hm σ X (node hm j) -
      configuration hm σ X (node hm (j.val + 1 + m))‖ = 2 := by
  simp only [configuration_node]
  exact negative_crossing hm σ X hc j hσ

theorem rational_pi_coefficients_algebraic (q : ℚ) :
    IsAlgebraic ℚ (Real.cos ((q : ℝ) * Real.pi)) ∧
      IsAlgebraic ℚ (Real.sin ((q : ℝ) * Real.pi)) := by
  have hi : Function.Injective (algebraMap ℤ ℚ) := by
    intro a b h
    exact_mod_cast h
  exact ⟨(Real.isAlgebraic_cos_rat_mul_pi q).extendScalars hi,
    (Real.isAlgebraic_sin_rat_mul_pi q).extendScalars hi⟩

theorem reference_coefficients_algebraic (m j : ℕ) :
    IsAlgebraic ℚ (LensClosure.unit (Real.pi / m * j)).re ∧
      IsAlgebraic ℚ (LensClosure.unit (Real.pi / m * j)).im := by
  have h := rational_pi_coefficients_algebraic ((j : ℚ) / m)
  have he : (((j : ℚ) / m : ℚ) : ℝ) * Real.pi = Real.pi / m * j := by push_cast; ring
  simpa only [he, LensClosure.unit_re, LensClosure.unit_im] using h

theorem midpoint_coefficients_algebraic {m : ℕ} (j : Fin m) :
    IsAlgebraic ℚ (LensClosure.unit (LensClosure.midpoint m j)).re ∧
      IsAlgebraic ℚ (LensClosure.unit (LensClosure.midpoint m j)).im := by
  have h := rational_pi_coefficients_algebraic (((j.val : ℚ) + 1 / 2) / m)
  have he : ((((j.val : ℚ) + 1 / 2) / m : ℚ) : ℝ) * Real.pi = LensClosure.midpoint m j := by
    unfold LensClosure.midpoint
    push_cast
    ring
  simpa only [he, LensClosure.unit_re, LensClosure.unit_im] using h

end
end StructuralNote.RationalConfiguration
