import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! The actual finite Schur weights in manuscript Section 4.1. -/

noncomputable section

namespace Erdos1045.EventualExact.SchurWeights

def Active (n p : ℕ) : Prop := Odd p ∧ 3 ≤ p ∧ p + 3 ≤ n

instance (n p : ℕ) : Decidable (Active n p) := inferInstanceAs
  (Decidable (Odd p ∧ 3 ≤ p ∧ p + 3 ≤ n))

/-- The weight is extended by zero off the odd interior frequencies. -/
def weight (n p : ℕ) : ℝ :=
  if Active n p then
    (((p : ℝ) - 1) * ((n : ℝ) - p - 1) / n) *
      Real.sin (Real.pi / n) ^ 2 /
      (Real.sin (((p : ℝ) - 1) * Real.pi / n) *
        Real.sin (((p : ℝ) + 1) * Real.pi / n))
  else 0

theorem weight_eq_zero {n p : ℕ} (h : ¬ Active n p) : weight n p = 0 := by
  simp [weight, h]

theorem active_bounds {n p : ℕ} (h : Active n p) :
    0 < (n : ℝ) ∧ 0 < (p : ℝ) - 1 ∧
      (p : ℝ) + 1 < n ∧ 0 < (n : ℝ) - p - 1 := by
  rcases h with ⟨_, hp, hpn⟩
  constructor
  · exact_mod_cast (show 0 < n by omega)
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn' : (p : ℝ) + 3 ≤ n := by exact_mod_cast hpn
  exact ⟨by linarith, by linarith, by linarith⟩

theorem weight_pos {n p : ℕ} (h : Active n p) : 0 < weight n p := by
  rcases active_bounds h with ⟨hn, hp, hpn, hnp⟩
  have hsin (a : ℝ) (ha : 0 < a) (han : a < n) :
      0 < Real.sin (a * Real.pi / n) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · apply (div_lt_iff₀ hn).2
      nlinarith [Real.pi_pos]
  have hminus := hsin ((p : ℝ) - 1) hp (by linarith)
  have hplus := hsin ((p : ℝ) + 1) (by linarith) hpn
  have hone := hsin 1 (by norm_num) (by linarith)
  simp only [one_mul] at hone
  simp only [weight, if_pos h]
  exact div_pos (mul_pos (div_pos (mul_pos hp hnp) hn) (sq_pos_of_pos hone))
    (mul_pos hminus hplus)

theorem weight_nonneg (n p : ℕ) : 0 ≤ weight n p := by
  by_cases h : Active n p
  · exact (weight_pos h).le
  · rw [weight_eq_zero h]

theorem weight_ne_zero_iff (n p : ℕ) : weight n p ≠ 0 ↔ Active n p := by
  constructor
  · intro h
    by_contra hn
    exact h (weight_eq_zero hn)
  · exact fun h => (weight_pos h).ne'

theorem active_reflect {n p : ℕ} (hn : Even n) (hp : p ≤ n) :
    Active n (n - p) ↔ Active n p := by
  have hodd : Odd (n - p) ↔ Odd p := by
    simpa [hn] using Nat.odd_sub' hp
  constructor
  · rintro ⟨ho, hlo, hhi⟩
    exact ⟨hodd.mp ho, by omega, by omega⟩
  · rintro ⟨ho, hlo, hhi⟩
    exact ⟨hodd.mpr ho, by omega, by omega⟩

theorem weight_reflect {n p : ℕ} (hn : Even n) (hp : p ≤ n) :
    weight n (n - p) = weight n p := by
  by_cases h : Active n p
  · have h' := (active_reflect hn hp).2 h
    rcases active_bounds h with ⟨hnpos, _, _, _⟩
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hsminus :
        Real.sin (((n : ℝ) - p - 1) * Real.pi / n) =
          Real.sin (((p : ℝ) + 1) * Real.pi / n) := by
      rw [show ((n : ℝ) - p - 1) * Real.pi / n =
          Real.pi - ((p : ℝ) + 1) * Real.pi / n by field_simp; ring]
      exact Real.sin_pi_sub _
    have hsplus :
        Real.sin (((n : ℝ) - p + 1) * Real.pi / n) =
          Real.sin (((p : ℝ) - 1) * Real.pi / n) := by
      rw [show ((n : ℝ) - p + 1) * Real.pi / n =
          Real.pi - ((p : ℝ) - 1) * Real.pi / n by field_simp; ring]
      exact Real.sin_pi_sub _
    simp only [weight, if_pos h, if_pos h', Nat.cast_sub hp, hsminus, hsplus]
    congr 1 <;> ring
  · rw [weight_eq_zero h, weight_eq_zero]
    exact fun h' => h ((active_reflect hn hp).1 h')

theorem weight_zero (n : ℕ) : weight n 0 = 0 := by
  apply weight_eq_zero
  simp [Active]

theorem weight_self (n : ℕ) : weight n n = 0 := by
  apply weight_eq_zero
  simp [Active]

end Erdos1045.EventualExact.SchurWeights
