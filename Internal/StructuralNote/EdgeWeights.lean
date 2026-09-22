import EventualExact.SchurWeights

/-! The full edge multiplier Gamma in (4.4). Unlike the old center multiplier,
this includes even frequencies and applies to odd as well as even n. -/

noncomputable section

namespace StructuralNote.EdgeWeights

def Active (n p : ℕ) : Prop := 2 ≤ p ∧ p + 2 ≤ n

instance (n p : ℕ) : Decidable (Active n p) := inferInstanceAs
  (Decidable (2 ≤ p ∧ p + 2 ≤ n))

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
  rcases h with ⟨hp, hpn⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpn' : (p : ℝ) + 2 ≤ n := by exact_mod_cast hpn
  exact ⟨hn, by linarith, by linarith, by linarith⟩

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

theorem active_reflect {n p : ℕ} (hp : p ≤ n) : Active n (n - p) ↔ Active n p := by
  unfold Active
  omega

theorem weight_reflect {n p : ℕ} (hp : p ≤ n) : weight n (n - p) = weight n p := by
  by_cases h : Active n p
  · have h' := (active_reflect hp).2 h
    have hn0 := (active_bounds h).1.ne'
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
    exact fun h' => h ((active_reflect hp).1 h')

theorem weight_zero (n : ℕ) : weight n 0 = 0 := by
  apply weight_eq_zero
  simp [Active]

theorem weight_one (n : ℕ) : weight n 1 = 0 := by
  apply weight_eq_zero
  simp [Active]

/-- On the antiperiodic space the new full multiplier restricts exactly to the
old odd-frequency center multiplier; no limiting operation is involved. -/
theorem odd_restriction {n p : ℕ} (hn : Even n) (hp : Odd p) :
    weight n p = Erdos1045.EventualExact.SchurWeights.weight n p := by
  have ha : Active n p ↔ Erdos1045.EventualExact.SchurWeights.Active n p := by
    have hn2 := Nat.even_iff.mp hn
    have hp2 := Nat.odd_iff.mp hp
    constructor
    · rintro ⟨ha, hb⟩
      exact ⟨hp, by omega, by omega⟩
    · rintro ⟨_, ha, hb⟩
      exact ⟨by omega, by omega⟩
  simp only [weight, Erdos1045.EventualExact.SchurWeights.weight, ha]

end StructuralNote.EdgeWeights
