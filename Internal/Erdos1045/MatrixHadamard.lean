import Erdos1045.MatrixTrace

namespace Erdos1045.MatrixDefect

open scoped BigOperators
noncomputable section

/-- The ordinary column form of Hadamard's determinant inequality, for every
complex square matrix. It contains no special Faber or capacity assertion. -/
structure ClassicalMatrixHadamard : Prop where
  hadamard : ∀ {n : ℕ} (F : Mat n),
    detSq F ≤ ∏ j, ∑ i, Complex.normSq (F i j)

theorem initial_determinant_bound (H : ClassicalMatrixHadamard)
    {n : ℕ} (hn : 0 < n) (F : Mat n)
    (hzero : ∀ i j : Fin n, (j : ℕ) = 0 → F i j = 1)
    (hother : ∀ i j : Fin n, (j : ℕ) ≠ 0 → ‖F i j‖ ≤ 2) :
    detSq F ≤ (n : ℝ) ^ n * 4 ^ (n - 1) := by
  have hcolumn (j : Fin n) : (∑ i, Complex.normSq (F i j)) ≤
      if (j : ℕ) = 0 then (n : ℝ) else 4 * n := by
    by_cases hj : (j : ℕ) = 0
    · simp [hj, hzero _ _ hj]
    · rw [if_neg hj]
      calc
        _ ≤ ∑ _i : Fin n, (4 : ℝ) := by
          apply Finset.sum_le_sum
          intro i _
          rw [Complex.normSq_eq_norm_sq]
          have h := hother i j hj
          have h0 := norm_nonneg (F i j)
          nlinarith
        _ = _ := by simp; ring
  have hprod : (∏ j : Fin n, if (j : ℕ) = 0 then (n : ℝ) else 4 * n) =
      (n : ℝ) ^ n * 4 ^ (n - 1) := by
    cases n with
    | zero => omega
    | succ m =>
      rw [Fin.prod_univ_succ]
      simp only [Fin.val_zero, ↓reduceIte, Fin.val_succ, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow,
        pow_succ]
      ring
  calc
    detSq F ≤ ∏ j, ∑ i, Complex.normSq (F i j) := H.hadamard F
    _ ≤ ∏ j : Fin n, if (j : ℕ) = 0 then (n : ℝ) else 4 * n := by
      apply Finset.prod_le_prod
      · intro j _; exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
      · intro j _; exact hcolumn j
    _ = _ := hprod

theorem initial_capacity_log_bound (H : ClassicalMatrixHadamard)
    {n : ℕ} (hn : 0 < n) {c Δ : ℝ} (hc : 0 < c) (F : Mat n)
    (hzero : ∀ i j : Fin n, (j : ℕ) = 0 → F i j = 1)
    (hother : ∀ i j : Fin n, (j : ℕ) ≠ 0 → ‖F i j‖ ≤ 2)
    (hlower : (n : ℝ) ^ n ≤ Δ)
    (hdet : Δ = c ^ (n * (n - 1)) * detSq F) :
    0 ≤ ((n : ℝ) - 1) * Real.log 4 + (n : ℝ) * (n - 1) * Real.log c := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hbound := initial_determinant_bound H hn F hzero hother
  have hup : (n : ℝ) ^ n ≤ c ^ (n * (n - 1)) * ((n : ℝ) ^ n * 4 ^ (n - 1)) := by
    calc
      _ ≤ Δ := hlower
      _ = c ^ (n * (n - 1)) * detSq F := hdet
      _ ≤ _ := mul_le_mul_of_nonneg_left hbound (pow_nonneg hc.le _)
  have hl := Real.log_le_log (pow_pos hn' n) hup
  rw [Real.log_mul (pow_ne_zero _ hc.ne') (mul_ne_zero (pow_ne_zero _ hn'.ne')
    (pow_ne_zero _ (by norm_num))),
    Real.log_mul (pow_ne_zero _ hn'.ne') (pow_ne_zero _ (by norm_num)),
    Real.log_pow, Real.log_pow, Real.log_pow] at hl
  have hn1 : 1 ≤ n := hn
  simp only [Nat.cast_mul, Nat.cast_sub hn1, Nat.cast_one] at hl
  linarith

end
end Erdos1045.MatrixDefect
