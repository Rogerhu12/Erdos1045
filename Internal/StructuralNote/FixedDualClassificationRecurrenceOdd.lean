import StructuralNote.FixedDualClassificationRecurrenceFourier

/-! Odd-frequency projection of the exact quadratic Fourier identity. -/

namespace StructuralNote.FixedDualClassificationRecurrenceOdd

open Complex Real
open FixedDualClassificationRecurrenceFourier
open scoped BigOperators
noncomputable section

theorem exp_ne_one_of_sin_half {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    Complex.exp ((t : ℂ) * Complex.I) ≠ 1 := by
  intro he
  have h := exp_chord_identity t
  rw [he] at h
  have hn : ((-4 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast mul_ne_zero (by norm_num : (-4 : ℝ) ≠ 0) (pow_ne_zero 2 ht)
  apply hn
  simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_one] using h.symm

theorem cosine_root_sum {n : ℕ} {t : ℝ}
    (hroot : Complex.exp ((t : ℂ) * Complex.I) ^ n = 1)
    (hsin : Real.sin (t / 2) ≠ 0) :
    (∑ p ∈ Finset.range n, Real.cos (p * t)) = 0 := by
  have h := geom_sum_eq (exp_ne_one_of_sin_half hsin) n
  rw [hroot, sub_self, zero_div] at h
  have hre := congrArg Complex.re h
  simp only [Complex.re_sum, Complex.zero_re] at hre
  convert hre using 1
  apply Finset.sum_congr rfl
  intro p _
  rw [← Complex.exp_nat_mul]
  have he : (p : ℂ) * ((t : ℂ) * Complex.I) = ((p * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re]

theorem polynomial_cosine_sum {n : ℕ} {t : ℝ}
    (hroot : Complex.exp ((t : ℂ) * Complex.I) ^ n = 1)
    (hsin : Real.sin (t / 2) ≠ 0) :
    (∑ p ∈ Finset.range n, ((p : ℝ) - 1) * ((n : ℝ) - p - 1) * Real.cos (p * t)) =
      -(n : ℝ) / (2 * Real.sin (t / 2) ^ 2) := by
  have he : (∑ p ∈ Finset.range n, ((p : ℝ) - 1) * ((n : ℝ) - p - 1) * Real.cos (p * t)) =
      (∑ p ∈ Finset.range n, (p : ℝ) * ((n : ℝ) - p) * Real.cos (p * t)) -
        ((n : ℝ) - 1) * ∑ p ∈ Finset.range n, Real.cos (p * t) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he, quadratic_cosine_sum hroot hsin, cosine_root_sum hroot hsin, mul_zero, sub_zero]

theorem odd_projection (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (∑ p ∈ Finset.range n, if Odd p then a p * Real.cos (p * t) else 0) =
      ((∑ p ∈ Finset.range n, a p * Real.cos (p * t)) -
        ∑ p ∈ Finset.range n, a p * Real.cos (p * (t + Real.pi))) / 2 := by
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  rw [mul_add, Real.cos_add_nat_mul_pi]
  by_cases hp : Odd p
  · rw [if_pos hp, hp.neg_one_pow]
    ring
  · have he : Even p := Nat.not_odd_iff_even.mp hp
    rw [if_neg hp, he.neg_one_pow]
    ring

theorem even_root_shift {n : ℕ} (hn : Even n) {t : ℝ}
    (hroot : Complex.exp ((t : ℂ) * Complex.I) ^ n = 1) :
    Complex.exp (((t + Real.pi : ℝ) : ℂ) * Complex.I) ^ n = 1 := by
  rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I,
    mul_neg_one, hn.neg_pow, hroot]

theorem odd_polynomial_cosine_sum {n : ℕ} (hn : Even n) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (hroot : Complex.exp ((t : ℂ) * Complex.I) ^ n = 1) :
    (∑ p ∈ Finset.range n, if Odd p then
        ((p : ℝ) - 1) * ((n : ℝ) - p - 1) * Real.cos (p * t) else 0) =
      -(n : ℝ) * Real.cos t / Real.sin t ^ 2 := by
  have hs : 0 < Real.sin (t / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
    (by linarith [ht.2, pi_pos])
  have hc : 0 < Real.cos (t / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, pi_pos], by linarith [ht.2]⟩
  have he : Real.sin ((t + Real.pi) / 2) = Real.cos (t / 2) := by
    rw [show (t + Real.pi) / 2 = t / 2 + Real.pi / 2 by ring, Real.sin_add_pi_div_two]
  have hs' : Real.sin ((t + Real.pi) / 2) ≠ 0 := by rw [he]; exact hc.ne'
  rw [odd_projection, polynomial_cosine_sum hroot hs.ne',
    polynomial_cosine_sum (even_root_shift hn hroot) hs', he]
  have hsin : Real.sin t = 2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    rw [← Real.sin_two_mul, show 2 * (t / 2) = t by ring]
  have hcos : Real.cos t = Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2 := by
    have h := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  rw [hsin, hcos]
  field_simp
  ring

end
end StructuralNote.FixedDualClassificationRecurrenceOdd
