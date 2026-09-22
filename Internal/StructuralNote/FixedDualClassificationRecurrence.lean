import StructuralNote.FixedDualClassificationRecurrenceOdd

/-! The exact second-difference equation for the actual finite Schur kernel. -/

namespace StructuralNote.FixedDualClassificationRecurrence

open Real Complex Erdos1045.EventualExact
open FixedDualClassificationKernel FixedDualClassificationRecurrenceOdd
open scoped BigOperators
noncomputable section

theorem cosine_difference_factor (p a : ℝ) :
    2 * Real.cos (2 * p * a) - 2 * Real.cos (2 * a) =
      -4 * Real.sin ((p - 1) * a) * Real.sin ((p + 1) * a) := by
  have h := Real.cos_sub_cos (2 * p * a) (2 * a)
  rw [show (2 * p * a + 2 * a) / 2 = (p + 1) * a by ring,
    show (2 * p * a - 2 * a) / 2 = (p - 1) * a by ring] at h
  nlinarith

theorem weight_difference {n p : ℕ} (hn : Even n) (hp : p < n) :
    SchurWeights.weight n p * (2 * Real.cos (p * (2 * Real.pi / n)) -
        2 * Real.cos (2 * Real.pi / n)) =
      (-4 * Real.sin (Real.pi / n) ^ 2 / n) *
        (if Odd p then ((p : ℝ) - 1) * ((n : ℝ) - p - 1) else 0) := by
  by_cases ha : SchurWeights.Active n p
  · rcases SchurWeights.active_bounds ha with ⟨hn0, hp0, hpn, hnp⟩
    have hs (x : ℝ) (hx : 0 < x) (hxn : x < n) : Real.sin (x * Real.pi / n) ≠ 0 := by
      apply ne_of_gt
      apply Real.sin_pos_of_pos_of_lt_pi
      · positivity
      · apply (div_lt_iff₀ hn0).mpr
        nlinarith [pi_pos]
    have hm := hs ((p : ℝ) - 1) hp0 (by linarith)
    have hplus := hs ((p : ℝ) + 1) (by linarith) hpn
    rw [show (p : ℝ) * (2 * Real.pi / n) = 2 * p * (Real.pi / n) by ring,
      show 2 * Real.pi / n = 2 * (Real.pi / n) by ring, cosine_difference_factor,
      SchurWeights.weight, if_pos ha, if_pos ha.1]
    rw [show ((p : ℝ) - 1) * (Real.pi / n) = ((p : ℝ) - 1) * Real.pi / n by ring,
      show ((p : ℝ) + 1) * (Real.pi / n) = ((p : ℝ) + 1) * Real.pi / n by ring]
    have halg (A d : ℝ) (hd : d ≠ 0) : (A / d) * (-4 * d) = -4 * A := by
      rw [show (A / d) * (-4 * d) = -4 * ((A / d) * d) by ring, div_mul_cancel₀ _ hd]
    rw [show -4 * Real.sin (((p : ℝ) - 1) * Real.pi / n) *
        Real.sin (((p : ℝ) + 1) * Real.pi / n) =
      -4 * (Real.sin (((p : ℝ) - 1) * Real.pi / n) *
        Real.sin (((p : ℝ) + 1) * Real.pi / n)) by ring,
      halg _ _ (mul_ne_zero hm hplus)]
    ring
  · rw [SchurWeights.weight_eq_zero ha, zero_mul]
    by_cases ho : Odd p
    · have he : p = 1 ∨ p + 1 = n := by
        have hpmod := Nat.odd_iff.mp ho
        have hnmod := Nat.even_iff.mp hn
        simp only [SchurWeights.Active, ho, true_and, not_and, not_le] at ha
        omega
      rw [if_pos ho]
      rcases he with rfl | he
      · norm_num
      · have hn' : (n : ℝ) = (p : ℝ) + 1 := by exact_mod_cast he.symm
        rw [hn']
        ring
    · rw [if_neg ho, mul_zero]

theorem finiteKernel_difference_fourier (n : ℕ) (t b : ℝ) :
    finiteKernel n (t + b) - 2 * Real.cos b * finiteKernel n t + finiteKernel n (t - b) =
      (1 / 2) * ∑ p : Fin n, SchurWeights.weight n p *
        (2 * Real.cos (p * b) - 2 * Real.cos b) * Real.cos (p * t) := by
  have hp (p : Fin n) :
      SchurWeights.weight n p * Real.cos (p * (t + b)) -
        2 * Real.cos b * (SchurWeights.weight n p * Real.cos (p * t)) +
          SchurWeights.weight n p * Real.cos (p * (t - b)) =
      SchurWeights.weight n p * (2 * Real.cos (p * b) - 2 * Real.cos b) * Real.cos (p * t) := by
    rw [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
    ring
  have hs := Finset.sum_congr (s₁ := Finset.univ) rfl (fun p _ => hp p)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  unfold finiteKernel
  linear_combination hs / 2

theorem finiteKernel_recurrence {n : ℕ} (hn : Even n) (hn0 : 0 < n) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 Real.pi)
    (hroot : Complex.exp ((t : ℂ) * Complex.I) ^ n = 1) :
    finiteKernel n (t + 2 * Real.pi / n) -
      2 * Real.cos (2 * Real.pi / n) * finiteKernel n t +
        finiteKernel n (t - 2 * Real.pi / n) =
      2 * Real.sin (Real.pi / n) ^ 2 * Real.cos t / Real.sin t ^ 2 := by
  rw [finiteKernel_difference_fourier]
  simp_rw [weight_difference hn (Fin.isLt _)]
  rw [show (∑ p : Fin n, (-4 * Real.sin (Real.pi / n) ^ 2 / n) *
      (if Odd p.val then ((p : ℝ) - 1) * ((n : ℝ) - p - 1) else 0) * Real.cos (p * t)) =
      (-4 * Real.sin (Real.pi / n) ^ 2 / n) *
        ∑ p ∈ Finset.range n, if Odd p then
          ((p : ℝ) - 1) * ((n : ℝ) - p - 1) * Real.cos (p * t) else 0 by
    rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> ring]
  rw [odd_polynomial_cosine_sum hn ht hroot]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0.ne'
  field_simp
  ring

theorem grid_root {n : ℕ} (hn : 0 < n) (r : ℕ) :
    Complex.exp (((2 * Real.pi * r / n : ℝ) : ℂ) * Complex.I) ^ n = 1 := by
  rw [← Complex.exp_nat_mul]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (n : ℂ) * (((2 * Real.pi * r / n : ℝ) : ℂ) * Complex.I) =
      (r : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [he, Complex.exp_nat_mul_two_pi_mul_I]

theorem finiteKernel_grid_recurrence {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (hrm : r < m) :
    let n := 2 * m
    let b := 2 * Real.pi / n
    finiteKernel n ((r + 1) * b) - 2 * Real.cos b * finiteKernel n (r * b) +
      finiteKernel n (((r : ℝ) - 1) * b) =
        2 * Real.sin (b / 2) ^ 2 * Real.cos (r * b) / Real.sin (r * b) ^ 2 := by
  dsimp only
  have hn : 0 < 2 * m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hrmR : (r : ℝ) < m := by exact_mod_cast hrm
  have ht : 2 * Real.pi * r / (2 * m : ℕ) ∈ Set.Ioo 0 Real.pi := by
    constructor
    · positivity
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (2 * m : ℕ))).mpr
      push_cast
      nlinarith [pi_pos]
  have h := finiteKernel_recurrence (even_two_mul m) hn ht (grid_root hn r)
  convert h using 1 <;> congr 2 <;> push_cast <;> ring

end
end StructuralNote.FixedDualClassificationRecurrence
