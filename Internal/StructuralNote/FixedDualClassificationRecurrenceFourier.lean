import StructuralNote.FixedDualClassificationKernel
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! Exact finite Fourier sums for the quadratic frequency polynomial. -/

namespace StructuralNote.FixedDualClassificationRecurrenceFourier

open Complex Real
open scoped BigOperators
noncomputable section

theorem linear_geometric_sum (n : ℕ) (z : ℂ) :
    (1 - z) ^ 2 * (∑ p ∈ Finset.range n, (p : ℂ) * z ^ p) =
      z - n * z ^ n + ((n : ℂ) - 1) * z ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    simp only [pow_succ]
    ring

theorem quadratic_geometric_sum (n : ℕ) (z : ℂ) :
    (1 - z) ^ 3 * (∑ p ∈ Finset.range n, (p : ℂ) ^ 2 * z ^ p) =
      z + z ^ 2 - (n : ℂ) ^ 2 * z ^ n +
        (2 * (n : ℂ) ^ 2 - 2 * n - 1) * z ^ (n + 1) -
          ((n : ℂ) - 1) ^ 2 * z ^ (n + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    simp only [pow_succ]
    ring

theorem quadratic_root_sum {n : ℕ} {z : ℂ} (hz : z ^ n = 1) (hne : z ≠ 1) :
    (∑ p ∈ Finset.range n, (p : ℂ) * ((n : ℂ) - p) * z ^ p) =
      2 * n * z / (1 - z) ^ 2 := by
  have hlin := linear_geometric_sum n z
  have hquad := quadratic_geometric_sum n z
  rw [pow_add, pow_add, hz] at hquad
  rw [pow_add, hz] at hlin
  norm_num only [pow_one, one_mul] at hlin hquad
  have hid : (1 - z) ^ 3 * (∑ p ∈ Finset.range n, (p : ℂ) * ((n : ℂ) - p) * z ^ p) =
      (1 - z) * (2 * n * z) := by
    have he : (∑ p ∈ Finset.range n, (p : ℂ) * ((n : ℂ) - p) * z ^ p) =
        (n : ℂ) * (∑ p ∈ Finset.range n, (p : ℂ) * z ^ p) -
          (∑ p ∈ Finset.range n, (p : ℂ) ^ 2 * z ^ p) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    rw [he]
    linear_combination (n : ℂ) * (1 - z) * hlin - hquad
  have h1 : 1 - z ≠ 0 := sub_ne_zero.mpr hne.symm
  apply (eq_div_iff (pow_ne_zero 2 h1)).mpr
  apply mul_left_cancel₀ h1
  linear_combination hid

theorem exp_chord_identity (t : ℝ) :
    (1 - Complex.exp ((t : ℂ) * Complex.I)) ^ 2 =
      ((-4 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
  have he := Complex.exp_ofReal_mul_I t
  rw [he]
  have ht : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have h := Real.cos_two_mul (t / 2)
    rw [show 2 * (t / 2) = t by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  apply Complex.ext
  · simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sin_sq_add_cos_sq t]
  · simp only [pow_two, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    rw [ht]
    ring

theorem quadratic_cosine_sum {n : ℕ} {t : ℝ}
    (hroot : Complex.exp ((t : ℂ) * Complex.I) ^ n = 1)
    (hsin : Real.sin (t / 2) ≠ 0) :
    (∑ p ∈ Finset.range n, (p : ℝ) * ((n : ℝ) - p) * Real.cos (p * t)) =
      -(n : ℝ) / (2 * Real.sin (t / 2) ^ 2) := by
  let z := Complex.exp ((t : ℂ) * Complex.I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hc : (1 - z) ^ 2 = ((-4 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) * z := exp_chord_identity t
  have hne : z ≠ 1 := by
    intro he
    rw [he] at hc
    have hn : ((-4 * Real.sin (t / 2) ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast mul_ne_zero (by norm_num : (-4 : ℝ) ≠ 0) (pow_ne_zero 2 hsin)
    apply hn
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_one] using hc.symm
  have h := quadratic_root_sum hroot hne
  have hval : (∑ p ∈ Finset.range n, (p : ℂ) * ((n : ℂ) - p) * z ^ p) =
      (-(n : ℝ) / (2 * Real.sin (t / 2) ^ 2) : ℝ) := by
    rw [h, hc]
    push_cast
    field_simp
    ring
  have hre := congrArg Complex.re hval
  simp only [Complex.re_sum, Complex.ofReal_re] at hre
  convert hre using 1
  apply Finset.sum_congr rfl
  intro p _
  have hp : z ^ p = Complex.exp (((p * t : ℝ) : ℂ) * Complex.I) := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hp]
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.natCast_re,
    Complex.natCast_im, sub_zero, zero_mul, mul_zero, sub_self, add_zero,
    Complex.exp_ofReal_mul_I_re]

end
end StructuralNote.FixedDualClassificationRecurrenceFourier
