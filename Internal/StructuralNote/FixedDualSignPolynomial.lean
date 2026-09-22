import StructuralNote.FixedDualPrimitive
import Mathlib.Algebra.Polynomial.RuleOfSigns

/-! The actual polynomial governing the Wronskian derivative in Appendix A. -/

namespace StructuralNote.FixedDualSignPolynomial

open Real Polynomial FixedDualPrimitive
noncomputable section

def signPolynomial (b : ℝ) : Polynomial ℝ :=
  C (8 * b) * X ^ 5 + C 23 * X ^ 4 - C (24 * b) * X ^ 3 - C 10 * X ^ 2 - C 1

theorem signPolynomial_eval (b t : ℝ) :
    (signPolynomial b).eval t = 8 * b * t ^ 5 + 23 * t ^ 4 - 24 * b * t ^ 3 - 10 * t ^ 2 - 1 := by
  simp [signPolynomial]

theorem signPolynomial_degree {b : ℝ} (hb : b ≠ 0) : (signPolynomial b).degree = 5 := by
  unfold signPolynomial
  compute_degree!

theorem signPolynomial_coeffList {b : ℝ} (hb : b ≠ 0) :
    (signPolynomial b).coeffList = [8 * b, 23, -24 * b, -10, 0, -1] := by
  rw [Polynomial.coeffList, signPolynomial_degree hb]
  change [(signPolynomial b).coeff 5, (signPolynomial b).coeff 4,
    (signPolynomial b).coeff 3, (signPolynomial b).coeff 2,
    (signPolynomial b).coeff 1, (signPolynomial b).coeff 0] = _
  simp only [signPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  norm_num

theorem positive_signVariations {b : ℝ} (hb : 0 < b) :
    (signPolynomial b).signVariations = 1 := by
  rw [Polynomial.signVariations, signPolynomial_coeffList hb.ne']
  have hp : 0 < 8 * b := by positivity
  have hn : -24 * b < 0 := by nlinarith
  simp only [List.map_cons, List.map_nil, sign_pos hp, sign_neg hn]
  norm_num [List.destutter]

theorem negative_signVariations {b : ℝ} (hb : 0 < b) :
    (signPolynomial (-b)).signVariations = 2 := by
  rw [Polynomial.signVariations, signPolynomial_coeffList (neg_ne_zero.mpr hb.ne')]
  have hn : 8 * -b < 0 := by nlinarith
  have hp : 0 < -24 * -b := by nlinarith
  simp only [List.map_cons, List.map_nil, sign_pos hp, sign_neg hn]
  norm_num [List.destutter]

theorem positive_polynomial_root_bound {b : ℝ} (hb : 0 < b) :
    (signPolynomial b).roots.countP (0 < ·) ≤ 1 := by
  simpa [positive_signVariations hb] using (signPolynomial b).roots_countP_pos_le_signVariations

theorem negative_polynomial_root_bound {b : ℝ} (hb : 0 < b) :
    (signPolynomial (-b)).roots.countP (0 < ·) ≤ 2 := by
  simpa [negative_signVariations hb] using (signPolynomial (-b)).roots_countP_pos_le_signVariations

/-- The manuscript's tangent substitution, without real fractional powers. -/
theorem wronskian_deriv_polynomial (b : ℝ) {u : ℝ} (hs : sin u ≠ 0) (hc : cos u ≠ 0) :
    deriv (wronskian b) u = cos u ^ 6 / sin u ^ 2 * (signPolynomial b).eval (tan u) := by
  have he : cos u ^ 6 * (signPolynomial b).eval (tan u) =
      8 * b * sin u ^ 5 * cos u + 23 * sin u ^ 4 * cos u ^ 2 -
        24 * b * sin u ^ 3 * cos u ^ 3 - 10 * sin u ^ 2 * cos u ^ 4 - cos u ^ 6 := by
    rw [signPolynomial_eval, tan_eq_sin_div_cos]
    field_simp
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero 2 hs)).2
  rw [he]
  rw [wronskian_deriv b hs, sin_three_mul, cos_three_mul]
  have hh := sin_sq_add_cos_sq u
  field_simp
  linear_combination (24 * b * sin u ^ 3 - 23 * cos u * sin u ^ 2 +
    cos u ^ 3 + cos u) * hh

end
end StructuralNote.FixedDualSignPolynomial
