import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! Exact elementary integral needed to evaluate the even limit series. -/

namespace StructuralNote.RewrittenSeriesIntegral

open Real Set MeasureTheory
open scoped Interval
noncomputable section

def density (y : ℝ) : ℝ :=
  3 * y ^ 2 / ((y + 1) * (y ^ 2 - y + 1) * (y ^ 2 + y + 1))

def primitive (y : ℝ) : ℝ :=
  Real.log (y + 1) + (1 / 4) * Real.log (y ^ 2 - y + 1) -
    (3 / 4) * Real.log (y ^ 2 + y + 1) +
    (Real.sqrt 3 / 2) * (Real.arctan ((2 * y - 1) / Real.sqrt 3) -
      Real.arctan ((2 * y + 1) / Real.sqrt 3))

theorem quadratic_minus_pos (y : ℝ) : 0 < y ^ 2 - y + 1 := by
  nlinarith [sq_nonneg (y - 1 / 2)]

theorem quadratic_plus_pos (y : ℝ) : 0 < y ^ 2 + y + 1 := by
  nlinarith [sq_nonneg (y + 1 / 2)]

theorem denominator_pos {y : ℝ} (hy : 0 ≤ y) :
    0 < (y + 1) * (y ^ 2 - y + 1) * (y ^ 2 + y + 1) :=
  mul_pos (mul_pos (by linarith) (quadratic_minus_pos y)) (quadratic_plus_pos y)

theorem density_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ density y :=
  div_nonneg (by positivity) (denominator_pos hy).le

theorem density_le_three {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) : density y ≤ 3 := by
  apply (div_le_iff₀ (denominator_pos hy.1)).2
  have he : (y + 1) * (y ^ 2 - y + 1) * (y ^ 2 + y + 1) =
      1 + y + y ^ 2 + y ^ 3 + y ^ 4 + y ^ 5 := by ring
  rw [he]
  have h3 : 0 ≤ y ^ 3 := pow_nonneg hy.1 _
  have h5 : 0 ≤ y ^ 5 := pow_nonneg hy.1 _
  nlinarith [sq_nonneg (y ^ 2)]

theorem density_continuousOn : ContinuousOn density (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  exact fun y hy => (denominator_pos hy.1).ne'

theorem density_integrable : IntervalIntegrable density volume 0 1 :=
  density_continuousOn.intervalIntegrable_of_Icc (by norm_num)

theorem primitive_hasDerivAt {y : ℝ} (hy : 0 ≤ y) :
    HasDerivAt primitive (density y) y := by
  have h1 : y + 1 ≠ 0 := by linarith
  have hm := (quadratic_minus_pos y).ne'
  have hp := (quadratic_plus_pos y).ne'
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlog1 := ((hasDerivAt_id y).add_const 1).log h1
  have hlogm := ((((hasDerivAt_id y).pow 2).sub (hasDerivAt_id y)).add_const 1).log hm
  have hlogp := ((((hasDerivAt_id y).pow 2).add (hasDerivAt_id y)).add_const 1).log hp
  have hatm := ((((hasDerivAt_id y).const_mul 2).sub_const 1).div_const (Real.sqrt 3)).arctan
  have hatp := ((((hasDerivAt_id y).const_mul 2).add_const 1).div_const (Real.sqrt 3)).arctan
  have h := ((hlog1.add (hlogm.const_mul (1 / 4))).sub (hlogp.const_mul (3 / 4))).add
    ((hatm.sub hatp).const_mul (Real.sqrt 3 / 2))
  convert h using 1
  all_goals try rfl
  simp only [density, Pi.pow_apply, Pi.sub_apply, Pi.add_apply, id_eq,
    Nat.cast_ofNat, show 2 - 1 = 1 from rfl, pow_one, mul_one, div_pow, hs2]
  rw [show 1 + (2 * y - 1) ^ 2 / 3 = (4 / 3) * (y ^ 2 - y + 1) by ring,
    show 1 + (2 * y + 1) ^ 2 / 3 = (4 / 3) * (y ^ 2 + y + 1) by ring]
  have hm' : 1 - y + y ^ 2 ≠ 0 := by nlinarith [quadratic_minus_pos y]
  field_simp [h1, hm, hp, hs, hm']
  ring_nf
  field_simp [hm']
  ring

theorem primitive_endpoint_difference :
    primitive 1 - primitive 0 = Real.log 2 - (3 / 4) * Real.log 3 +
      Real.pi / (4 * Real.sqrt 3) := by
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have he : (3 : ℝ) / Real.sqrt 3 = Real.sqrt 3 := by
    apply (div_eq_iff hs).2
    nlinarith [hs2]
  norm_num only [primitive, one_pow, zero_pow (by decide : 2 ≠ 0),
    mul_one, mul_zero, sub_self, zero_sub, zero_add, add_zero, zero_mul]
  rw [he]
  simp only [one_div, neg_div, Real.arctan_neg, Real.arctan_inv_sqrt_three,
    Real.arctan_sqrt_three, Real.log_one, mul_zero, add_zero, sub_zero]
  field_simp
  ring_nf
  rw [hs2]
  ring

theorem integral_density :
    (∫ y in (0 : ℝ)..1, density y) =
      Real.log 2 - (3 / 4) * Real.log 3 + Real.pi / (4 * Real.sqrt 3) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => primitive_hasDerivAt (by simpa using hy.1)) density_integrable]
  exact primitive_endpoint_difference

end
end StructuralNote.RewrittenSeriesIntegral
