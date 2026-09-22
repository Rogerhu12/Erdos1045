import StructuralNote.FixedDualArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Actual transcendental functions in §8.2 and Appendix A. The primitive and
the inhomogeneous differential equation are proved by differentiation. This
does not establish the root count or the numerical table of enclosures. -/

namespace StructuralNote.FixedDualPrimitive

open Real
open scoped Topology
noncomputable section

def kernel (u : ℝ) : ℝ :=
  -(1 / 2) * cos u * (1 + log (2 * sin u)) + (1 / 2) * (Real.pi / 2 - u) * sin u

def witness (b u : ℝ) : ℝ := cos (3 * u) + b * sin (3 * u) - 2 * kernel u

def primitive (b u : ℝ) : ℝ :=
  sin (3 * u) / 3 - b * cos (3 * u) / 3 + sin u * log (2 * sin u) +
    (Real.pi / 2 - u) * cos u + sin u

theorem witness_expand (b u : ℝ) :
    witness b u = cos (3 * u) + b * sin (3 * u) +
      cos u * (1 + log (2 * sin u)) - (Real.pi / 2 - u) * sin u := by
  unfold witness kernel
  ring

theorem log_sine_hasDerivAt {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt (fun v => log (2 * sin v)) (cos u / sin u) u := by
  have hd := ((hasDerivAt_sin u).const_mul 2).log (mul_ne_zero (by norm_num) hu)
  convert hd using 1
  field_simp

/-- The actual formula (A.4) differentiates to the actual witness (8.4). -/
theorem primitive_hasDerivAt (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt (primitive b) (witness b u) u := by
  have ht := (hasDerivAt_id u).const_mul 3
  have hs3 := ht.sin
  have hc3 := ht.cos
  have hd := (((hs3.div_const 3).sub ((hc3.const_mul b).div_const 3)).add
    ((hasDerivAt_sin u).mul (log_sine_hasDerivAt hu))).add
      (((hasDerivAt_const u (Real.pi / 2)).sub (hasDerivAt_id u)).mul (hasDerivAt_cos u))
  have hd' := hd.add (hasDerivAt_sin u)
  convert hd' using 1 <;> try rfl
  rw [witness_expand]
  simp only [id_eq, mul_one, Pi.sub_apply]
  field_simp
  ring

theorem primitive_deriv (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    deriv (primitive b) u = witness b u := (primitive_hasDerivAt b hu).deriv

theorem primitive_hasDerivAt_on_interval (b : ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioo 0 Real.pi) : HasDerivAt (primitive b) (witness b u) u :=
  primitive_hasDerivAt b (ne_of_gt (sin_pos_of_pos_of_lt_pi hu.1 hu.2))

def witnessFirst (b u : ℝ) : ℝ :=
  -3 * sin (3 * u) + 3 * b * cos (3 * u) - sin u * log (2 * sin u) +
    cos u ^ 2 / sin u - (Real.pi / 2 - u) * cos u

def witnessSecond (b u : ℝ) : ℝ :=
  -9 * cos (3 * u) - 9 * b * sin (3 * u) - cos u * log (2 * sin u) -
    2 * cos u - cos u ^ 3 / sin u ^ 2 + (Real.pi / 2 - u) * sin u

theorem witness_hasDerivAt (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt (witness b) (witnessFirst b u) u := by
  have ht := (hasDerivAt_id u).const_mul 3
  have hv := (hasDerivAt_const u (Real.pi / 2)).sub (hasDerivAt_id u)
  have hd := (((ht.cos).add (ht.sin.const_mul b)).add
    ((hasDerivAt_cos u).mul ((log_sine_hasDerivAt hu).const_add 1))).sub
      (hv.mul (hasDerivAt_sin u))
  convert hd using 1 <;> try rfl
  · funext v
    exact witness_expand b v
  · simp only [witnessFirst, id_eq, mul_one, Pi.sub_apply]
    field_simp
    ring

theorem witnessFirst_hasDerivAt (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt (witnessFirst b) (witnessSecond b u) u := by
  have ht := (hasDerivAt_id u).const_mul 3
  have hv := (hasDerivAt_const u (Real.pi / 2)).sub (hasDerivAt_id u)
  have hd := (((((ht.sin).const_mul (-3)).add ((ht.cos).const_mul (3 * b))).sub
    ((hasDerivAt_sin u).mul (log_sine_hasDerivAt hu))).add
      (((hasDerivAt_cos u).pow 2).div (hasDerivAt_sin u) hu)).sub
        (hv.mul (hasDerivAt_cos u))
  convert hd using 1 <;> try rfl
  simp only [witnessSecond, id_eq, mul_one, Pi.sub_apply, Pi.pow_apply]
  field_simp
  ring

theorem witness_second_hasDerivAt (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt (deriv (witness b)) (witnessSecond b u) u := by
  apply (witnessFirst_hasDerivAt b hu).congr_of_eventuallyEq
  filter_upwards [continuous_sin.continuousAt.eventually_ne hu] with v hv
  exact (witness_hasDerivAt b hv).deriv

/-- The sign is negative: `H_b'' + H_b = -8(cos 3u + b sin 3u) - cos u / sin² u`. -/
theorem witness_differential_equation (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    deriv (deriv (witness b)) u + witness b u =
      -8 * (cos (3 * u) + b * sin (3 * u)) - cos u / sin u ^ 2 := by
  rw [(witness_second_hasDerivAt b hu).deriv, witness_expand]
  unfold witnessSecond
  have htrig : cos u * (sin u ^ 2 + cos u ^ 2) = cos u := by
    rw [sin_sq_add_cos_sq, mul_one]
  field_simp
  nlinarith [htrig]

theorem witness_differential_equation_on_interval (b : ℝ) {u : ℝ}
    (hu : u ∈ Set.Ioo 0 Real.pi) :
    deriv (deriv (witness b)) u + witness b u =
      -8 * (cos (3 * u) + b * sin (3 * u)) - cos u / sin u ^ 2 :=
  witness_differential_equation b (ne_of_gt (sin_pos_of_pos_of_lt_pi hu.1 hu.2))

theorem primitive_zero (b : ℝ) : primitive b 0 = Real.pi / 2 - b / 3 := by
  simp only [primitive, mul_zero, sin_zero, cos_zero, zero_div, mul_one, zero_mul,
    sub_zero, add_zero]
  ring

theorem primitive_pi_div_two (b : ℝ) :
    primitive b (Real.pi / 2) = log 2 + 2 / 3 := by
  simp only [primitive, sin_three_mul, cos_three_mul, sin_pi_div_two, cos_pi_div_two]
  ring

theorem witness_reflection (b u : ℝ) : witness b (Real.pi - u) = -witness (-b) u := by
  simp only [witness_expand, sin_three_mul, cos_three_mul, sin_pi_sub, cos_pi_sub]
  ring

theorem witness_pi_div_two (b : ℝ) : witness b (Real.pi / 2) = -b := by
  simp only [witness_expand, sin_three_mul, cos_three_mul, sin_pi_div_two, cos_pi_div_two]
  ring

/-- The Wronskian expression used in the analytic zero count. -/
def wronskian (b u : ℝ) : ℝ := cos u * witnessFirst b u + sin u * witness b u

theorem wronskian_eq_deriv (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    wronskian b u = cos u * deriv (witness b) u + sin u * witness b u := by
  rw [(witness_hasDerivAt b hu).deriv]
  rfl

theorem wronskian_hasDerivAt (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    HasDerivAt (wronskian b) (cos u * (witnessSecond b u + witness b u)) u := by
  have hd := ((hasDerivAt_cos u).mul (witnessFirst_hasDerivAt b hu)).add
    ((hasDerivAt_sin u).mul (witness_hasDerivAt b hu))
  convert hd using 1 <;> try rfl
  ring

theorem wronskian_deriv (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) :
    deriv (wronskian b) u =
      cos u * (-8 * (cos (3 * u) + b * sin (3 * u)) - cos u / sin u ^ 2) := by
  rw [(wronskian_hasDerivAt b hu).deriv]
  have h := witness_differential_equation b hu
  rw [(witness_second_hasDerivAt b hu).deriv] at h
  rw [h]

theorem quotient_hasDerivAt (b : ℝ) {u : ℝ} (hu : sin u ≠ 0) (hc : cos u ≠ 0) :
    HasDerivAt (fun v => witness b v / cos v) (wronskian b u / cos u ^ 2) u := by
  have hd := (witness_hasDerivAt b hu).div (hasDerivAt_cos u) hc
  convert hd using 1 <;> try rfl
  unfold wronskian
  ring

theorem wronskian_pi_div_two (b : ℝ) : wronskian b (Real.pi / 2) = -b := by
  simp only [wronskian, sin_pi_div_two, cos_pi_div_two, zero_mul, one_mul,
    zero_add, witness_pi_div_two]

end
end StructuralNote.FixedDualPrimitive
