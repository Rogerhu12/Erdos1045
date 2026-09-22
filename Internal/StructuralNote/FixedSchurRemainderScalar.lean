import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The scalar logarithmic remainder used in the fixed-Schur source estimate. -/

namespace StructuralNote.FixedSchurRemainderScalar

open Complex
open scoped Topology

noncomputable section

def R (u x : ℂ) : ℂ :=
  Complex.log (1 - u ^ 2 / (1 + x) ^ 2) + u ^ 2

def D (u x : ℂ) : ℂ := (1 + x) ^ 2 - u ^ 2

private theorem one_add_norm_lower {x : ℂ} (hx : ‖x‖ ≤ 1 / 4) :
    (3 : ℝ) / 4 ≤ ‖1 + x‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-x)
  have h' : (1 : ℝ) - ‖x‖ ≤ ‖1 + x‖ := by
    simpa only [norm_one, norm_neg, sub_neg_eq_add] using h
  linarith

private theorem one_add_ne_zero {x : ℂ} (hx : ‖x‖ ≤ 1 / 4) :
    (1 + x : ℂ) ≠ 0 := by
  have h := one_add_norm_lower hx
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

private theorem denominator_lower {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    (1 : ℝ) / 2 ≤ ‖D u x‖ := by
  have ha := one_add_norm_lower hx
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 4) ha
  have husq : ‖u‖ ^ 2 ≤ (1 : ℝ) / 16 := by
    have h := mul_self_le_mul_self (norm_nonneg u) hu
    nlinarith
  have h := norm_sub_norm_le ((1 + x) ^ 2) (u ^ 2)
  rw [norm_pow, norm_pow] at h
  dsimp [D]
  nlinarith [husq, sq_nonneg (‖u‖ - 1 / 4)]

private theorem argument_mem_slitPlane {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    1 - u ^ 2 / (1 + x) ^ 2 ∈ Complex.slitPlane := by
  have ha := one_add_norm_lower hx
  have ha0 : 0 < ‖1 + x‖ := by linarith
  have ha2 : 0 < ‖1 + x‖ ^ 2 := sq_pos_of_pos ha0
  have hnum : ‖u‖ ^ 2 ≤ (1 : ℝ) / 16 := by
    have h := mul_self_le_mul_self (norm_nonneg u) hu
    nlinarith
  have hden : (9 : ℝ) / 16 ≤ ‖1 + x‖ ^ 2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 4) ha]
  have hquot : ‖u ^ 2 / (1 + x) ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, norm_pow]
    apply (div_lt_iff₀ ha2).2
    nlinarith
  have hh : ‖-(u ^ 2 / (1 + x) ^ 2)‖ < 1 := by
    simpa only [norm_neg] using hquot
  simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hh

private theorem denominator_ne_zero {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) : D u x ≠ 0 := by
  have h := denominator_lower hu hx
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

theorem hasDerivAt_R_u {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun w : ℂ => R w x)
      (2 * u * (1 - 1 / D u x)) u := by
  have hp := (hasDerivAt_id u).pow 2
  have hc := hasDerivAt_const u ((1 + x) ^ 2)
  have hq := hp.div_const ((1 + x) ^ 2)
  have hi := (hasDerivAt_const u (1 : ℂ)).sub hq
  have hl := hi.clog (argument_mem_slitPlane hu hx)
  have hr := hl.add hp
  have harg := Complex.slitPlane_ne_zero (argument_mem_slitPlane hu hx)
  have ha2 := pow_ne_zero 2 (one_add_ne_zero hx)
  apply hr.congr_deriv
  dsimp [R, D]
  field_simp [D, harg, ha2, one_add_ne_zero hx, denominator_ne_zero hu hx]
  ring

theorem hasDerivAt_R_x {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun y : ℂ => R u y)
      (2 * u ^ 2 / ((1 + x) * D u x)) x := by
  have ha : HasDerivAt (fun y : ℂ => 1 + y) 1 x := by
    change HasDerivAt ((fun y : ℂ => 1) + id) 1 x
    simpa only [zero_add] using
      (hasDerivAt_const x (1 : ℂ)).add (hasDerivAt_id x)
  have hp := ha.pow 2
  have hc := hasDerivAt_const x (u ^ 2)
  have hq := hc.div hp (pow_ne_zero 2 (one_add_ne_zero hx))
  have hi := (hasDerivAt_const x (1 : ℂ)).sub hq
  have hl := hi.clog (argument_mem_slitPlane hu hx)
  have hr := hl.add (hasDerivAt_const x (u ^ 2))
  have harg := Complex.slitPlane_ne_zero (argument_mem_slitPlane hu hx)
  have ha2 := pow_ne_zero 2 (one_add_ne_zero hx)
  apply hr.congr_deriv
  dsimp [R, D]
  field_simp [D, harg, ha2, one_add_ne_zero hx, denominator_ne_zero hu hx]
  ring

private theorem denominator_sub_one_norm_le {u x : ℂ}
    (hx : ‖x‖ ≤ 1 / 4) :
    ‖D u x - 1‖ ≤ 4 * ‖x‖ + 2 * ‖u‖ ^ 2 := by
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hx2 : ‖x‖ ^ 2 ≤ (1 : ℝ) / 4 * ‖x‖ := by
    have h := mul_self_le_mul_self hx0 hx
    nlinarith
  calc
    ‖D u x - 1‖ = ‖2 * x + x ^ 2 - u ^ 2‖ := by
      congr 1
      dsimp [D]
      ring
    _ ≤ ‖2 * x + x ^ 2‖ + ‖u ^ 2‖ := norm_sub_le _ _
    _ ≤ (‖2 * x‖ + ‖x ^ 2‖) + ‖u ^ 2‖ := by
      gcongr
      exact norm_add_le (2 * x) (x ^ 2)
    _ = 2 * ‖x‖ + ‖x‖ ^ 2 + ‖u‖ ^ 2 := by
      rw [norm_mul, norm_pow, norm_pow]
      norm_num
    _ ≤ 4 * ‖x‖ + 2 * ‖u‖ ^ 2 := by
      nlinarith

private theorem norm_one_sub_inv_denominator_le {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    ‖1 - 1 / D u x‖ ≤ 8 * (‖x‖ + ‖u‖ ^ 2) := by
  have hDpos : 0 < ‖D u x‖ := by
    have h := denominator_lower hu hx
    linarith
  have hiden : 1 - 1 / D u x = (D u x - 1) / D u x := by
    field_simp [denominator_ne_zero hu hx]
  rw [hiden, norm_div]
  calc
    ‖D u x - 1‖ / ‖D u x‖ ≤ 2 * ‖D u x - 1‖ := by
      apply (div_le_iff₀ hDpos).2
      have hmul :=
        mul_le_mul_of_nonneg_left (denominator_lower hu hx)
          (norm_nonneg (D u x - 1))
      nlinarith
    _ ≤ 2 * (4 * ‖x‖ + 2 * ‖u‖ ^ 2) := by
      gcongr
      exact denominator_sub_one_norm_le hx
    _ ≤ 8 * (‖x‖ + ‖u‖ ^ 2) := by
      nlinarith [sq_nonneg ‖u‖]

theorem norm_deriv_R_u_le {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    ‖2 * u * (1 - 1 / D u x)‖ ≤
      32 * ‖u‖ * (‖x‖ + ‖u‖ ^ 2) := by
  have hfac := norm_one_sub_inv_denominator_le hu hx
  calc
    ‖2 * u * (1 - 1 / D u x)‖ =
        2 * ‖u‖ * ‖1 - 1 / D u x‖ := by
      rw [norm_mul, norm_mul]
      norm_num
    _ ≤ 2 * ‖u‖ * (8 * (‖x‖ + ‖u‖ ^ 2)) := by
      gcongr
    _ ≤ 32 * ‖u‖ * (‖x‖ + ‖u‖ ^ 2) := by
      nlinarith [mul_nonneg (norm_nonneg u)
        (add_nonneg (norm_nonneg x) (sq_nonneg ‖u‖))]

theorem norm_deriv_R_x_le {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    ‖2 * u ^ 2 / ((1 + x) * D u x)‖ ≤ 32 * ‖u‖ ^ 2 := by
  have ha := one_add_norm_lower hx
  have hD := denominator_lower hu hx
  have hprod : (3 : ℝ) / 8 ≤ ‖1 + x‖ * ‖D u x‖ := by
    have hmul := mul_le_mul ha hD (by positivity : 0 ≤ (1 : ℝ) / 2)
      (norm_nonneg (1 + x))
    nlinarith
  have hprodpos : 0 < ‖1 + x‖ * ‖D u x‖ := by linarith
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  norm_num
  apply (div_le_iff₀ hprodpos).2
  nlinarith [sq_nonneg ‖u‖]

end
end StructuralNote.FixedSchurRemainderScalar
