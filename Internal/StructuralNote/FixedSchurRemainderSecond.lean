import StructuralNote.FixedSchurRemainderScalar
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Second derivatives of the scalar logarithmic Schur remainder. -/

namespace StructuralNote.FixedSchurRemainderSecond

open StructuralNote.FixedSchurRemainderScalar
open scoped Topology

noncomputable section

def Ru (u x : ℂ) : ℂ := 2 * u * (1 - 1 / D u x)

def Rx (u x : ℂ) : ℂ := 2 * u ^ 2 / ((1 + x) * D u x)

private theorem one_add_norm_lower {x : ℂ} (hx : ‖x‖ ≤ 1 / 4) :
    (3 : ℝ) / 4 ≤ ‖1 + x‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (-x)
  have h' : (1 : ℝ) - ‖x‖ ≤ ‖1 + x‖ := by
    simpa only [norm_one, norm_neg, sub_neg_eq_add] using h
  linarith

private theorem one_add_norm_upper {x : ℂ} (hx : ‖x‖ ≤ 1 / 4) :
    ‖1 + x‖ ≤ (5 : ℝ) / 4 := by
  have h := norm_add_le (1 : ℂ) x
  norm_num at h
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

private theorem denominator_ne_zero {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) : D u x ≠ 0 := by
  have h := denominator_lower hu hx
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

private theorem norm_one_sub_inv_D_le {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    ‖1 - 1 / D u x‖ ≤ 8 * (‖x‖ + ‖u‖ ^ 2) := by
  have hDpos : 0 < ‖D u x‖ := by
    have h := denominator_lower hu hx
    linarith
  have hsub : ‖D u x - 1‖ ≤ 4 * ‖x‖ + 2 * ‖u‖ ^ 2 := by
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
  have hiden : 1 - 1 / D u x = (D u x - 1) / D u x := by
    field_simp [denominator_ne_zero hu hx]
  rw [hiden, norm_div]
  calc
    ‖D u x - 1‖ / ‖D u x‖ ≤ 2 * ‖D u x - 1‖ := by
      apply (div_le_iff₀ hDpos).2
      have hmul := mul_le_mul_of_nonneg_left (denominator_lower hu hx)
        (norm_nonneg (D u x - 1))
      nlinarith
    _ ≤ 2 * (4 * ‖x‖ + 2 * ‖u‖ ^ 2) := by
      gcongr
    _ ≤ 8 * (‖x‖ + ‖u‖ ^ 2) := by
      nlinarith [sq_nonneg ‖u‖]

theorem hasDerivAt_actual_R_u {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun w : ℂ => R w x) (Ru u x) u := by
  simpa only [Ru] using hasDerivAt_R_u hu hx

theorem hasDerivAt_actual_R_x {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun y : ℂ => R u y) (Rx u x) x := by
  simpa only [Rx] using hasDerivAt_R_x hu hx

theorem hasDerivAt_Ru_u {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun w : ℂ => Ru w x)
      (2 * (1 - 1 / D u x) - 4 * u ^ 2 / (D u x) ^ 2) u := by
  have hD : HasDerivAt (fun w : ℂ => D w x) (-2 * u) u := by
    have h := (hasDerivAt_const u ((1 + x) ^ 2)).sub ((hasDerivAt_id u).pow 2)
    have h' : HasDerivAt (fun w : ℂ => D w x)
        (0 - (2 : ℂ) * u ^ (2 - 1) * 1) u :=
      h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun w => by simp [D]))
    exact h'.congr_deriv (by ring)
  have hinv := (hasDerivAt_const u (1 : ℂ)).div hD
    (denominator_ne_zero hu hx)
  have hone := (hasDerivAt_const u (1 : ℂ)).sub hinv
  have hleft := (hasDerivAt_const u (2 : ℂ)).mul (hasDerivAt_id u)
  have hprod := hleft.mul hone
  apply hprod.congr_deriv
  dsimp [Ru, D]
  field_simp [denominator_ne_zero hu hx]
  ring

theorem hasDerivAt_Ru_x {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun y : ℂ => Ru u y)
      (4 * u * (1 + x) / (D u x) ^ 2) x := by
  have hone : HasDerivAt (fun y : ℂ => 1 + y) 1 x := by
    change HasDerivAt ((fun y : ℂ => 1) + id) 1 x
    simpa only [zero_add] using
      (hasDerivAt_const x (1 : ℂ)).add (hasDerivAt_id x)
  have hD : HasDerivAt (fun y : ℂ => D u y) (2 * (1 + x)) x := by
    have h := (hone.pow 2).sub (hasDerivAt_const x (u ^ 2))
    have h' : HasDerivAt (fun y : ℂ => D u y)
        (↑2 * (1 + x) ^ (2 - 1) * 1 - 0) x :=
      h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by simp [D]))
    exact h'.congr_deriv (by ring)
  have hinv := (hasDerivAt_const x (1 : ℂ)).div hD
    (denominator_ne_zero hu hx)
  have hone' := (hasDerivAt_const x (1 : ℂ)).sub hinv
  have hprod := (hasDerivAt_const x (2 * u)).mul hone'
  apply hprod.congr_deriv
  dsimp [Ru, D]
  field_simp [denominator_ne_zero hu hx]
  ring

theorem hasDerivAt_Rx_x {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun y : ℂ => Rx u y)
      (-2 * u ^ 2 * (3 * (1 + x) ^ 2 - u ^ 2) /
        ((1 + x) ^ 2 * (D u x) ^ 2)) x := by
  have hone : HasDerivAt (fun y : ℂ => 1 + y) 1 x := by
    change HasDerivAt ((fun y : ℂ => 1) + id) 1 x
    simpa only [zero_add] using
      (hasDerivAt_const x (1 : ℂ)).add (hasDerivAt_id x)
  have hD : HasDerivAt (fun y : ℂ => D u y) (2 * (1 + x)) x := by
    have h := (hone.pow 2).sub (hasDerivAt_const x (u ^ 2))
    have h' : HasDerivAt (fun y : ℂ => D u y)
        (↑2 * (1 + x) ^ (2 - 1) * 1 - 0) x :=
      h.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by simp [D]))
    exact h'.congr_deriv (by ring)
  have hden := hone.mul hD
  have hq := (hasDerivAt_const x (2 * u ^ 2)).div hden
    (mul_ne_zero (one_add_ne_zero hx) (denominator_ne_zero hu hx))
  apply hq.congr_deriv
  dsimp [Rx, D]
  field_simp [one_add_ne_zero hx, denominator_ne_zero hu hx]
  ring

theorem norm_deriv_Ru_u_le {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    ‖2 * (1 - 1 / D u x) - 4 * u ^ 2 / (D u x) ^ 2‖ ≤
      32 * (‖x‖ + ‖u‖ ^ 2) := by
  have hfac := norm_one_sub_inv_D_le hu hx
  have hfirst : ‖2 * (1 - 1 / D u x)‖ ≤
      16 * (‖x‖ + ‖u‖ ^ 2) := by
    calc
      ‖2 * (1 - 1 / D u x)‖ = 2 * ‖1 - 1 / D u x‖ := by
        rw [norm_mul]
        norm_num
      _ ≤ 2 * (8 * (‖x‖ + ‖u‖ ^ 2)) := by
        gcongr
      _ = 16 * (‖x‖ + ‖u‖ ^ 2) := by ring
  have hDsq : (1 : ℝ) / 4 ≤ ‖D u x‖ ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (denominator_lower hu hx)
    nlinarith
  have hsecond : ‖4 * u ^ 2 / (D u x) ^ 2‖ ≤ 16 * ‖u‖ ^ 2 := by
    rw [norm_div, norm_mul, norm_pow]
    norm_num
    have hDpos : 0 < ‖D u x‖ ^ 2 := by linarith
    apply (div_le_iff₀ hDpos).2
    have h := mul_le_mul_of_nonneg_left hDsq (sq_nonneg ‖u‖)
    nlinarith
  calc
    ‖2 * (1 - 1 / D u x) - 4 * u ^ 2 / (D u x) ^ 2‖ ≤
        ‖2 * (1 - 1 / D u x)‖ + ‖4 * u ^ 2 / (D u x) ^ 2‖ :=
      norm_sub_le _ _
    _ ≤ 16 * (‖x‖ + ‖u‖ ^ 2) + 16 * ‖u‖ ^ 2 :=
      add_le_add hfirst hsecond
    _ ≤ 32 * (‖x‖ + ‖u‖ ^ 2) := by
      nlinarith [sq_nonneg ‖u‖, norm_nonneg x]

theorem norm_deriv_Ru_x_le {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    ‖4 * u * (1 + x) / (D u x) ^ 2‖ ≤ 32 * ‖u‖ := by
  have ha := one_add_norm_upper hx
  have hDsq : (1 : ℝ) / 4 ≤ ‖D u x‖ ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (denominator_lower hu hx)
    nlinarith
  rw [norm_div, norm_mul, norm_mul, norm_pow]
  norm_num
  have hDpos : 0 < ‖D u x‖ ^ 2 := by linarith
  apply (div_le_iff₀ hDpos).2
  have hnum : 4 * ‖u‖ * ‖1 + x‖ ≤ 5 * ‖u‖ := by
    have h := mul_le_mul_of_nonneg_left ha (norm_nonneg u)
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hDsq (norm_nonneg u)
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  calc
    4 * ‖u‖ * ‖1 + x‖ ≤ 5 * ‖u‖ := hnum
    _ ≤ 8 * ‖u‖ := by nlinarith
    _ ≤ 32 * ‖u‖ * ‖D u x‖ ^ 2 := by nlinarith

theorem norm_deriv_Rx_x_le {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    ‖-2 * u ^ 2 * (3 * (1 + x) ^ 2 - u ^ 2) /
        ((1 + x) ^ 2 * (D u x) ^ 2)‖ ≤ 128 * ‖u‖ ^ 2 := by
  have hAlower : (9 : ℝ) / 16 ≤ ‖1 + x‖ ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (one_add_norm_lower hx)
    nlinarith
  have hDsq : (1 : ℝ) / 4 ≤ ‖D u x‖ ^ 2 := by
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (denominator_lower hu hx)
    nlinarith
  have hden : (9 : ℝ) / 64 ≤ ‖1 + x‖ ^ 2 * ‖D u x‖ ^ 2 := by
    have hmul := mul_le_mul hAlower hDsq
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (sq_nonneg ‖1 + x‖)
    nlinarith
  have hdenpos : 0 < ‖1 + x‖ ^ 2 * ‖D u x‖ ^ 2 := by linarith
  have ha2 : ‖1 + x‖ ^ 2 ≤ (25 : ℝ) / 16 := by
    have h := mul_self_le_mul_self (norm_nonneg (1 + x))
      (one_add_norm_upper hx)
    nlinarith
  have hu2upper : ‖u‖ ^ 2 ≤ (1 : ℝ) / 16 := by
    have h := mul_self_le_mul_self (norm_nonneg u) hu
    nlinarith
  have hA : ‖3 * (1 + x) ^ 2 - u ^ 2‖ ≤ 5 := by
    have h := norm_sub_le (3 * (1 + x) ^ 2) (u ^ 2)
    rw [norm_mul, norm_pow, norm_pow] at h
    norm_num at h
    nlinarith
  have hnum : 2 * ‖u‖ ^ 2 * ‖3 * (1 + x) ^ 2 - u ^ 2‖ ≤ 10 * ‖u‖ ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hA (sq_nonneg ‖u‖)
    nlinarith [sq_nonneg ‖u‖]
  simp only [norm_div, norm_mul, norm_pow, norm_neg, Complex.norm_ofNat]
  apply (div_le_iff₀ hdenpos).2
  have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg ‖u‖)
  have hu2nonneg : 0 ≤ ‖u‖ ^ 2 := sq_nonneg ‖u‖
  calc
    2 * ‖u‖ ^ 2 * ‖3 * (1 + x) ^ 2 - u ^ 2‖ ≤ 10 * ‖u‖ ^ 2 := hnum
    _ ≤ 18 * ‖u‖ ^ 2 := by nlinarith
    _ ≤ 128 * ‖u‖ ^ 2 * (‖1 + x‖ ^ 2 * ‖D u x‖ ^ 2) := by
      nlinarith

end
end StructuralNote.FixedSchurRemainderSecond
