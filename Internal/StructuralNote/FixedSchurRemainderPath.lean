import StructuralNote.FixedSchurRemainderSecond
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Actual first and second chain rules for the scalar Schur remainder. -/

namespace StructuralNote.FixedSchurRemainderPath

open Complex
open StructuralNote.FixedSchurRemainderScalar
open StructuralNote.FixedSchurRemainderSecond
open scoped Topology

noncomputable section

def Ruu (u x : ℂ) : ℂ :=
  2 * (1 - 1 / D u x) - 4 * u ^ 2 / (D u x) ^ 2

def Rux (u x : ℂ) : ℂ := 4 * u * (1 + x) / (D u x) ^ 2

def Rxx (u x : ℂ) : ℂ :=
  -2 * u ^ 2 * (3 * (1 + x) ^ 2 - u ^ 2) /
    ((1 + x) ^ 2 * (D u x) ^ 2)

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

private theorem denominator_ne_zero {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) : D u x ≠ 0 := by
  have h := denominator_lower hu hx
  intro hz
  rw [hz, norm_zero] at h
  norm_num at h

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

private theorem argument_re_pos {u x : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    0 < (1 - u ^ 2 / (1 + x) ^ 2).re := by
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
  have hreal := Complex.abs_re_le_norm (-(u ^ 2 / (1 + x) ^ 2))
  have hnegq : ‖-(u ^ 2 / (1 + x) ^ 2)‖ < 1 := by
    simpa only [norm_neg] using hquot
  have hreal' : |(-(u ^ 2 / (1 + x) ^ 2)).re| < 1 := hreal.trans_lt hnegq
  have hneg : -1 < (-(u ^ 2 / (1 + x) ^ 2)).re := (abs_lt.mp hreal').1
  have harg : (1 - u ^ 2 / (1 + x) ^ 2).re =
      1 + (-(u ^ 2 / (1 + x) ^ 2)).re := by
    simp only [sub_re, one_re, neg_re]
    ring
  rw [harg]
  linarith

private theorem hasDerivAt_D_u {u x : ℂ} (_hu : ‖u‖ ≤ 1 / 4)
    (_hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun w : ℂ => D w x) (-2 * u) u := by
  have h := (hasDerivAt_const u ((1 + x) ^ 2)).sub ((hasDerivAt_id u).pow 2)
  have h' : HasDerivAt (fun w : ℂ => D w x)
      (0 - (2 : ℂ) * u ^ (2 - 1) * 1) u :=
    h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => by simp [D]))
  exact h'.congr_deriv (by ring)

private theorem hasDerivAt_D_x {u x : ℂ} (_hu : ‖u‖ ≤ 1 / 4)
    (_hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun y : ℂ => D u y) (2 * (1 + x)) x := by
  have hone : HasDerivAt (fun y : ℂ => 1 + y) 1 x := by
    change HasDerivAt ((fun y : ℂ => 1) + id) 1 x
    simpa only [zero_add] using
      (hasDerivAt_const x (1 : ℂ)).add (hasDerivAt_id x)
  have h := (hone.pow 2).sub (hasDerivAt_const x (u ^ 2))
  have h' : HasDerivAt (fun y : ℂ => D u y)
      (↑2 * (1 + x) ^ (2 - 1) * 1 - 0) x :=
    h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => by simp [D]))
  exact h'.congr_deriv (by ring)

theorem hasDerivAt_R_path {u x : ℝ → ℂ} {du dx : ℂ} {t : ℝ}
    (hu : HasDerivAt u du t) (hx : HasDerivAt x dx t)
    (hU : ‖u t‖ ≤ 1 / 4) (hX : ‖x t‖ ≤ 1 / 4) :
    HasDerivAt (fun s : ℝ => R (u s) (x s))
      (Ru (u t) (x t) * du + Rx (u t) (x t) * dx) t := by
  have hone : HasDerivAt (fun s : ℝ => 1 + x s)  dx t := by
    have h := (hasDerivAt_const t (1 : ℂ)).add hx
    have h' : HasDerivAt (fun s : ℝ => 1 + x s) (0 + dx) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards [] with s
      simp
    exact h'.congr_deriv (by ring)
  have hden : HasDerivAt (fun s : ℝ => (1 + x s) ^ 2)
      (2 * (1 + x t) * dx) t := by
    have h := hone.pow 2
    have h' : HasDerivAt (fun s : ℝ => (1 + x s) ^ 2)
        (2 * (1 + x t) ^ (2 - 1) * dx) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards [] with s
      simp
    exact h'.congr_deriv (by ring)
  have hquot := (hu.pow 2).div hden
    (pow_ne_zero 2 (one_add_ne_zero hX))
  have harg : HasDerivAt
      (fun s : ℝ => 1 - u s ^ 2 / (1 + x s) ^ 2)
      (0 - (↑2 * u t ^ (2 - 1) * du * (1 + x t) ^ 2 -
        (u t) ^ 2 * (2 * (1 + x t) * dx)) /
        ((1 + x t) ^ 2) ^ 2) t := by
    have h := (hasDerivAt_const t (1 : ℂ)).sub hquot
    apply h.congr_of_eventuallyEq
    filter_upwards [] with s
    simp
  have hlog :=
    (Complex.hasDerivAt_log (Or.inl (argument_re_pos hU hX))).hasFDerivAt
      |>.restrictScalars ℝ |>.comp_hasDerivAt t harg
  have hsum := hlog.add (hu.pow 2)
  apply hsum.congr_deriv
  dsimp [R, Ru, Rx, D]
  field_simp [one_add_ne_zero hX, denominator_ne_zero hU hX,
    Complex.slitPlane_ne_zero (argument_mem_slitPlane hU hX)]
  ring

theorem hasDerivAt_Rx_u {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun w : ℂ => Rx w x) (Rux u x) u := by
  have hD := hasDerivAt_D_u hu hx
  have hden := (hasDerivAt_const u (1 + x)).mul hD
  have hnum := (hasDerivAt_const u (2 : ℂ)).mul ((hasDerivAt_id u).pow 2)
  have hq := hnum.div hden
    (mul_ne_zero (one_add_ne_zero hx) (denominator_ne_zero hu hx))
  apply hq.congr_deriv
  dsimp [Rx, Rux, D]
  field_simp [one_add_ne_zero hx, denominator_ne_zero hu hx]
  ring

theorem mixed_partial_agreement {u x : ℂ} (hu : ‖u‖ ≤ 1 / 4)
    (hx : ‖x‖ ≤ 1 / 4) :
    HasDerivAt (fun y : ℂ => Ru u y) (Rux u x) x ∧
      HasDerivAt (fun w : ℂ => Rx w x) (Rux u x) u := by
  exact ⟨by simpa only [Rux] using hasDerivAt_Ru_x hu hx,
    hasDerivAt_Rx_u hu hx⟩

theorem hasDerivAt_Ru_path {u x : ℝ → ℂ} {du dx : ℂ} {t : ℝ}
    (hu : HasDerivAt u du t) (hx : HasDerivAt x dx t)
    (hU : ‖u t‖ ≤ 1 / 4) (hX : ‖x t‖ ≤ 1 / 4) :
    HasDerivAt (fun s : ℝ => Ru (u s) (x s))
      (Ruu (u t) (x t) * du + Rux (u t) (x t) * dx) t := by
  have hone : HasDerivAt (fun s : ℝ => 1 + x s) dx t := by
    have h := (hasDerivAt_const t (1 : ℂ)).add hx
    have h' : HasDerivAt (fun s : ℝ => 1 + x s) (0 + dx) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards [] with s
      simp
    exact h'.congr_deriv (by ring)
  have hD : HasDerivAt (fun s : ℝ => D (u s) (x s))
      (2 * (1 + x t) * dx - 2 * u t * du) t := by
    have h := (hone.pow 2).sub (hu.pow 2)
    have h' : HasDerivAt (fun s : ℝ => D (u s) (x s))
        (2 * (1 + x t) ^ (2 - 1) * dx -
          (2 * u t ^ (2 - 1) * du)) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards [] with s
      simp [D]
    exact h'.congr_deriv (by ring)
  have hinv := (hasDerivAt_const t (1 : ℂ)).div hD
    (denominator_ne_zero hU hX)
  have hone' := (hasDerivAt_const t (1 : ℂ)).sub hinv
  have hleft := (hasDerivAt_const t (2 : ℂ)).mul hu
  have hprod := hleft.mul hone'
  apply (hprod.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => by simp [Ru]))).congr_deriv
  dsimp [Ruu, Rux, Ru, D]
  field_simp [denominator_ne_zero hU hX]
  ring

theorem hasDerivAt_Rx_path {u x : ℝ → ℂ} {du dx : ℂ} {t : ℝ}
    (hu : HasDerivAt u du t) (hx : HasDerivAt x dx t)
    (hU : ‖u t‖ ≤ 1 / 4) (hX : ‖x t‖ ≤ 1 / 4) :
    HasDerivAt (fun s : ℝ => Rx (u s) (x s))
      (Rux (u t) (x t) * du + Rxx (u t) (x t) * dx) t := by
  have hone : HasDerivAt (fun s : ℝ => 1 + x s) dx t := by
    have h := (hasDerivAt_const t (1 : ℂ)).add hx
    have h' : HasDerivAt (fun s : ℝ => 1 + x s) (0 + dx) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards [] with s
      simp
    exact h'.congr_deriv (by ring)
  have hD : HasDerivAt (fun s : ℝ => D (u s) (x s))
      (2 * (1 + x t) * dx - 2 * u t * du) t := by
    have h := (hone.pow 2).sub (hu.pow 2)
    have h' : HasDerivAt (fun s : ℝ => D (u s) (x s))
        (2 * (1 + x t) ^ (2 - 1) * dx -
          (2 * u t ^ (2 - 1) * du)) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards [] with s
      simp [D]
    exact h'.congr_deriv (by ring)
  have hden := hone.mul hD
  have hnum := (hasDerivAt_const t (2 : ℂ)).mul (hu.pow 2)
  have hq := hnum.div hden
    (mul_ne_zero (one_add_ne_zero hX) (denominator_ne_zero hU hX))
  apply (hq.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => by simp [Rx]))).congr_deriv
  dsimp [Rux, Rxx, Rx, D]
  field_simp [one_add_ne_zero hX, denominator_ne_zero hU hX]
  ring

theorem hasDerivAt_R_velocity {u x du dx : ℝ → ℂ}
    {ddu ddx : ℂ} {t : ℝ}
    (hu : HasDerivAt u (du t) t) (hx : HasDerivAt x (dx t) t)
    (hdu : HasDerivAt du ddu t) (hdx : HasDerivAt dx ddx t)
    (hU : ‖u t‖ ≤ 1 / 4) (hX : ‖x t‖ ≤ 1 / 4) :
    HasDerivAt
      (fun s : ℝ => Ru (u s) (x s) * du s + Rx (u s) (x s) * dx s)
      (Ruu (u t) (x t) * (du t) ^ 2 +
        2 * Rux (u t) (x t) * du t * dx t +
        Rxx (u t) (x t) * (dx t) ^ 2 +
        Ru (u t) (x t) * ddu + Rx (u t) (x t) * ddx) t := by
  have hRu := hasDerivAt_Ru_path hu hx hU hX
  have hRx := hasDerivAt_Rx_path hu hx hU hX
  have hsum := (hRu.mul hdu).add (hRx.mul hdx)
  apply (hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun s => by simp))).congr_deriv
  dsimp [Ruu, Rux, Rxx, Ru, Rx]
  ring

theorem norm_R_velocity_deriv_le {u x du dx ddu ddx : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) :
    ‖Ruu u x * du ^ 2 + 2 * Rux u x * du * dx +
        Rxx u x * dx ^ 2 + Ru u x * ddu + Rx u x * ddx‖ ≤
      32 * (‖x‖ + ‖u‖ ^ 2) * ‖du‖ ^ 2 +
        64 * ‖u‖ * ‖du‖ * ‖dx‖ +
        128 * ‖u‖ ^ 2 * ‖dx‖ ^ 2 +
        32 * ‖u‖ * (‖x‖ + ‖u‖ ^ 2) * ‖ddu‖ +
        32 * ‖u‖ ^ 2 * ‖ddx‖ := by
  have hRuu := norm_deriv_Ru_u_le hu hx
  have hRux := norm_deriv_Ru_x_le hu hx
  have hRxx := norm_deriv_Rx_x_le hu hx
  have hRu := norm_deriv_R_u_le hu hx
  have hRx := norm_deriv_R_x_le hu hx
  have h1 : ‖Ruu u x * du ^ 2‖ ≤
      32 * (‖x‖ + ‖u‖ ^ 2) * ‖du‖ ^ 2 := by
    have hh : ‖Ruu u x‖ ≤ 32 * (‖x‖ + ‖u‖ ^ 2) := by
      simpa only [Ruu] using hRuu
    calc
      ‖Ruu u x * du ^ 2‖ = ‖Ruu u x‖ * ‖du‖ ^ 2 := by
        rw [norm_mul, norm_pow]
      _ ≤ 32 * (‖x‖ + ‖u‖ ^ 2) * ‖du‖ ^ 2 := by
        gcongr
  have h2 : ‖2 * Rux u x * du * dx‖ ≤
      64 * ‖u‖ * ‖du‖ * ‖dx‖ := by
    have hh : ‖Rux u x‖ ≤ 32 * ‖u‖ := by
      simpa only [Rux] using hRux
    calc
      ‖2 * Rux u x * du * dx‖ =
          2 * ‖Rux u x‖ * ‖du‖ * ‖dx‖ := by
        rw [norm_mul, norm_mul, norm_mul]
        norm_num
      _ ≤ 2 * (32 * ‖u‖) * ‖du‖ * ‖dx‖ := by
        gcongr
      _ = 64 * ‖u‖ * ‖du‖ * ‖dx‖ := by ring
  have h3 : ‖Rxx u x * dx ^ 2‖ ≤
      128 * ‖u‖ ^ 2 * ‖dx‖ ^ 2 := by
    have hh : ‖Rxx u x‖ ≤ 128 * ‖u‖ ^ 2 := by
      simpa only [Rxx] using hRxx
    calc
      ‖Rxx u x * dx ^ 2‖ = ‖Rxx u x‖ * ‖dx‖ ^ 2 := by
        rw [norm_mul, norm_pow]
      _ ≤ 128 * ‖u‖ ^ 2 * ‖dx‖ ^ 2 := by
        gcongr
  have h4 : ‖Ru u x * ddu‖ ≤
      32 * ‖u‖ * (‖x‖ + ‖u‖ ^ 2) * ‖ddu‖ := by
    have hh : ‖Ru u x‖ ≤ 32 * ‖u‖ * (‖x‖ + ‖u‖ ^ 2) := by
      simpa only [Ru] using hRu
    calc
      ‖Ru u x * ddu‖ = ‖Ru u x‖ * ‖ddu‖ := norm_mul _ _
      _ ≤ 32 * ‖u‖ * (‖x‖ + ‖u‖ ^ 2) * ‖ddu‖ := by
        gcongr
  have h5 : ‖Rx u x * ddx‖ ≤ 32 * ‖u‖ ^ 2 * ‖ddx‖ := by
    have hh : ‖Rx u x‖ ≤ 32 * ‖u‖ ^ 2 := by
      simpa only [Rx] using hRx
    calc
      ‖Rx u x * ddx‖ = ‖Rx u x‖ * ‖ddx‖ := norm_mul _ _
      _ ≤ 32 * ‖u‖ ^ 2 * ‖ddx‖ := by
        gcongr
  have ht :
      ‖Ruu u x * du ^ 2 + 2 * Rux u x * du * dx +
          Rxx u x * dx ^ 2 + Ru u x * ddu + Rx u x * ddx‖ ≤
        ‖Ruu u x * du ^ 2‖ + ‖2 * Rux u x * du * dx‖ +
          ‖Rxx u x * dx ^ 2‖ + ‖Ru u x * ddu‖ + ‖Rx u x * ddx‖ := by
    have he := norm_add_le
      (Ruu u x * du ^ 2 + 2 * Rux u x * du * dx +
        Rxx u x * dx ^ 2 + Ru u x * ddu) (Rx u x * ddx)
    have hd := norm_add_le
      (Ruu u x * du ^ 2 + 2 * Rux u x * du * dx + Rxx u x * dx ^ 2)
      (Ru u x * ddu)
    have hc := norm_add_le
      (Ruu u x * du ^ 2 + 2 * Rux u x * du * dx) (Rxx u x * dx ^ 2)
    have hb := norm_add_le (Ruu u x * du ^ 2) (2 * Rux u x * du * dx)
    nlinarith only [he, hd, hc, hb]
  nlinarith only [ht, h1, h2, h3, h4, h5]

end
end StructuralNote.FixedSchurRemainderPath
