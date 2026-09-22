import StructuralNote.FixedSchurRemainderScalar
import Mathlib.Analysis.Calculus.MeanValue

/-! Finite-difference estimates for the scalar Schur remainder. -/

namespace StructuralNote.FixedSchurRemainderDifference

open StructuralNote.FixedSchurRemainderScalar
open scoped Topology

noncomputable section

private theorem affine_u_norm_le {u v : ℂ} {U : ℝ} {t : ℝ}
    (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) (_hU : 0 ≤ U)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖v + t • (u - v)‖ ≤ U := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h₁ : 0 ≤ 1 - t := by linarith
  have h₂ := mul_le_mul_of_nonneg_left hv h₁
  have h₃ := mul_le_mul_of_nonneg_left hu ht0
  calc
    ‖v + t • (u - v)‖ = ‖(1 - t) • v + t • u‖ := by
      congr 1
      module
    _ ≤ ‖(1 - t) • v‖ + ‖t • u‖ := norm_add_le _ _
    _ = |1 - t| * ‖v‖ + |t| * ‖u‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ = (1 - t) * ‖v‖ + t * ‖u‖ := by
      rw [abs_of_nonneg h₁, abs_of_nonneg ht0]
    _ ≤ U := by
      nlinarith

theorem norm_R_sub_R_u_le {u v x : ℂ} {U X : ℝ}
    (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) (hU : 0 ≤ U) (hUquarter : U ≤ 1 / 4)
    (hx : ‖x‖ ≤ X) (hX : 0 ≤ X) (hXquarter : X ≤ 1 / 4) :
    ‖R u x - R v x‖ ≤ 32 * U * (X + U ^ 2) * ‖u - v‖ := by
  let f : ℝ → ℂ := fun t => R (v + t • (u - v)) x
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt f
        ((2 * (v + t • (u - v)) *
          (1 - 1 / D (v + t • (u - v)) x)) * (u - v)) t := by
    have hp : HasDerivAt (fun s : ℝ => v + s • (u - v)) (u - v) t := by
      simpa [add_comm] using
        ((hasDerivAt_id t).smul_const (u - v)).const_add v
    have hpnorm := affine_u_norm_le hu hv hU ht
    have hq := hasDerivAt_R_u (u := v + t • (u - v)) (x := x)
      (hpnorm.trans hUquarter) (hx.trans hXquarter)
    have hc := (hq.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hp
    simpa [f, Function.comp_def, mul_comm] using hc
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖(2 * (v + t • (u - v)) *
          (1 - 1 / D (v + t • (u - v)) x)) * (u - v)‖ ≤
        32 * U * (X + U ^ 2) * ‖u - v‖ := by
    have hp := affine_u_norm_le hu hv hU ht
    have hq := norm_deriv_R_u_le (u := v + t • (u - v)) (x := x)
      (hp.trans hUquarter) (hx.trans hXquarter)
    rw [norm_mul]
    calc
      ‖2 * (v + t • (u - v)) *
            (1 - 1 / D (v + t • (u - v)) x)‖ * ‖u - v‖ ≤
          (32 * U * (‖x‖ + U ^ 2)) * ‖u - v‖ := by
        gcongr
        exact hq.trans (by gcongr)
      _ ≤ 32 * U * (X + U ^ 2) * ‖u - v‖ := by
        gcongr
  have hC : 0 ≤ 32 * U * (X + U ^ 2) * ‖u - v‖ := by
    positivity
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
    (C := 32 * U * (X + U ^ 2) * ‖u - v‖)
    (fun t ht => hbound t ⟨ht.1, ht.2.le⟩)
  have heq : f 1 - f 0 = R u x - R v x := by
    simp [f]
  rw [← heq]
  exact hm

theorem norm_R_sub_R_x_le {u x y : ℂ}
    (hu : ‖u‖ ≤ 1 / 4) (hx : ‖x‖ ≤ 1 / 4) (hy : ‖y‖ ≤ 1 / 4) :
    ‖R u x - R u y‖ ≤ 32 * ‖u‖ ^ 2 * ‖x - y‖ := by
  let f : ℝ → ℂ := fun t => R u (y + t • (x - y))
  have hderiv (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt f
        ((2 * u ^ 2 / ((1 + (y + t • (x - y))) *
          D u (y + t • (x - y)))) * (x - y)) t := by
    have hp : HasDerivAt (fun s : ℝ => y + s • (x - y)) (x - y) t := by
      simpa [add_comm] using
        ((hasDerivAt_id t).smul_const (x - y)).const_add y
    have hpnorm := affine_u_norm_le hx hy (by norm_num : (0 : ℝ) ≤ 1 / 4) ht
    have hq := hasDerivAt_R_x (u := u) (x := y + t • (x - y)) hu
      hpnorm
    have hc := (hq.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hp
    simpa [f, Function.comp_def, mul_comm] using hc
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖(2 * u ^ 2 / ((1 + (y + t • (x - y))) *
          D u (y + t • (x - y)))) * (x - y)‖ ≤
        32 * ‖u‖ ^ 2 * ‖x - y‖ := by
    have hpnorm := affine_u_norm_le hx hy (by norm_num : (0 : ℝ) ≤ 1 / 4) ht
    have hq := norm_deriv_R_x_le (u := u) (x := y + t • (x - y)) hu hpnorm
    rw [norm_mul]
    gcongr
  have hm := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hderiv t ht).hasDerivWithinAt)
    (C := 32 * ‖u‖ ^ 2 * ‖x - y‖)
    (fun t ht => hbound t ⟨ht.1, ht.2.le⟩)
  have heq : f 1 - f 0 = R u x - R u y := by
    simp [f]
  rw [← heq]
  exact hm

theorem norm_R_sub_R_sub_le {u v x y : ℂ} {U X : ℝ}
    (hu : ‖u‖ ≤ U) (hv : ‖v‖ ≤ U) (hU : 0 ≤ U) (hUquarter : U ≤ 1 / 4)
    (hx : ‖x‖ ≤ X) (hy : ‖y‖ ≤ X) (hX : 0 ≤ X) (hXquarter : X ≤ 1 / 4) :
    ‖R u x - R v y‖ ≤
      32 * U * (X + U ^ 2) * ‖u - v‖ + 32 * U ^ 2 * ‖x - y‖ := by
  have huquarter : ‖u‖ ≤ 1 / 4 := hu.trans hUquarter
  have hvquarter : ‖v‖ ≤ 1 / 4 := hv.trans hUquarter
  have hxquarter : ‖x‖ ≤ 1 / 4 := hx.trans hXquarter
  have hyquarter : ‖y‖ ≤ 1 / 4 := hy.trans hXquarter
  have hu_part := norm_R_sub_R_u_le hu hv hU hUquarter hx hX hXquarter
  have hv_part := norm_R_sub_R_x_le hvquarter hxquarter hyquarter
  calc
    ‖R u x - R v y‖ ≤ ‖R u x - R v x‖ + ‖R v x - R v y‖ := by
      rw [show R u x - R v y = (R u x - R v x) + (R v x - R v y) by ring]
      exact norm_add_le _ _
    _ ≤ 32 * U * (X + U ^ 2) * ‖u - v‖ +
          32 * ‖v‖ ^ 2 * ‖x - y‖ := by
      gcongr
    _ ≤ 32 * U * (X + U ^ 2) * ‖u - v‖ +
          32 * U ^ 2 * ‖x - y‖ := by
      gcongr

end
end StructuralNote.FixedSchurRemainderDifference
